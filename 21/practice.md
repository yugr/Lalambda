# Motivation

All applications are special but each calls `malloc`,
one way or another.

`Malloc` may sometimes fail, i.e. return `NULL`,
and a well-written app should detect such cases and
terminate graciously.

Not doing will result in a SEGV signal being sent
which will most likely cause a coredump,
and often result in leaked system resources,
hanged database transactions and other BAD THINGS.

The issue is greatly alleviated with memory overcommit
(apps may allocate more virtual memory than there's
DRAM+swap available) but it's often not available
(e.g. not available on all OSes or disabled due
to reliability issues) so in any case verifying
`malloc` is a good practice.

In this workshop we'll make a simple checker
which will detect this behavior at large scale and
use it to find issues in popular OSS packages.

# Initial app

So let's start with the simplest possible implementation
in branch `workshop/1` of [failing-malloc repo](https://github.com/yugr/failing-malloc)
  * intercept `malloc` via `LD_PRELOAD`
  * on first call collect various data
  * and return `NULL`

Few points of interest:
  * we protect against programs who run in parallel -
    only one thread will return `NULL`
  * we are not using printf (`PRINTF_NO_ALLOC`)
    because it may itself call malloc
    and we'll get into an endless loop
  * we take some effort to report full command line -
    this will help us later
  * to simplify code we are using buffers of fixed size -
    they are always enough in practice but we are still
    careful
  * we are not using simpler mechanisms to call libc's malloc
    ([malloc hooks](https://www.gnu.org/software/libc/manual/html_node/Hooks-for-Malloc.html)
    or `__libc_malloc`) for illustrative purposes

We can now run this test on a simple reprocases in example.c:
```
failingmalloc: intercepting malloc in '/home/yugr/src/failing-malloc/bin/example-safe 123 456'
failingmalloc: returning NULL from malloc in '/home/yugr/src/failing-malloc/bin/example-safe 123 456'
Safe test terminated normally
failingmalloc: intercepting malloc in '/home/yugr/src/failing-malloc/bin/example-unsafe 1 2 3'
failingmalloc: returning NULL from malloc in '/home/yugr/src/failing-malloc/bin/example-unsafe 1 2 3'
Segmentation fault (core dumped)
Unsafe test failed with 139
```

We can see that safe test terminates normally
and unsafe one (that does not check `malloc` result) crashes.

We can now try running our checker on real-world programs:
```
$ LD_PRELOAD=$HOME/src/failing-malloc/bin/libfailingmalloc.so ls
failingmalloc: intercepting malloc in '/usr/bin/ls --color=auto'
failingmalloc: returning NULL from malloc in '/usr/bin/ls --color=auto'
ls: memory exhausted
$ LD_PRELOAD=$HOME/src/failing-malloc/bin/libfailingmalloc.so whoami
failingmalloc: intercepting malloc in '/usr/bin/whoami'
failingmalloc: returning NULL from malloc in '/usr/bin/whoami'
whoami: cannot find name for user ID 1000
```

Ok, looks like at least coreutils are not failing.

But let's try something more complicated:
```
$ LD_PRELOAD=$HOME/src/failing-malloc/bin/libfailingmalloc.so perl -e 'print;'
failingmalloc: intercepting malloc in '/usr/bin/perl -e print;'
failingmalloc: returning NULL from malloc in '/usr/bin/perl -e print;'
Segmentation fault (core dumped)
```

# Delayed fails

Our checker returns `NULL` on first `malloc` call
so it can only identify the failure at first `malloc` call.
Let's add a knob to insert `NULL` at arbitrary place.

Usually the easiest way to control instrumenting
checkers is through a environment variables
(that's e.g. how sanitizers work).

That's what we do in branch `workshop/2`. Here we add
a `FAILING_MALLOC_FAIL_AFTER` option to control
when exactly to return NULL.

Let's verify that it works:
```
$ FAILING_MALLOC_START_AFTER=999 LD_PRELOAD=$HOME/src/failing-malloc/bin/libfailingmalloc.so whoami
failingmalloc: intercepting malloc in '/usr/bin/whoami'
yugr
```

Great! Now we can run any app with many random values
of `FAILING_MALLOC_START_AFTER` to see if it fails somewhere:
```
$ while true; do
  export FAILING_MALLOC_FAIL_AFTER=$((`od -vAn -N1 -tu1 < /dev/urandom` >> 5))
  LD_PRELOAD=$HOME/src/failing-malloc/bin/libfailingmalloc.so whoami
  sleep 0.5
done
failingmalloc: intercepting malloc in '/usr/bin/whoami' (fail after 6 allocs)
yugr
failingmalloc: intercepting malloc in '/usr/bin/whoami' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/usr/bin/whoami'
whoami: cannot find name for user ID 1000
failingmalloc: intercepting malloc in '/usr/bin/whoami' (fail after 6 allocs)
yugr
failingmalloc: intercepting malloc in '/usr/bin/whoami' (fail after 3 allocs)
yugr
failingmalloc: intercepting malloc in '/usr/bin/whoami' (fail after 2 allocs)
yugr
failingmalloc: intercepting malloc in '/usr/bin/whoami' (fail after 1 allocs)
yugr
...
```

# Analyze bug in real package

Let's try on something less trivial:
```
$ LD_PRELOAD=$HOME/src/failing-malloc/bin/libfailingmalloc.so getfacl /bin/ls
failingmalloc: intercepting malloc in '/usr/bin/getfacl /bin/ls' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/usr/bin/getfacl /bin/ls'
Segmentation fault (core dumped)
```
To understand what's going on we can run `gdb`:
```
$ gdb -ex "set environment LD_PRELOAD=$HOME/src/failing-malloc/bin/libfailingmalloc.so" -ex r --args /bin/getfacl /bin/ls
...
Starting program: /usr/bin/getfacl /bin/ls
failingmalloc: intercepting malloc in '/usr/bin/bash -c exec /usr/bin/getfacl /bin/ls' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/usr/bin/bash -c exec /usr/bin/getfacl /bin/ls'
bash: xmalloc: cannot allocate 10 bytes
During startup program exited with code 2.
```

Hm, what's going on here? By default `gdb` runs apps through `bash`.
Bash was run under `LD_PRELOAD` and terminated because `malloc` returned `NULL`!

Luckily in new gdbs we can disable this behavior with `startup-with-shell` option:
```
$ gdb -ex 'set startup-with-shell off' -ex "set environment LD_PRELOAD=$HOME/src/failing-malloc/bin/libfailingmalloc.so" -ex r --args /bin/getfacl /bin/ls
...
Starting program: /usr/bin/getfacl /bin/ls
failingmalloc: intercepting malloc in '/usr/bin/getfacl /bin/ls' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/usr/bin/getfacl /bin/ls'

Program received signal SIGSEGV, Segmentation fault.
0x00007ffff7fa6bb8 in ?? () from /lib/x86_64-linux-gnu/libacl.so.1
(gdb) bt
#0  0x00007ffff7fa6bb8 in ?? () from /lib/x86_64-linux-gnu/libacl.so.1
#1  0x00007ffff7fa8408 in acl_from_mode () from /lib/x86_64-linux-gnu/libacl.so.1
#2  0x00007ffff7fa78fd in acl_get_file () from /lib/x86_64-linux-gnu/libacl.so.1
#3  0x00005555555579a3 in ?? ()
#4  0x0000555555558262 in ?? ()
#5  0x0000555555558831 in ?? ()
#6  0x00005555555569eb in ?? ()
#7  0x00007ffff7dd90b3 in __libc_start_main (main=0x555555556680, argc=2, argv=0x7fffffffdd88, init=<optimized out>, fini=<optimized out>, rtld_fini=<optimized out>, stack_end=0x7fffffffdd78) at ../csu/libc-start.c:308
#8  0x0000555555556b0e in ?? ()
```

Hm, not very helpful... But let's install debug symbols and see if it helps.
```
$ dpkg -S /bin/getfacl
acl: /bin/getfacl
$ dpkg -S libacl.so.1
libacl1:amd64: /usr/lib/x86_64-linux-gnu/libacl.so.1
libacl1:amd64: /usr/lib/x86_64-linux-gnu/libacl.so.1.1.2253
$ sudo apt-get install acl-dbgsym libacl1-dbgsym
```

If dbgsym packages are not found you need to add more repos to your `sources.list`:
```
$ sudo apt-key adv --keyserver keyserver.ubuntu.com --recv-keys 428D7C01 C8CAB6595FDFF622
$ printf "deb http://ddebs.ubuntu.com %s main restricted universe multiverse\n" $(lsb_release -cs){,-updates,-security,-proposed} |  sudo tee -a /etc/apt/sources.list.d/ddebs.list
```

Now rerun gdb and enjoy a nicely formatted backtrace:
```
$ gdb ...
...
(gdb) bt
#0  0x00007ffff7fa6bb8 in __acl_free_acl_obj (acl_obj_p=0x0) at libacl/acl_free.c:30
#1  0x00007ffff7fa8408 in acl_from_mode (mode=33261) at libacl/acl_from_mode.c:70
#2  0x00007ffff7fa78fd in acl_get_file (path_p=<optimized out>, type=32768) at libacl/acl_get_file.c:84
#3  0x00005555555579a3 in do_print (walk_flags=272, unused=0x0, st=0x7fffffffcbb0, path_p=0x7fffffffcca0 "/bin/ls") at tools/getfacl.c:471
#4  do_print (path_p=path_p@entry=0x7fffffffcca0 "/bin/ls", st=st@entry=0x7fffffffcbb0, walk_flags=walk_flags@entry=272, unused=unused@entry=0x0) at tools/getfacl.c:448
#5  0x0000555555558262 in walk_tree_rec (path=0x7fffffffcca0 "/bin/ls", walk_flags=walk_flags@entry=16, func=func@entry=0x555555557790 <do_print>, arg=arg@entry=0x0, depth=depth@entry=0) at libmisc/walk_tree.c:98
#6  0x0000555555558831 in walk_tree (path=0x7fffffffe189 "/bin/ls", walk_flags=16, num=<optimized out>, func=0x555555557790 <do_print>, arg=0x0) at libmisc/walk_tree.c:231
#7  0x00005555555569eb in main (argc=2, argv=0x7fffffffddf8) at tools/getfacl.c:744
```

dbgsyms do not contain the source code so we need to download it manually:
```
$ apt-get source acl
$ cd acl-2.2.53
$ vim libacl/acl_free.c +30
```

Now we can instruct gdb where to find sources via
```
(gdb) directory acl-2.2.53
(gdb) l
25	
26	void
27	__acl_free_acl_obj(acl_obj *acl_obj_p)
28	{
29		acl_entry_obj *entry_obj_p;
30		while (acl_obj_p->anext != (acl_entry_obj *)acl_obj_p) {
31			entry_obj_p = acl_obj_p->anext;
32			acl_obj_p->anext = acl_obj_p->anext->enext;
33			free_obj_p(entry_obj_p);
34		}
(gdb) p acl_obj_p
$1 = (acl_obj *) 0x0
```

Looks like we are accessing a `NULL` object in `acl_obj_p`!

```
(gdb) fr 1
#1  0x00007ffff7fa8408 in acl_from_mode (mode=33261) at libacl/acl_from_mode.c:70
70		__acl_free_acl_obj(acl_obj_p);
(gdb) l
65		entry_obj_p->eid.qid = ACL_UNDEFINED_ID;
66		entry_obj_p->eperm.sperm = mode & S_IRWXO;
67		return int2ext(acl_obj_p);
68	
69	fail:
70		__acl_free_acl_obj(acl_obj_p);
71		return NULL;
72	}
```

So looks like acl correctly detected `NULL` returned by `malloc`
prior to `__acl_free_acl_obj` call but
failed to properly release the resources.

At this point we can quickly cook a patch and file a bug
in acl's bugtracker.

# Testing at larger scale

Now, of course manually applying checkers to various programs is a tiresome and boring task.
So what can we do to make it interesting?

Few simple ideas:
  * apply your checker to each app on Linux:
    * run without arguments and stdin redirected from /dev/null (do this only in containers to avoid damaging your system!)
    * run with `--help` or `-h`
  * (for LD_PRELOAD-based checkers, not for the faint hearted!) boot complete Linux system with your checker preloaded
  * run some large system benchmark under your checker (e.g. Phoronix testsuite)

Unfortunately this is all very shallow and won't result too much loot^W bugs found.

A more promising solution is reusing builtin testsuites
which are available for many open-source packages.
For example let's try to detect a bug in libacl's unittests:
```
$ cd acl-2.2.53
$ find | xargs touch -m -r /bin/ls  # Fix clock skew
$ ./configure
$ make
$ LD_PRELOAD=$HOME/src/failing-malloc/bin/libfailingmalloc.so make check
...
# TOTAL: 15
# PASS:  9
# SKIP:  4
# XFAIL: 2
# FAIL:  0
# XPASS: 0
# ERROR: 0
```

Weird, all tests passed. What's going on?
The clever testwrapper overrides our `LD_PRELOAD`:
```
yugr@yugr-VirtualBox:~/src/1/acl-2.2.53$ gr LD_PRELOAD
test/runwrapper:	export LD_PRELOAD="$PWD/.libs/libtestlookup.so"
```

Let's fix it for now
```
$ sed -r -e 's/^if /if false \&\& /' test/runwrapper
```
(btw this illustrates the idea why `LD_PRELOAD` is unreliable
and we should use `/etc/ld.so.preload` instead).

Now we run into another issue:
```
yugr@yugr-VirtualBox:~/src/1/acl-2.2.53$ LD_PRELOAD=$HOME/src/failing-malloc/bin/libfailingmalloc.so make check
failingmalloc: intercepting malloc in '/usr/bin/make check' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/usr/bin/make check'
Segmentation fault (core dumped)
```
Ouch, our checker has tried inserting errors into make process and successfully failed it!
On a positive side this means that make also has bugs that we can fix but
currently we just want to ignore them and proceed with libacl testing.

Let's update our checker once again, this time teaching it to not instrument system programs
and libraries. This is done in branch `workshop/3`.

Now finally results are expected:
```
# TOTAL: 15
# PASS:  0
# SKIP:  4
# XFAIL: 2
# FAIL:  9
# XPASS: 0
# ERROR: 0
```
and closer inspection of logfile shows that fails are indeed due to the segfault we found above:
```
yugr@yugr-VirtualBox:~/src/1/acl-2.2.53$ grep -a failingmalloc test-suite.log | head
failingmalloc: intercepting malloc in '/home/yugr/src/1/acl-2.2.53/.libs/setfacl -m u:bin:rw f' != ~
failingmalloc: returning NULL from malloc in '/home/yugr/src/1/acl-2.2.53/.libs/setfacl -m u:bin:rw f' != ~
failingmalloc: intercepting malloc in '/home/yugr/src/1/acl-2.2.53/.libs/setfacl -R -m u:bin:rwx h' != ~
failingmalloc: returning NULL from malloc in '/home/yugr/src/1/acl-2.2.53/.libs/setfacl -R -m u:bin:rwx h' != ~
failingmalloc: intercepting malloc in '/home/yugr/src/1/acl-2.2.53/.libs/getfacl --omit-header h/x' != user::rw-
failingmalloc: returning NULL from malloc in '/home/yugr/src/1/acl-2.2.53/.libs/getfacl --omit-header h/x' != user:bin:rwx
failingmalloc: segmentation fault in '/home/yugr/src/1/acl-2.2.53/.libs/getfacl --omit-header h/x' != group::r--
failingmalloc: intercepting malloc in '/home/yugr/src/1/acl-2.2.53/.libs/getfacl --omit-header i/x' != user::rw-
failingmalloc: returning NULL from malloc in '/home/yugr/src/1/acl-2.2.53/.libs/getfacl --omit-header i/x' != user:bin:rwx
failingmalloc: segmentation fault in '/home/yugr/src/1/acl-2.2.53/.libs/getfacl --omit-header i/x' != group::r--
...
```

# debian_pkg_test: unittesting at scale

The easiest way to automate running of unit tests for many open-source projects
is to abuse^W reuse a build system of some distro.

I selected Debian as it has the most packages and has convenient automation tools (pbuilder/cowbuilder).
The main problem is that Debian build system is aimed at _building_ packages, not _testing_ them
so it does not have builtin support for running unit tests :(
But with some effort we can add some clever hooks into their build system and run tests outselves.
I've done this in debian_pkg_test project. We'll now use it to automate out checker.

Firstly we need to make a small adaptation failing-malloc to massive batch runs,
namely teach it to autodetect crashes and register them in dedicated place.
This is done in branch `workshop/4` by adding support for `FAILING_MALLOC_LOGFILE`
environment variable and installing signal handler prior to retuning bad value
from `malloc`.

To set up debian_pkg_test we follow instructions
in [debian_pkg_test/README.md](https://github.com/yugr/debian_pkg_test#setting-up)
and use pre-cooked integration from
[examples/failingmalloc](https://github.com/yugr/debian_pkg_test/examples/failing-malloc).
```
$ ./test_pkgs acl
...
============================================================================
Testsuite summary for acl 2.2.53
============================================================================
# TOTAL: 15
# PASS:  0
# SKIP:  0
# XFAIL: 2
# FAIL:  13
# XPASS: 0
# ERROR: 0
============================================================================
See ./test-suite.log
Please report to acl-devel@nongnu.org
...
```

TODO: fix hang in autopkgtest's `example` test.

Debian_pkg_test stored all the necessary info:
failing-malloc reports, syslog and build log
to `test_pkgs.1/acl` folder. We can make sure
that expected bugs have been found:
```
$ cat test_pkgs.8/acl/output/failingmalloc.log
failingmalloc: intercepting malloc in '/build/acl-2.2.53/.libs/setfacl -m u:bin:rw f'
failingmalloc: intercepting malloc in '/build/acl-2.2.53/.libs/setfacl -m u:bin:rw f' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/build/acl-2.2.53/.libs/setfacl -m u:bin:rw f'
failingmalloc: intercepting malloc in '/build/acl-2.2.53/.libs/setfacl -R -m u:bin:rwx h'
failingmalloc: intercepting malloc in '/build/acl-2.2.53/.libs/setfacl -R -m u:bin:rwx h' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/build/acl-2.2.53/.libs/setfacl -R -m u:bin:rwx h'
failingmalloc: intercepting malloc in '/build/acl-2.2.53/.libs/getfacl --omit-header h/x'
failingmalloc: intercepting malloc in '/build/acl-2.2.53/.libs/getfacl --omit-header h/x' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/build/acl-2.2.53/.libs/getfacl --omit-header h/x'
failingmalloc: segmentation fault in '/build/acl-2.2.53/.libs/getfacl --omit-header h/x'
...
```

# Further work

At this point the checker is more or less ready
and we can unleash it's power to the world
and start filing bugreports and PRs.

At this point you can pursue several directions.

Firstly you can try applying the checker to other packages!
After quick skimming from packages in
[Debian package rating](https://popcon.debian.org/by_vote)
I saw segfaults in
  * libfastjson
  * pixman
  * p11-kit
  * pcre2/pcre3
  * dpkg
  * expat
  * openssl
  * acl
  * ligogg
  * apt
  * gpg

If that sounds too boring, try improving the existing checker:
  * intercept other alloc functions like `realloc` or `aligned_alloc`
    (would also be nice to figure out why `calloc` interception does not work!)
  * add support for control via single env variable `FAILING_MALLOC_OPTIONS`
    (verbosity, logfile, file pattern to enable/disable fails, etc.)
  * make library scan more efficient (used interval tree instead of linear search)
  * print caller's address, DSO and program location (e.g. via `addr2line(1)`)
    and use it for automatic bug deduplication
  * randomize number of skipped mallocs before first return 0
  * automatically fork tested app multiple times with different skip factors
    (fuzzing)
  * make code thread-safe

Finally if the whole runtime checking idea inspires you,
try writing other simple checkers e.g.
  * find intersecting ranges in `memcpy` or `strcpy`
  * `memcpy`/`memcmp`/`malloc`/`calloc` of 0 bytes
or come up with your own idea and try it out on Debian!

# (Backup)

A reprocase from gpg.

```
$ gdb -ex 'set startup-with-shell off' -ex "set environment LD_PRELOAD=$HOME/src/debian_pkg_test/pbuilder-shared/failing-malloc/bin/libfailingmalloc.so" -ex r --args /usr/bin/gpg
...
failingmalloc: intercepting malloc in '/usr/bin/gpg' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/usr/bin/gpg'

Fatal error: No such file or directory

Program received signal SIGABRT, Aborted.
__GI_raise (sig=sig@entry=6) at ../sysdeps/unix/sysv/linux/raise.c:50
50	../sysdeps/unix/sysv/linux/raise.c: No such file or directory.
(gdb) bt
#0  __GI_raise (sig=sig@entry=6) at ../sysdeps/unix/sysv/linux/raise.c:50
#1  0x00007ffff7ae2859 in __GI_abort () at abort.c:79
#2  0x00007ffff7d47826 in ?? () from /lib/x86_64-linux-gnu/libgcrypt.so.20
#3  0x00007ffff7d4a169 in ?? () from /lib/x86_64-linux-gnu/libgcrypt.so.20
#4  0x00007ffff7e0eae7 in ?? () from /lib/x86_64-linux-gnu/libgcrypt.so.20
#5  0x00007ffff7e0eb6b in ?? () from /lib/x86_64-linux-gnu/libgcrypt.so.20
#6  0x00007ffff7d48a1a in ?? () from /lib/x86_64-linux-gnu/libgcrypt.so.20
#7  0x00007ffff7d48c55 in ?? () from /lib/x86_64-linux-gnu/libgcrypt.so.20
#8  0x000055555560227b in ?? ()
#9  0x0000555555564ecf in ?? ()
#10 0x00007ffff7ae40b3 in __libc_start_main (main=0x555555564e00, argc=1, argv=0x7fffffffdd98, init=<optimized out>, fini=<optimized out>, rtld_fini=<optimized out>, stack_end=0x7fffffffdd88) at ../csu/libc-start.c:308
#11 0x000055555556c05e in ?? ()
```
