# Motivation

All applications are special but each calls `malloc`,
one way or another.

`Malloc` may sometimes fail, i.e. return `NULL`,
and a well-written app should detect such cases and
terminate graciously.

Not doing so will result in a SEGV signal being sent
which will most likely cause a coredump,
and often result in leaked system resources,
hanged database transactions and other BAD THINGS.

The issue is greatly alleviated by
[memory overcommit](https://en.wikipedia.org/wiki/Memory_overcommitment)
(apps may allocate more virtual memory than there's
DRAM+swap available) but it's often not available
(e.g. not available on all OSes or disabled due
to reliability issues) so in any case verifying
`malloc` is a good practice.

In this workshop we'll make a simple checker
which will be capable of detecting problematic programs at
large scale. We'll then use it to find issues in popular OSS packages.

# Prerequisites

We'll be using Docker for our experiments.
To install Docker on Ubuntu please follow the guide
at https://docs.docker.com/engine/install/ubuntu/

To avoid the need to run Docker commands with `sudo`, run
```
$ sudo usermod -aG docker $USER
$ newgrp docker
```

Then go to the `docker` subdirectory and run
```
$ sudo docker build -t yugr/failing-malloc .
```

Finally create a local workspace on you host system
and start docker
```
$ mkdir $HOME/work
$ sudo docker run -it --privileged -v $HOME/work:/work yugr/failing-malloc
```
(`privileged` is needed due to mounts which will be needed by pbuilder).

# Initial app

So let's start with the simplest possible implementation
of our checker. For that we'll clone the repo from Github
and use initial implementation from
[workshop/1](https://github.com/yugr/failing-malloc/commits/workshop/1) branch:
```
# cd /work
# git clone -b workshop/1 https://github.com/yugr/failing-malloc
```
This implementation simply
  * intercepts `malloc` via `LD_PRELOAD`
  * on first call collects various data
  * and then blatantly returns `NULL` to the caller

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

We can build checker and run it on a simple unittest in example.c:
```
# make -C failing-malloc
# make -C failing-malloc check
failingmalloc: intercepting malloc in '/home/yugr/src/failing-malloc/bin/example-safe 123 456'
failingmalloc: returning NULL from malloc in '/home/yugr/src/failing-malloc/bin/example-safe 123 456'
Safe test terminated normally
failingmalloc: intercepting malloc in '/home/yugr/src/failing-malloc/bin/example-unsafe 1 2 3'
failingmalloc: returning NULL from malloc in '/home/yugr/src/failing-malloc/bin/example-unsafe 1 2 3'
Segmentation fault (core dumped)
Unsafe test failed with 139
```
We can see that safe test terminates normally
and the unsafe one (that does not check `malloc` result) crashes.

We can now try running our checker on real-world programs:
```
# export LD_LIBRARY_PATH=/work/failing-malloc/bin${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
# LD_PRELOAD=libfailingmalloc.so ls
failingmalloc: intercepting malloc in '/usr/bin/ls --color=auto'
failingmalloc: returning NULL from malloc in '/usr/bin/ls --color=auto'
ls: memory exhausted
# LD_PRELOAD=libfailingmalloc.so whoami
failingmalloc: intercepting malloc in '/usr/bin/whoami'
failingmalloc: returning NULL from malloc in '/usr/bin/whoami'
whoami: cannot find name for user ID 1000
```

Ok, looks like at least coreutils handle memory exhaustion correctly
(which is not surprising as they have been a standard verification
target in past 30+ years).

But more complicated apps do fail:
```
# LD_PRELOAD=libfailingmalloc.so dpkg
failingmalloc: intercepting malloc in '/usr/bin/dpkg'
failingmalloc: returning NULL from malloc in '/usr/bin/dpkg'
Segmentation fault (core dumped)
```

# Delayed fails

Our checker returns `NULL` on first `malloc` call
so it can only identify issues with the first allocation.
Let's add a knob to insert `NULL` at arbitrary place.

Usually the easiest way to control instrumenting
checkers is through a environment variables
(that's e.g. how sanitizers work).

That's what we do in branch [workshop/2](https://github.com/yugr/failing-malloc/compare/workshop/1...workshop/2).
Here we add a `FAILING_MALLOC_FAIL_AFTER` option to control
when exactly to return NULL.

Let's verify that it works:
```
# git -C /work/failing-malloc checkout workshop/2
# make -C /work/failing-malloc
# FAILING_MALLOC_FAIL_AFTER=999 LD_PRELOAD=libfailingmalloc.so whoami
failingmalloc: intercepting malloc in '/usr/bin/whoami'
root
```

Great! Now we can run any app with many random values
of `FAILING_MALLOC_FAIL_AFTER` to see if it fails somewhere:
```
# while true; do
  FAILING_MALLOC_FAIL_AFTER=$((`od -vAn -N1 -tu1 < /dev/urandom` >> 1)) LD_PRELOAD=libfailingmalloc.so whoami
  sleep 0.5
done
failingmalloc: intercepting malloc in '/usr/bin/whoami' (fail after 120 allocs)
root
failingmalloc: intercepting malloc in '/usr/bin/whoami' (fail after 65 allocs)
root
failingmalloc: intercepting malloc in '/usr/bin/whoami' (fail after 104 allocs)
root
failingmalloc: intercepting malloc in '/usr/bin/whoami' (fail after 36 allocs)
failingmalloc: returning NULL from malloc in '/usr/bin/whoami'
whoami: cannot find name for user ID 0
```

# Analyze bug in real package

Let's try on something less trivial:
```
# apt-get install acl
# LD_PRELOAD=libfailingmalloc.so getfacl /bin/ls
failingmalloc: intercepting malloc in '/usr/bin/getfacl /bin/ls' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/usr/bin/getfacl /bin/ls'
Segmentation fault (core dumped)
```

To understand what's going on we can run `gdb`:
```
# gdb -ex 'set environment LD_PRELOAD=libfailingmalloc.so' -ex r --args /bin/getfacl /bin/ls
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
# gdb -ex 'set startup-with-shell off' -ex 'set environment LD_PRELOAD=libfailingmalloc.so' -ex r --args /bin/getfacl /bin/ls
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
# dpkg -S /bin/getfacl
acl: /bin/getfacl
# dpkg -S libacl.so.1
libacl1:amd64: /usr/lib/x86_64-linux-gnu/libacl.so.1
libacl1:amd64: /usr/lib/x86_64-linux-gnu/libacl.so.1.1.2253
# sudo apt-get install acl-dbgsym libacl1-dbgsym
```

Now rerun gdb and enjoy a nicely formatted backtrace:
```
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
# dpkg -S getfacl
acl: /usr/share/man/man1/getfacl.1.gz
acl: /bin/getfacl
# apt-get source acl
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
Let's see why this happens:

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

Now, of course manually applying checkers to various programs
is a tiresome and boring task.
What can we do to make it more interesting?

Few simple ideas:
  * apply your checker to each app on Linux:
    * run without arguments and stdin redirected from `/dev/null`
      (do this only in containers to avoid damaging your system!)
    * run with `--help` or `-h`
  * (for `LD_PRELOAD`-based checkers, not for the faint hearted!) boot complete Linux system
    with your checker preloaded
  * run some large system benchmark under your checker
    (e.g. [Phoronix testsuite](https://www.phoronix-test-suite.com/))

Unfortunately this is all very shallow and won't result too much loot^W bugs found.

A more promising solution is reusing builtin testsuites
which are available for many open-source packages.
For example let's try to detect a bug in libacl's unittests:
```
# cd acl-2.2.53
# find | xargs touch -m -r /bin/ls  # Fix clock skew
# apt-get install attr-dev
# ./configure
# make

# LD_PRELOAD=libfailingmalloc.so make check
failingmalloc: intercepting malloc in '/usr/bin/make check' (fail after 0 allocs)
failingmalloc: returning NULL from malloc in '/usr/bin/make check'
Segmentation fault (core dumped)
```

Ouch, our checker has tried inserting errors into top-level `make` process
and successfully failed it! On a positive side this means that make
also has bugs that we can pursue later on but
for now we just want to ignore them and proceed with libacl testing.

Let's update our checker once again, this time teaching it to
not instrument system programs and libraries.
This is done in branch [workshop/3](https://github.com/yugr/failing-malloc/compare/workshop/2...workshop/3):
```
# git -C /work/failing-malloc checkout workshop/3
# make -C /work/failing-malloc
```

Now rerun the tests:
```
# LD_PRELOAD=libfailingmalloc.so make check
...
# TOTAL: 15
# PASS:  12
# SKIP:  0
# XFAIL: 2
# FAIL:  1
# XPASS: 0
# ERROR: 0
```

Weird, most tests passed. What's going on?
The clever testwrapper overrides our `LD_PRELOAD`:
```
# grep -rC1 LD_PRELOAD
est/runwrapper-if [ -e "$PWD/.libs/libtestlookup.so" ]; then
test/runwrapper:	export LD_PRELOAD="$PWD/.libs/libtestlookup.so"
test/runwrapper-fi
```

Let's fix it for now
```
# sed -r -i -e 's/^if /if false \&\& /' test/runwrapper
```
(btw this illustrates the idea why `LD_PRELOAD` is unreliable
and we should use `/etc/ld.so.preload` instead).

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
# grep -a failingmalloc test-suite.log | head
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

As we saw manually applying checker to different OSS projects is hard:
  * we need to take care of dependencies
  * we need to build code
  * we need to consider various test system quirks

The easiest way to automate running of unit tests for many open-source projects
is to abuse^W reuse an existing distro build system.

I selected Debian as it has the most packages and has convenient automation tools (pbuilder/cowbuilder).
The main problem is that Debian build system is aimed at _building_ packages, not _testing_ them
so it does not have builtin support for running unit tests :(
But with some effort we can add some clever hooks into their build system and run tests outselves.
I've done this in [debian_pkg_test](https://github.com/yugr/debian_pkg_test) project.
We'll now use it to automate out checker.

Firstly we need to make a small adaptation failing-malloc to massive batch runs,
namely teach it to autodetect crashes and register them in dedicated place.
This is done in branch [workshop/4](https://github.com/yugr/failing-malloc/compare/workshop/3...workshop/4)
by adding support for `FAILING_MALLOC_LOGFILE`
environment variable and installing signal handler prior to retuning bad value
from `malloc`.

```
# git -C /work/failing-malloc checkout workshop/4
# make -C /work/failing-malloc
```

Now we'll clone debian_pkg_test repo and set up a pbuilder container for tests:
```
# cd /work
# git clone https://github.com/yugr/debian_pkg_test
# cd debian_pkg_test
```

Now we can install failing-malloc integration
```
# cp examples/failing-malloc/hooks/* pbuilder-shared/hooks
# cp -r /work/failing-malloc pbuilder-shared
```
and apply it to acl package:
```
$ ./test_pkgs --pbuilder acl
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

Debian_pkg_test stored all the necessary info:
failing-malloc reports, syslog and build log
to `test_pkgs.1/acl` folder. We can make sure
that expected bugs have been found:
```
$ cat test_pkgs.1/acl/output/failingmalloc.log
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
(you may need to need to change to some other `test_pkgs.N`,
depending on history of previous runs).

# Further work

At this point the checker is more or less ready
and we can unleash it's power to the world
and start filing bugreports and PRs.

From here you can pursue several directions.

Firstly you could try applying the checker to other OSS programs.
After quick skimming the packages from
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

But note that `debian_pkg_test` should preferably be run outside of Docker.

If that sounds too boring, try improving the existing checker:
  * intercept other alloc functions like `realloc` or `aligned_alloc`
    (would also be nice to figure out why `calloc` interception does not work!)
    * `dlsym` itself calls `calloc` so will need to resort to "early malloc"
      from static buffer until first successful return from `dlsym`
  * intercept `operator new` (in theory C++ insists on throwing `std::bad_cast`
    on failed allocation but many C++ programs are compiled with `-fno-exceptions`
    and simply return `NULL` on OOM)
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

or, better yet, try to come up with your own idea and
verify it's usefulness via debian_pkg_test.
For finding ideas on useful checkers try skimming through
the [openwall list](https://www.openwall.com/lists/oss-security).
