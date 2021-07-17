---
theme: gaia
_class: lead
paginate: true
backgroundColor: #fff
backgroundImage: url('https://marp.app/assets/hero-background.jpg')

---

# **Runtime verification**

(aka Dynamic Analysis)

[Lalambda '21](https://github.com/yugr/Lalambda/tree/master/21)

---

# Something about the author

* www.github.com/yugr
* TL @ Samsung Moscow
* Accidentally became a compiler writer 15 years ago
  * In-house, GCC, LLVM, neurocompilers (also some HPC and gamedev)
* Passionate about verification in general and dynamic/static analyses in particular

![bg right:33% 80%](https://avatars.githubusercontent.com/u/1101391?v=4)

---

# Disclaimer

* C/C++-focused (although ideas are generally applicable)
* Gives big picture overview without delving into details

---

# Overview

* Runtime verification aka dynamic analysis
* Instrumentation of programs to verify invariants (safety, performance, etc.)
* (Much) more widely used in industry than static tools:
  * no false positives
  * reprocases easily available
  * no scalability problems

---

# Disadvantages

* Limited coverage
* Solved via
  * fuzzing
  * rule/grammar-based input generators
  * AB-testing in production

---

# Example analyses

* Virtual memory :)
* C/C++ assertions in programs
* Library sanity checks (e.g. Glibc `malloc` internal checks)
* Valgrind
* Sanitizers (Asan, UBsan, Msan, Tsan, etc.)

---

# Ontology of dynamic analysis project

Runtime analysis project contains of three main "parts":
  * spec: an invariant that we want to check
  * instrumentation: a way to verify that invariant is preserved during execution
  * test corpus: input data which we run checker through

New successful checkers are created by innovating in any of the three components.

---

# Creating new checkers: spec

The "spec" part:
  * come up with a new class of bugs and propose method to autodetect them
  * e.g. [Sortchecker](https://github.com/yugr/sortcheck)) was the first tool to check [qsort axioms](https://lists.llvm.org/pipermail/llvm-dev/2016-January/093835.html)

---

# Creating new checkers: instrumentation

The "instrumentation" part:
  * develop new ways to detect more errors from the same spec more efficiently
  * e.g. there were many buffer overflow checkers before [Asan](https://clang.llvm.org/docs/AddressSanitizer.html) but too slow or with limited coverage

---

# Creating new checkers: coverage

The "test corpus" part: find ways to significantly increase coverage by extending test corpus
  * via clever fuzzing
    * e.g. [AFL](https://lcamtuf.coredump.cx/afl/) revolutionized fuzzing by taking code coverage into account
  * by developing generator for sufficiently important class of data
    * e.g. [Defensics](https://www.synopsys.com/software-integrity/security-testing/fuzz-testing.html) supports grammar-based test generation for [250+ protocols](https://www.synopsys.com/software-integrity/security-testing/fuzz-testing/defensics.html)
    * e.g. [Csmith](https://embed.cs.utah.edu/csmith) generates random C++ code for compiler testing

---

# Spec taxonomy (1)

* Memory errors ([Asan](https://clang.llvm.org/docs/AddressSanitizer.html)/[Msan](https://clang.llvm.org/docs/MemorySanitizer.html), [Valgrind](https://www.valgrind.org)):
  * liveness errors: accessing after end-of-life (UAR, UAF, iterator invalidation)
  * buffer overflow: heap, global, stack
  * Uninitialized memory
* Typing errors:
  * aliasing violations ([TypeSanitizer](http://llvm.org/devmtg/2017-10/slides/Finkel-The%20Type%20Sanitizer.pdf))
  * mismatched types ([libcrunch](https://github.com/stephenrkell/libcrunch))

---

# Spec taxonomy (2)

* Parallel programming errors (Tsan):
  * deadlocks and races
* Language-specific errors:
  * integer overflows ([UBsan](https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html))
  * static init order fiasco ([Asan](https://clang.llvm.org/docs/AddressSanitizer.html)

---

# Spec taxonomy (3)

* Invalid usage of APIs:
  * not checking return codes of syscalls or standard APIs
  * mismatched memory allocation API (calling `free` on `new`-ed pointer)
  * invalid comparators

---

# Instrumentation taxonomy

* Runtime verification is trivial in languages like Python or Java
  * Full access to AST at runtime
* Checkers for native code are categorized by stage in compilation pipeline and mechanism used for instrumentation

---

# Instrumentation taxonomy: preprocess-time

* Code can be instrumented by forced inclusion of debug header
  * e.g. via `-include mycheker.h`
  * header would contain something like `#define malloc my_safe_malloc` 
* Examples:
  * [dmalloc](https://dmalloc.com)
  * [_FORTIFY_SOURCE](https://access.redhat.com/blogs/766093/posts/1976213)

---

# Instrumentation taxonomy: compile-time

* Compile-time instrumentation:
  * source-to-source (e.g. [libcrunch](https://github.com/stephenrkell/libcrunch))
    * traditionally done via [CIL](https://github.com/cil-project/cil) but it's C only :(
    * [Clang LibTooling](https://clang.llvm.org/docs/LibTooling.html) supports C++ but is complicated to use due to overdetailed AST
  * codegen-based (e.g. [Asan](https://clang.llvm.org/docs/AddressSanitizer.html) or [DirtyPad](https://github.com/yugr/DirtyPad))
  * asm-based (e.g. [DirtyFrame](https://github.com/yugr/DirtyFrame) or [AFL](https://github.com/google/AFL/blob/master/afl-as.c))

---

# Instrumentation taxonomy: link-time

Link-time instrumentation:
  * replacing normal code with "checking" implementations at link time
  * e.g. via `-Wl,--defsym,malloc=my_safe_malloc`
  * e.g. [\_malloc_dbg](https://docs.microsoft.com/en-us/cpp/c-runtime-library/reference/malloc-dbg?view=msvc-160) replaces normal `malloc` if user links against debug version of Microsoft runtime

---

# Instrumentation taxonomy: run-time

* Run-time instrumentation types:
  * `LD_PRELOAD`-based (e.g. [ElectricFence](https://elinux.org/Electric_Fence), [sortchecker](https://github.com/yugr/sortcheck), [failing-malloc](https://github.com/yugr/failing-malloc))
  * syscall instrumentation (e.g. [SystemTap](https://sourceware.org/systemtap/wiki))
  * interpretation/JITs (e.g. [Valgrind](https://www.valgrind.org), [DynamoRIO](https://dynamorio.org) or [Intel Ping](https://software.intel.com/content/www/us/en/develop/articles/pin-a-dynamic-binary-instrumentation-tool.html))

---

# How to test a checker (1)

* Once checker is ready you'll want to test it on as much code as you can
* Manually apply checker to important OSS projects (archivers, media processing libraries, browsers, etc.)
  * to find interesting package faster:
    * [popularity rating](https://popcon.debian.org/by_vote)
    * [Debian codesearch](https://codesearch.debian.net)
  * build and run unittests
  * manual work: tiresome and demotivating

---

# How to test a checker (2)

* Run all apps in `/bin` and `/usr/bin`
  * without params, with `--help`, with `--version`
  * automatic but coverage is low
* System-level instrumentation
  * run system benchmarks (e.g. [Phoronix suite](https://www.phoronix-test-suite.com))
    * manual work and coverage is still low

---

# How to test a checker (3)

* For `LD_PRELOAD`-based checkers: boot complete Linux distro with your checker preloaded
  * LD_PRELOAD-only and need to perform manual actions to explore system behavior

---

# How to test a checker: comparison

<style scoped>
table {
  font-size: 90%
}
</style>

Test                              | Automatic | Coverage | All checkers
----------------------------------|-----------|----------|-------------
Manual package testing            | N         | High     | Y
Running apps with standard params | Y         | Low      | LD_PRELOAD-ony
System benchmarks                 | Y         | Low      | Y
Distro boot                       | Y         | Low (need manual actions to increase) | LD_PRELOAD-only

---

# Using distro build systems

* Ideal solution is package unittests but it requires manual work
* Linux distros come with a vast number of packages
* Distro build systems can be reused
  * to apply checkers under the hood
  * and run package-specific unittests
* [Debian build toolchain](https://en.wikipedia.org/wiki/Debian_build_toolchain)
  * Sadly only builds, not tests, but ...

---

# debian_pkg_test

* With some hacking we can make Debian build system to run tests for us!
* [debian_pkg_test](https://github.com/yugr/debian_pkg_test) project
  * based on [pbuilder](https://wiki.ubuntu.com/PbuilderHowto)
  * runs `make check` (or other standard test commands) once package build completes

---

# Trends (1)

Increasing fuzzing speed and efficiency (coverage) by various means
  * feedback-driven ("grey-box")
    * [AFL](https://lcamtuf.coredump.cx/afl/) and related tools (gofuzz, libfuzzer, etc.)
  * analysis-driven ("white-box")
    * [Billions and Billions of Constraints: Whitebox Fuzz Testing in Production](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/main-may10.pdf)
  * various combinations thereof

---

# Trends (2)

Increasing adoption in community:
  * inspire project owners to write fuzzing for their projects through initiatives like [oss-fuzz](https://github.com/google/oss-fuzz)
  * bug bounty programs e.g. [Google Fuzzilli](https://portswigger.net/daily-swig/google-launches-fuzzilli-grant-program-to-boost-js-engine-fuzzing-research)

---

# Links

* [Runtime Verificaton conference](https://runtime-verification.github.io] ([Springer](https://link.springer.com/conference/rv))
  * Too scientific
  * Most papers are on verifying temporal logic assertions at runtime
* More practical: vulnerability reports
  * [CVE reports](https://www.openwall.com/lists/oss-security)
  * [DEFCON](https://www.defcon.org/images/defcon-15)
  * [Blackhat](https://www.blackhat.com)

TODO: confirm with surveys

---

# The End

Please share your ideas on runtime verification!
  * tetra2005 beim gmail punct com
  * TG @the_real_yugr
  * GH [yugr](https://www.github.com/yugr)
  * Habr [the_real_yugr](https://habr.com/ru/users/the_real_yugr/)

---

# Checker gotchas

* Instead of testing that bad objects are not accessed, make sure that such accesses cause havoc
  * Fill undef memory/regs with garbage (MSVS does this with mallocked memory)
  * Unmap page after buffer to force segfault (ElectricFence)
  * Fill gaps in stack frame with random values (DirtyFrame)
  * Fill struct pads with random values (DirtyPad)
  * Intro random delays in Pthread-based programs
