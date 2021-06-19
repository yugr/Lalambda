---
theme: gaia
_class: lead
paginate: true
backgroundColor: #fff
backgroundImage: url('https://marp.app/assets/hero-background.jpg')
---

# Something about the author

* Accidentally became a compiler engineer 15 years ago
* In-house, GCC, LLVM, neurocompilers (also some HPC and gamedev)
* Passionate about verification in general and dynamic/static analyses in particular
* www.github.com/yugr
  * _There's some really nice stuff there, don't hesitate to check (and star if you like something)_

TODO: photo

# Overview

* Runtime verification aka dynamic analysis
* Instrumentation of programs to verify invariants (safety, performance, etc.)
* (Much) more widely used in industry than static tools:
  * no false positives
  * reprocases easily available
  * no scalability problems
* Cons
  * limited coverage (solved by fuzzing and rule-based input generators)

# Example analyses

* Virtual memory :)
* C/C++ assertions in programs
* Library sanity checks (e.g. Glibc `malloc` internal checks)
* Valgrind
* Sanitizers (Asan, UBsan, Msan, Tsan, etc.)

# Ontology of dynamic analysis project

Runtime analysis project contains of three main "parts":
  * spec: an invariant that we want to check
  * instrumentation: a way to verify that invariant is preserved during execution
  * test corpus: input data which we run checker through

# Creating new checkers: spec and instrumentation

New successful checkers are created by innovating in any of the three components:
  * one can come up with a new class of bugs and propose method to autodetect them (the "spec" part, e.g. [Sortchecker](https://github.com/yugr/sortcheck))
  * or she could develop new ways to detect more errors from the same spec more efficiently (the "instrumentation" part, e.g. [Asan](https://clang.llvm.org/docs/AddressSanitizer.html))

# Creating checkers: tests

  * or finally she could find ways to significantly extend test corpus
    * via clever fuzzing (e.g. [AFL](https://lcamtuf.coredump.cx/afl/) revolutionized fuzzing by taking code coverage into account)
    * by developing generator for sufficiently important class of data (e.g. [Csmith](https://embed.cs.utah.edu/csmith) generates random C++ code for compiler testing)

# Spec taxonomy

TODO

# Instrumentation taxonomy

* Runtime verification is trivial in languages like Python or Java
  * Full access to AST at runtime
* Checkers for native code are categorized by stage in compilation pipeline and mechanism used for instrumentation

# Instrumentation taxonomy: compile-time

* Preprocess-time:
  * [_FORTIFY_SOURCE](https://access.redhat.com/blogs/766093/posts/1976213)
  * `#define malloc safe_malloc` e.g. [dmalloc](https://dmalloc.com)
* Compile-time instrumentation:
  * source-to-source (e.g. via Clang tooling)
  * codegen-based (e.g. [Asan](https://clang.llvm.org/docs/AddressSanitizer.html) or [DirtyPad](https://github.com/yugr/DirtyPad))
  * asm-based (e.g. [DirtyFrame](https://github.com/yugr/DirtyFrame) or [AFL](https://github.com/google/AFL/blob/master/afl-as.c))

# Instrumentation taxonomy: link-time

Link-time instrumentation:
  * replacing normal code with "checking" implementations at link time
  * e.g. [\_malloc_dbg](https://docs.microsoft.com/en-us/cpp/c-runtime-library/reference/malloc-dbg?view=msvc-160) replaces normal `malloc` if user links against debug version of Microsoft runtime

# Instrumentation taxonomy: run-time

* Run-time instrumentation types:
  * `LD_PRELOAD`-based (e.g. [ElectricFence](https://elinux.org/Electric_Fence), [sortchecker](https://github.com/yugr/sortcheck), [failing-malloc](https://github.com/yugr/failing-malloc))
  * syscall instrumentation (e.g. [SystemTap](https://sourceware.org/systemtap/wiki))
  * interpretation/JITs (e.g. [Valgrind](https://www.valgrind.org), [DynamoRIO](https://dynamorio.org) or [Intel Ping](https://software.intel.com/content/www/us/en/develop/articles/pin-a-dynamic-binary-instrumentation-tool.html))

# How to test a checker

* Run all apps in `/bin` and `/usr/bin`: without params, with `--help`, with `--version`
  * cons: coverage is low
* System-level instrumentation:
  * run system benchmarks (e.g. [Phoronix suite](https://www.phoronix-test-suite.com))
    * cons: not many of those
  * for `LD_PRELOAD`-based checkers: boot complete Linux distro with your checker preloaded
    * cons: LD_PRELOAD only
    * cons: need to perform manual actions to explore system behavior
* Manually apply checker to important OSS projects (archivers, media processing libraries, browsers, etc.)
  * cons: manual work is tiresome and demotivating

TODO: table

# Using distro build systems

* Linux distros come with a vast number of packages
* Their build systems can be reused to apply your checker under the hood and run package-specific unittests
* [Debian build toolchain](https://en.wikipedia.org/wiki/Debian_build_toolchain)
  * Sadly only builds, not tests, but ...

# debian_pkg_test

* With some hacking we can make Debian build system to run tests for us
* [debian_pkg_test](https://github.com/yugr/debian_pkg_test)
  * uses pbuilder hooks to run `make check` and other standard test commands once build completes

# Checker gotchas

* Instead of testing that bad objects are not accessed, make sure that such accesses cause havoc
  * Fill undef memory/regs with garbage (MSVS does this with mallocked memory)
  * Unmap page after buffer to force segfault (ElectricFence)
  * Fill gaps in stack frame with random values (DirtyFrame)
  * Fill struct pads with random values (DirtyPad)
  * Intro random delays in Pthread-based programs

TODO: where to put this

Gotchas

* For LD_PRELOAD: do not apply to system files
* For asm/compile: provide options via env variable
* Find interesting package faster:
  * popularity rating
  * Deb package search

Interesting topics:

* Automatic specification mining
  * "Mutation-driven Generation of Unit Tests and Oracles" https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.472.7671&rep=rep1&type=pdf
* Automatic test generation by on-the-fly mutation aka fuzzing (AFL/libFuzzer at wide-scale)
  * "Growing A Test Corpus with Bonsai Fuzzing" https://arxiv.org/pdf/2103.04388.pdf
  * "Whole testsuite generation" https://www.evosuite.org/wp-content/papercite-data/pdf/tse12_evosuite.pdf
  * alternative (more realistic?) industry solutions:
    * inspire project owners to write fuzzing for their projects (https://github.com/google/oss-fuzz)
    * bug bounties (https://portswigger.net/daily-swig/google-launches-fuzzilli-grant-program-to-boost-js-engine-fuzzing-research)
* Concolic OSS projects

# Links

* [Runtime Verificaton conference](https://runtime-verification.github.io] ([Springer](https://link.springer.com/conference/rv))
  * Too scientific
  * Most papers are on verifying temporal logic assertions at runtime
* More practical: vulnerability reports
  * [DEFCON](https://www.defcon.org/images/defcon-15)
  * [Blackhat](https://www.blackhat.com)
  * [CVE reports](https://www.openwall.com/lists/oss-security)

# The End

Please share your ideas on runtime verification!
  * tetra2005 beim gmail punct com
  * TG @the_real_yugr
