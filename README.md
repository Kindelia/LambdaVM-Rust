Higher-order Virtual Machine 2 (HVM2)
=====================================

**Higher-order Virtual Machine 2 (HVM2)** is a massively parallel [Interaction
Combinator](https://www.semanticscholar.org/paper/Interaction-Combinators-Lafont/6cfe09aa6e5da6ce98077b7a048cb1badd78cc76)
evaluator.

By compiling programs from high-level languages (such as Python and Haskell) to
HVM, one can run these languages directly on massively parallel hardware, like
GPUs, with near-ideal speedup.

HVM2 is the successor to [HVM1](https://github.com/HigherOrderCO/HVM1), a 2022
prototype of this concept. Compared to its predecessor, HVM2 is simpler, faster
and, most importantly, more correct. [HOC](https://HigherOrderCO.com/) provides
long-term support for all features listed on its [PAPER](./paper/HVM2.pdf).

This repository provides a low-level IR language for specifying the HVM2 nets
and a compiler from that language to C and CUDA. It is not meant for direct
human usage. If you're looking for a high-level language to interface with HVM2,
check [Bend](https://github.com/HigherOrderCO/Bend) instead.

Usage
-----

> DISCLAIMER: Windows is currently not supported, please use [WSL](https://learn.microsoft.com/en-us/windows/wsl/install) for now as a workaround.

First install the dependencies:
* If you want to use the C runtime, install a C-11 compatible compiler like GCC or Clang.
* If you want to use the CUDA runtime, install CUDA and nvcc (the CUDA compiler).
  - _HVM requires CUDA 12.x and currently only works on Nvidia GPUs._

Install HVM2:

```sh
cargo install hvm
```

There are multiple ways to run an HVM program:

```sh
hvm run    <file.hvm> # interpret via Rust
hvm run-c  <file.hvm> # interpret via C
hvm run-cu <file.hvm> # interpret via CUDA
hvm gen-c  <file.hvm> # compile to standalone C
hvm gen-cu <file.hvm> # compile to standalone CUDA
```

All modes produce the same output. The compiled modes require you to compile the
generated file (with `gcc file.c -o file`, for example), but are faster to run.
The CUDA versions have much higher peak performance but are less stable. As a
rule of thumb, `gen-c` should be used in production.

Language
--------

HVM is a low-level compile target for high-level languages. It provides a raw
syntax for wiring interaction nets. For example:

```javascript
@main = a
  & @sum ~ (28 (0 a))

@sum = (?(((a a) @sum__C0) b) b)

@sum__C0 = ({c a} ({$([*2] $([+1] d)) $([*2] $([+0] b))} f))
  &! @sum ~ (a (b $([+] $(e f))))
  &! @sum ~ (c (d e))
```

The file above implements a recursive sum. If that looks unreadable to you -
don't worry, it isn't meant to. [Bend](https://github.com/HigherOrderCO/Bend) is
the human-readable language and should be used both by end users and by languages
aiming to target the HVM. If you're looking to learn more about the core
syntax and tech, though, please check the [PAPER](./paper/HVM2.pdf).

Interaction Net graph dumping and visualization
-----------------------------------------------

With the rust interpreter (`hvm run`), every evaluation step can be dumped with
the `--dump` command line option. You can dump in sequential mode (only one
redex is evaluated in each step) or, with the `--parallel` option,
in parallel mode (all redexes are evaluated in each step).

The dump will be written to the file `dots.js` in the current directory.

You can view the graph dump with `index.html` as follows:

Copy the file `dots.js` to the HVM directory. Then start a http server in the
HVM directory:

```sh
cd HVM
python3 -m http.server
```

Now you can visit `http://127.0.0.1:8000` and step through the graph with
the wasd keys on your keyboard.

How parallel is my Bend/HVM program?
------------------------------------

With the `--parallel` option, HVM also calculates the average number of regexes
in each step, thus giving a measurement of how parallel a given bend program is.

You can use the `--parallel` option without the `--dump` option as well.