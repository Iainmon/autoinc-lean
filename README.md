# autoinc-lean

## Overview

`autoinc-lean` (**Auto**matic **inc**remental computation in **Lean**) is a formal framework for building and reasoning about incremental computation.
  
The main goal of `autoinc-lean` is to investigate methodologies for automatically compiling a standard computation $C$ into an incremental computation $\Delta C$, such that $\Delta C$ is asymptotic faster than $C$. 

The strategy of `autoinc-lean` for incrementalizing programs is called *differential updating*, which translates a program's input changes to output changes. 

## Installation

This project is known to compile with Lean v4.27.0-rc1. 
Please read [this](https://lean-lang.org/install/) website to install lean in your computer.
After that, you may run the following commands to install dependencies and compile this project:

```
$ lake exe cache get
$ lake build
```



We have only tested the installation on MacOS, but we expect it to work on Linux and Windows systems as well.


## Example

Consider the dataflow of a word-count program 

```
text.toLowerCase().split(" ").filter(isNotEmpty).count()
```

![](<Utils/wordcount.svg>)

To process input changes (e.g., appending a whitespace), differential updating transforms the above program into the following form, where each primitive `f : A -> B` is replaced by its respective *differential operator* `Δf : ΔA -> ΔB`:

![](<Utils/dwordcount.svg>)

By exploiting the algebraic properties of data changes and string functions, differential updating derives the output changes in time proportional to the size of the input modification rather than to the total data size.


This repository provides an interface for building and verifying differential operators. 
Notably, this interface is monadic, allowing using various effects to implement expressive operators.
Here is a differential operator for `List.reverse : List α -> List α`:

```lean4
def Δreverse [MonadStateOf Nat m] : Operator (List β) (List β) (ΔList β) (ΔList β) m where
  f x := do set x.length; pure x.reverse
  Δf dx := do let s <- get; match dx with
    | ins i l => set (s + l.length); pure (ins (s - i) l.reverse)
    | del i n => set (s - n); pure (del (s - i - n) n)
```

This operator uses a `Nat` state (the length of original input) to compute the output changes in time proportional to the size of `dx` (input change), which achieves asymptotic speedup over `List.reverse` function.


## Project structure

- `./Autoinc.lean`: root of the `Autoinc` library
- `./Autoinc/Change.lean`: definition of change structure
- `./Autoinc/Operator.lean`: definition of monadic operators
- `./Autoinc/Monad.lean`: definition and instances of monadic change structures
- `./Autoinc/Partial.lean`: definition of partial differential operators (which processes changes a single parameter within an n-ary function)
- `./Autoinc/Lazy.lean`: definition and laws of lazy state monad 
- `./Autoinc/Combinator.lean`: combinators for differential operators
- `./Autoinc/Data/*`: change structure and differential operators for different data types
- `./Benchmark/*`: microbenchmarks for measuring the performance of list differential operators
  - `./Benchmark/List/Examples/*.lean`: incremental computation built with monadic list differential operators
  - `./Benchmark/Main.lean`: entry of benchmark, the command to run the benchmark: `lake -q exe benchmark`



## Contribution

The development of `autoinc-lean` is lead by the [PL Team](https://pl.ipd.kit.edu/index.php) from KIT under the ERC project "AutoInc: Asymptotic Speedups for Free through Automatic Incremental Computing" ([link](https://incremental.dev/)).
This repository serves as a snapshot to showcase the current progress, which is why it contains only a single commit. If you are interested, we warmly welcome you to contact the developers. The current contributors are:

- [Sebastian Erdweg](https://github.com/seba--)
- [Runqing Xu](https://github.com/runqingxu)
- [Iain Moncrief](https://github.com/iainmon)
- [Oliver Enes](https://github.com/eneoli)