# Solid source artifact

This repository contains a snapshot of the source code of Solid, a _prototype_
refinement type inference tool used to identify when it is safe to avoid integer
overflow runtime checks in Solidity smart contracts. The type system and Solid
are described in our paper:

> Bryan Tan, Benjamin Mariano, Shuvendu K. Lahiri, Isil Dillig, and Yu
> Feng. 2022. SolType: Refinement Types for Arithmetic Overflow in Solidity.
> Proc. ACM Program. Lang. 6, POPL, Article 4 (January 2022), 29 pages.
> DOI: https://doi.org/10.1145/3498665

The source code is provided **AS-IS** with **NO GUARANTEE that it is correct,
user-friendly, or bug-free**. Expect unclean, poorly written, "research-quality"
code that was written by a sleep-deprived grad student frantically trying to
meet deadlines. **Do not use this on a smart contract you plan to deploy**
unless you know what you are doing. You have been warned.

Before you look at the source code, you are strongly recommended to check out
our [evaluation artifact, which is located on Zenodo][eval-artifact-link].

## Building and Running

### Building

Make sure you run `git submodule update --init --remote --recursive` first to
pull in some necessary dependencies.

You will need to have [Stack][haskell-stack] installed and Z3 available on
`PATH`.

Compile the project with `stack build`. Install the tool using `stack install`,
which will copy the tool to a folder on `$PATH` (hopefully). Or instead of
installing, you can run the program directly using `stack run solid-exe -- <args..>`.

In short, if you are starting from scratch:
```
# retrieve project and dependencies
git clone https://github.com/UCSB-PLSE/solid-public.git
git submodule update --init --remote --recursive

# compile
stack build

# copy executable to folder on $PATH
stack install

# run it
solid-exe --help
```

Note: if you recompile the project, you will need to reinstall it with `stack
install` or else you will keep using the old version!

Trivia: for historical reasons, we initially named the tool "LiquidSol" because
the idea was to develop something like Liquid Types [Rondon et al 2008] but for
Solidity. Although the final name of the tool ended up as "Solid" in the paper,
we never bothered to change the code.

### Usage

A good description of how to use this tool can be found in the [evaluation
artifact README][eval-artifact-link].

* To run the tool, use `solid-exe <src file>`. By default, the tool will run
  in inference mode, i.e. it will invoke the CHC solver to find an invariant
  that can eliminate safe math operations.
* Solid currently only supports Solidity `0.4.x`, `0.5.x`, and `0.6.x`.
* A `solc` binary is required on `$PATH`. You can specify a custom `solc` binary
  by providing the argument `--solc <path to solc>`.
* There are three modes in `solid`, which can be set by the `--task <mode>`
  argument:
  * `infer` (default): this is called "AutoSolid" in the paper. This uses a CHC
    solver to find an invariant that can identify redundant safe math
    operations. This will use the safe math elmination algorithm by default. An
    alternative solving algorithm that makes only a single query is available by
    adding a `--mode fast` option. Note that the alternative solving algorithm
    either finds an invariant or fails completely!
  * `check`: this is called "SemiSolid" in the paper. Given the contract
    invariant provided by the `--check-inv <invariant string>` argument,
    determine whether any constraints are violated assuming that the contract
    invariant holds.
* Change the timeout options with `--query-timeout` and `--total-timeout`. The
  former controls sets the timeout to Z3 in milliseconds, while the latter sets
  the timeout of the overall task in seconds.
* To debug the CHC solver queries, provide the `--debug-smt` flag to print them
  to stdout. Alternatively, log the queries to a folder using the `--logdir
  <folder>` flag.
* If a source file contains multiple contracts, then the tool will run on every
  fully implemented contract (i.e. not missing any required interface functions)
  in the file. To control which contracts should be run, supply either the
  `--only <name>` option or the `--only-last` option.

## Refinement terms and annotations

### Predicates

Solid includes a refinement term parser to allow users to provide contract
invariants and annotations. See `src/LiquidSol/Parser.y` for the syntax. In
particular, the following terms are allowed:

* Arithmetic, relations, and boolean operations: e.g. `+ - * / % > < >= <= != == &&`
* Integer literals: e.g. `12345`, etc.
* Storage variables: e.g. `x`, `y`, `totalSupply`, `balances`
* Array/mapping indexing and struct field accesses: `balances[0]`, `mystruct.x`
* Sum: can express the sum of a mapping of uints, e.g. `sum(balances)`.
* Flatten: can express the flattening of a nested mapping of uints for a sum,
  e.g. `sum(flatten(allowances))` where `allowances` is a `mapping(address =>
  mapping(address => uint))`.
* Fld: can express the field project of a as `fld(S, f, x)` where `S` is the
  name of the struct, `f` is the name of the field, and `x` is the mapping.
  E.g., `sum(fld(User, amount, users))` expresses the sum of the `amount` fields
  of the entries of the mapping `users`.
* Implication: e.g. `true ==> false`

[haskell-stack]: https://docs.haskellstack.org/en/stable/README/
[eval-artifact-link]: https://doi.org/10.5281/zenodo.5553960
