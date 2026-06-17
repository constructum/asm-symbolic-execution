## Summary

This is a prototype tool for symbolic execution of Abstract State Machines (ASM). It supports a subset of the [AsmetaL](https://asmeta.github.io/userdoc.html) ASM-based specification language.

This [animation](https://github.com/constructum/asm-symbolic-execution/blob/main/doc/binary-search-example-animation.pdf) shows through a simple [example](https://github.com/constructum/asm-symbolic-execution/blob/main/doc/binary-search-example-animation.pdf) (an ASM rule implementing a binary search) how the ASM symbolic execution works.

## Papers

The following papers describe the principles on which the tool is based and an application to smart contract verification:

- [***A Symbolic Execution Approach to Bounded Verification of Abstract State Machines***](https://link.springer.com/chapter/10.1007/978-3-032-24494-9_8). In: A. Raschke, E. Riccobene, K.-D. Schewe, B. Thalheim (editors), [*Rigorous Methods in Theory and Practice — Essays Dedicated to Egon Börger on the Occasion of His 80th Birthday*, Lecture Notes in Computer Science (LNCS), vol. 16580](https://link.springer.com/book/10.1007/978-3-032-24494-9), Springer, 2026.
<br>**[\[PDF of preprint\]](https://github.com/constructum/asm-symbolic-execution/blob/main/doc/2026--Del-Castillo--preprint--A-Symbolic-Execution-Approach-to-Bounded-Verification-of-ASM.pdf)**
<br>This is the most complete and up-to-date description of the symbolic execution method implemented by the `asm-symbolic-execution` tool.

- [***Using Symbolic Model Execution to Detect Vulnerabilities of Smart Contracts***](https://doi.org/10.1007/978-3-031-94533-5_3) (with Chiara Braghin, Elvinia Riccobene, Simone Valentini). In: M. Leuschel, F. Ishikawa (editors), [*Rigorous State-Based Methods — 11th International Conference, ABZ 2025, Düsseldorf, Germany, June 10–13, 2025, Proceedings*, Lecture Notes in Computer Science (LNCS), vol. 15728](https://link.springer.com/book/10.1007/978-3-031-94533-5), Springer, 2025.
<br>**[\[PDF of preprint\]](https://github.com/constructum/asm-symbolic-execution/blob/main/doc/2025--Braghin--Del-Castillo--Riccobene--Valentini--Symbolic-Model-Execution-Smart-Contract--ABZ2025-preprint.pdf)**
<br>
This paper describes an application to the detection of vulnerabilities in Ethereum smart contracts modelled in [AsmetaL](https://asmeta.github.io/userdoc.html). <!-- For this purpose, the tool was extended to support invariant checking in runs of single-agent ASMs.--> The [smart contract models](https://github.com/smart-contract-verification/ABZ2025) can be found in this [GitHub repository](https://github.com/smart-contract-verification/ABZ2025). The version of the tool used for the experiments of this paper is in the [ABZ2025 branch](https://github.com/constructum/asm-symbolic-execution/tree/ABZ2025).


- [***Using Symbolic Execution to Transform Turbo Abstract State Machines into Basic Abstract State Machines***](https://link.springer.com/chapter/10.1007/978-3-031-63790-2_15). In: S. Bonfanti, A. Gargantini, M. Leuschel, E. Riccobene, P. Scandurra (editors): [*Rigorous State-Based Methods — 10th International Conference, ABZ 2024, Bergamo, Italy, June 25–28, 2024, Proceedings*, Lecture Notes in Computer Science (LNCS), vol. 14759](https://link.springer.com/book/10.1007/978-3-031-63790-2), Springer, 2024.
<br>This short paper is the first published description of the ASM symbolic execution method on which the tool is based. 
<br>**[\[PDF of an extended version of the ABZ 2024 paper\]](https://github.com/constructum/asm-symbolic-execution/blob/main/doc/2024--Del-Castillo--extended-version-of-ABZ-2024-paper.pdf)**
<br>The extended version additionally includes a summary of ASM syntax and semantics, more detailed explainations, a short description of the implementation, examples and experimental results.


## Installation

To run the tool, the .NET environment must be installed on the system.

In principle, the necessary dependencies (in particular, the [Z3](https://github.com/Z3Prover/z3/wiki) SMT solver) should be imported automatically via .NET.

However, under Linux, an appropriate version of the Z3 shared library must be installed manually and the `LD_LIBRARY_PATH` environment library must be set accordingly.


## Examples

The examples mentioned in the 2024 paper can be found in the `examples/` folder.

More recent examples, written in [AsmetaL](https://asmeta.github.io/userdoc.html), can be found in the [`examples-asmeta/`](https://github.com/constructum/asm-symbolic-execution/tree/main/examples-asmeta) folder.


## Command line interface

(to be invoked from the project's root folder)

```
dotnet run [OPTION]...
```

```
Options:
  -str <strg>    load definitions specified in string <strg>
                   into the top-level environment
  -file <file>   load definitions contained in file <file>
                   into top-level environment

  -legacy        use legacy UASM-based language as input language
  -asmeta        use AsmetaL as input language
  -asmeta-dag    use AsmetaL with DAG-based symbolic execution (default)
  -init <state>  (AsmetaL only) start from initial state named <state>
  -invcheck <n>  (AsmetaL only) check invariants during symbolic execution
                   for at most <n> steps or indefinitely, if <n> not specified

  -symbolic      symbolic execution of 'Main' rule (default)
  -steps <n>     symbolic execution of <n> steps of 'Main' rule
                   starting from initial state (default: n = 1)

  -nonsymbolic   execute 'Main' rule non-symbolically

  -turbo2basic   turbo ASM to basic ASM transformation
                   (all non-static functions are uninterpreted)

  -nosmt         do not use SMT solver

  -license       display license information
```
