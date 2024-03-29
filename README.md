## Summary

This is a prototype tool for symbolic execution of Abstract State Machines (ASM).

The principles on which it is based are described in a paper titled "Elimination
of Sequential Composition from Abstract State Machines Rules by Symbolic
Execution" submitted to the [ABZ 2024](https://abz-conf.org/site/2024/)
conference.

The tool implements a transformation of ASM transition rules, which eliminates `seq` and `iterate` rules to obtain a transition rule that condenses a whole sequential computation into one single step.

## Installation

To run the tool, the .NET environment must be installed on the system.

The dependencies ([Z3](https://github.com/Z3Prover/z3/wiki) SMT solver) should be imported automatically via .NET. However, some tweaking may be required due to possible version incompatibilities of dynamic libraries (this was at least my experience).

## Examples

The examples mentioned in the paper can be found in the `examples/` folder.

In each folder there is a `run` script (or, in the quicksort example, two scripts `run-a` and `run-b` for the two different versions) to symbolically execute the example with the given parameter(s), typically the input size (e.g. for the sorting algorithms).

In each folder there is a `run-tests` script to execute the example multiple times with different values of the parameters and output the results in text files in the respective folder and a `run-tests-nosmt` that does the same but does not invoke the SMT solver during symbolic execution.


## Command line interface

(to be invoked from the project's root folder)

```
dotnet run [OPTION]...
```

```
Options:
  -str <strg>   load definitions specified in string <strg>
                  into the top-level environment
  -file <file>  load definitions contained in file <filename>
                  into top-level environment

  -symbolic         symbolic execution of 'Main' rule (default)
  -nonsymbolic      execute 'Main' rule non-symbolically

  -nosmt            do not use SMT solver
