# Binary Search (ASM example)

This folder contains ASM specifications and simple runner scripts for the `binary-search` example.

## Contents

| ASM file | Content | 
|-----|-----|
| `binary-search.asm` | ASM program for binary search (only ASM rule, without invariants). |
| `binary-search-inv-wrong.asm` | Same program with an incorrect invariant (not taking termination into account) to demonstrate how the tool finds counterexamples during `-invcheck` runs. |
| `binary-search-inv-right.asm` |  Same program with a correct invariant. |

The following scripts provide abbreviations to run `asm-symbolic-execution` on the example with an array size of 4.

| Shell script | content |
|-----|-----|
| `run-steps` *n* | Generate ASM rule corresponding to the execution of $n$ steps of the binary search program (`binary-search.asm`) |
| `run-invcheck-wrong` *n* | Run invariant check for the 'wrong' property (`binary-search-inv-wrong.asm`) on states S_0, ..., S_n |
| `run-invcheck-right` *n* | Run invariant check for the 'right' property (`binary-search-inv-wrong.asm`) on states S_0, ..., S_n | 


## Usage Examples

Importante note: the following commands must be run **from the project's root folder**.

---

To construct an ASM rule corresponding to the execution of the first 4 steps:

```
examples-asmeta/binary-search/run-steps 4
```

Equivalent to:
```
dotnet run -steps 4 -file examples-asmeta/binary-search/binary-search.asm
```

---

To run invariant checks on states S_0, ..., S_4 (first 4 steps):

```
examples-asmeta/binary-search/run-invcheck-wrong 4
examples-asmeta/binary-search/run-invcheck-right 4
```

Equivalent to:
```
dotnet run -invcheck 4 -file examples-asmeta/binary-search/binary-search-inv-wrong.asm
dotnet run -invcheck 4 -file examples-asmeta/binary-search/binary-search-inv-right.asm
```

## Using different array sizes

The ASM files include several `init` blocks (`n1`, `n2`, `n3`, `n4`, `n5`, etc.) corresponding to different array sizes. By default `n4` is used (size of array = 4).

To select the init block to be used for initialisation, the `-init` option has to be used.

For example, for a size of 7, use:
```
dotnet run -asmeta-dag -init n7 -steps 5 -file examples-asmeta/binary-search/binary-search.asm
```
