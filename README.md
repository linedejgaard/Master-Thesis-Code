
# Formal Specifications of a Kernel Memory Manager in the Verified Software Toolchain



This project formally verifies the kernel memory management functions `kalloc` and `kfree` using the Verified Software Toolchain (VST) within the Rocq environment. It provides two layers of specifications: a general layer verifying simplified C implementations, and a detailed subspecification layer for verifying client functions that use the memory manager.


## Project structure

All code, specifications, and proofs were developed using **VST** within the **Rocq interactive proof environment**. The project contains approximately **3,370 lines of code**, distributed as follows:



### Implementation & Formal Representation

| File         | Description                            | Lines |
|--------------|----------------------------------------|-------|
| `kalloc.c`   | C source code for the kernel memory manager   | ~180  |
| `kalloc.v`   | Rocq formalization of `kalloc.c`              | ~845  |



### Specifications

| File             | Description                                      | Lines |
|------------------|--------------------------------------------------|-------|
| `ASI_kalloc.v`   | Abstract specification interface (API-level)     | ~85   |
| `Spec_kalloc.v`  | Detailed subspecifications of `kalloc` behavior  | ~195  |



### Proofs

| File                           | Description                                              | Lines |
|--------------------------------|----------------------------------------------------------|-------|
| `Verif_kalloc_kfree.v`         | Correctness proofs for `kalloc` and `kfree`              | ~70   |
| `Verif_allocation_examples.v` | Allocation client proofs                                 | ~265  |
| `Verif_kalloc_kfree_examples.v` | Client proofs using both `kalloc` and `kfree`          | ~845  |
| `Verif_kfree_loops_examples.v` | Proofs for clients with deallocation loops              | ~380  |



### Functional Models

| File            | Description                                  | Lines |
|------------------|----------------------------------------------|-------|
| `kallocfun.v`     | Functional model of the memory manager       | ~190  |
| `clientsfun.v`    | Functional model of client interactions      | ~260  |



### Abstract Predicate Declarations

| File           | Description                              | Lines |
|----------------|------------------------------------------|-------|
| `Kalloc_APD.v` | Abstract predicate declarations used in the specifications | ~55   |



### Supporting Files

| File         | Description                       |
|--------------|-----------------------------------|
| `_CoqProject` | Coq project configuration         |
| `Makefile`    | Build instructions                |
| `README.md`   | Project documentation             |
| `tactics.v`   | Custom proof tactics used in proofs |


## How to compile

- Compile C code to Rocq representation: `clightgen -normalize <c-file>.c`

- In this directory, use `make clean` to clean the project, and `make` to compile the Rocq files.

- Edit the `_CoqProject` file to compile fewer files. Note that some files depend on each other.

- When compiling, yields warnings which can be safely ignored.

## Dependencies

To build and work with this project, you will need the following tools:

- [Rocq](https://https://rocq-prover.org/): version **8.20.1**
- [CompCert](http://https://compcert.org/): version **3.15**
- [OCaml](https://ocaml.org/): version **4.12.0** (used to compile Rocq)
- [GNU Make](https://www.gnu.org/software/make/): version **3.81**
- [Verified Software Toolchain (VST)](https://vst.cs.princeton.edu/): version **2.15**
