# SECDA

Formalization of a SECD machine [1][2] in Agda with typed assembly.

Work in progress.

[1] https://en.wikipedia.org/wiki/SECD_machine

[2] https://xavierleroy.org/mpri/2-4/machines.pdf

## Aims
- Syntactical formalization of typed assembly, giving a higher assurance in compilers to this instruction set;
- Semantics by way of an embedding to Agda (utilizing coinduction to model possibly-nonterminating execution);

### Further ideas of interest
- Syntax & embedding to Agda of an untyped lambda calculus with syntactical translation to SECD instructions and proof of preservation of semantics by this translation, thus proving correctness (difficult?);
- Compilation from our typed assembly to x86 / ARM assembly.
