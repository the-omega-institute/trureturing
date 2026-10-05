# Li–Jiang Polar-Pair Optimality: An Exact Finite-Noise Refutation

## Abstract

A feasible qubit rank-one encoder has strictly larger canonical-purification fidelity than the Li–Jiang polar encoder paired with the actual right partial trace at fixed noise.

**Definition 1.1 (The source parameters and polar pair).**

The source parameters, canonical purification, source noise, right partial trace, and polar encoder are defined by Eqs. 18–23 and S60 of Li and Jiang, arXiv:2609.00778v1.

*Formalization.* `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda1`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda4`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda5`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda2`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.lambda3`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.canonicalPurification`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourcePi`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceQ`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceD`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceB`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceE`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.rightTrace`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceNoise`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourceC`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.sourcePolar`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.matrixAction`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.TraceNonincreasing`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.inputFirstChoi`, `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.entanglementFidelity`, and `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.claim`.

*Citation.* Li and Jiang, arXiv:2609.00778v1, Eqs. 18–23 and supplement S60.

*Commentary.*

The definitions retain the full universal fixed-noise dominance assertion over dimensions, noise parameters, unit auxiliary vectors, and completely positive trace-nonincreasing encoder and decoder pairs with input-first encoder Choi rank at most one. Fidelity is the unnormalized canonical-purification overlap.

**Theorem 1.2 (A feasible qubit pair strictly improves the source polar pair).**

The full fixed-noise polar-pair dominance assertion is false. At `d = 2`, `p = 9/13`, and `chi = ket(0)`, the competitor columns are `(24 ket(00) - 7 ket(11))/25` and `ket(10)`, with the same actual right partial trace decoder. The source and competitor fidelities differ by

`7 (10279 - 3250 sqrt(10)) / 260000 > 0`.

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.result`.

*Source.* Repository-derived.

*Commentary.*

This refutes exact dominance at the universal fixed-noise pair level. It does not determine a global rank-one optimum and does not refute the source's quadratic asymptotic coefficient or high-rank theorem.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
