---
bibkey: sarkar2026mubdegreefour
authors: Shreyhaan Sarkar
year: 2026
title: Degree-Four Vector-Coordinate SoS Cannot Detect the MUB Upper Bound
doi: 10.48550/arXiv.2606.13903
claim: Degree-four vector-coordinate SoS admits pseudoexpectations beyond the MUB bound, while centered rank-one projector coordinates yield a degree-four Gram certificate for the general bound m <= d + 1.
strata_touched:
  - D5/S3/Quantum/Tomography/MUBHadamardCompatibility
  - D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes
  - D5/S3/Quantum/Tomography/PurityPythagorasDecomposition
  - D5/S3/QuantumBounds/Designs/CollisionConservation
license: citation-only
triage: anchor
---

# Degree-Four Vector-Coordinate SoS Cannot Detect the MUB Upper Bound

Sarkar studies degree-four sum-of-squares relaxations for mutually unbiased
bases. The result separates two polynomial encodings of the same geometry.

In vector coordinates, the paper constructs a degree-four pseudoexpectation
satisfying the MUB constraints for arbitrary numbers of bases. That relaxation
therefore cannot certify the universal upper bound `m <= d + 1`.

In centered rank-one projector coordinates, write

```math
Q_{a,i}=P_{a,i}-I/d,
```

and vectorize the trace-zero Hermitian projectors as `q_{a,i}`. The within-basis
and cross-basis Hilbert--Schmidt overlaps become quadratic Gram constraints.
For the frame operator

```math
S=\sum_{a,i} q_{a,i}q_{a,i}^{T},
```

the degree-four trace-rank identity

```math
D\operatorname{Tr}(S^2)-\operatorname{Tr}(S)^2
 = \sum_{u<v}(S_{uu}-S_{vv})^2
   + 2D\sum_{u<v}S_{uv}^2
```

is an explicit sum of squares, where `D=d^2-1`. Reducing the traces by the MUB
Gram relations gives

```math
\operatorname{Tr}(S)=m(d-1),
\qquad
\operatorname{Tr}(S^2)=m(d-1),
```

and hence the nonnegative polynomial

```math
m(d-1)^2(d+1-m).
```

For positive `m` and `d>1`, this proves `m <= d+1` inside degree-four
projector-coordinate SoS.

## Exact scope for dimension six

At `d=6`, the certificate is proportional to

```math
25m(7-m).
```

It is tight at seven bases and excludes eight or more. At four bases it is
strictly positive, so it supplies no contradiction for the open fourth-basis
problem. Reusing this identity alone cannot exclude `m=4`.

Its value for trureturing is coordinate selection. The repository's
`centeredProjector`, `centeredContextPlane`, tomography, purity decomposition,
and collision identities already live on the coordinate system in which the
proof system sees the correct trace-zero geometry. Branch-specific order-six
certificates should therefore be expressed in these centered projector or
relative-Hadamard Gram variables, rather than returning to the weaker raw
vector-coordinate degree-four relaxation.

## Consequence for the research lane

The next useful certificate must introduce information absent from the general
rank bound. Candidate sources include:

- exact equations defining a classified order-six Hadamard branch;
- compatibility equations for two additional Hadamard matrices in a common
  left gauge;
- branch-specific low-rank, resultant, interval, or higher-degree SoS
  consequences;
- exact separation functionals on the centered projector Gram matrix.

The paper rules out one proof encoding at one degree. It does not rule out
higher-degree vector SoS, projector-coordinate hierarchies, exact semidefinite
certificates, or algebraic branch elimination.

## Verified locators

- arXiv: https://arxiv.org/abs/2606.13903
- arXiv DOI: https://doi.org/10.48550/arXiv.2606.13903
- projector-coordinate certificate: Section 8 of arXiv:2606.13903v1
