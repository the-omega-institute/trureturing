---
bibkey: beccaria2012staggered
authors: Matteo Beccaria; Christian Hagendorf
year: 2012
title: "A staggered fermion chain with supersymmetry on open intervals"
doi: 10.1088/1751-8113/45/36/365201
url: https://arxiv.org/abs/1206.4194v2
claim: "Section 3.2.3 conjectures the endpoint-density identity for staggering II on every open M1 chain with N = 3n."
strata_touched:
  - D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner
  - D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel
  - D5/S3/Quantum/SpinChains/StaggeredM1EndpointDensity
license: citation-only
triage: anchor
---

# A staggered fermion chain with supersymmetry on open intervals

M. Beccaria and C. Hagendorf, J. Phys. A 45 (2012) 365201,
arXiv:1206.4194v2. Section 2.1, printed page 2, states the canonical
anticommutation relations
$\{c_i,c_j\}=\{c_i^\dagger,c_j^\dagger\}=0$ and
$\{c_i,c_j^\dagger\}=\delta_{ij}$.

Section 2.1, printed page 3, specifies:

> nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.

> We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.

The hard-core configurations use the existing admissible-word predicate `AdmissibleCount.Adm`; `ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true` identifies it with the stated nearest-neighbour exclusion.

The dressed annihilator is $d_j=P_{j-1}c_jP_{j+1}$, with
$P_j=1-c_j^\dagger c_j$. In the hard-core realization,
`HardCoreModel.annihilator_number` identifies $c_j^\dagger c_j$
with the occupation diagonal, including zero at inaccessible sites. The supercharge is
$Q=\sum_{j=1}^N\lambda_jd_j$ and the Hamiltonian is
$H=QQ^\dagger+Q^\dagger Q$. Equation (2) gives staggering II as
$\lambda_{3p-2}=y$, $\lambda_{3p-1}=y$, $\lambda_{3p}=1$.

Section 3.2.3, printed page 13, states:

> As similar pattern is found by probing if a particle is present on the last site. The data is consistent with $\rho_n^{(N)}(y) = y^{-2}\rho_n^{(1)}(y)$ for finite $n\leq 8$. We conjecture this to hold for arbitrary system sizes.

Here $N=3n$, $n\geq1$, and the density is the normalized expectation of
site occupation in the zero-energy ground state. The formal claim quantifies
over every nonzero zero-energy state for real $y\ne0$. It therefore contains
the stated ground-state relation without using existence or uniqueness.
The source's cohomology statement about the unique ground state cites its
reference [14]; that statement is not a premise of the endpoint argument.

## Verified locator

- DOI: https://doi.org/10.1088/1751-8113/45/36/365201
- Source: https://arxiv.org/abs/1206.4194v2
