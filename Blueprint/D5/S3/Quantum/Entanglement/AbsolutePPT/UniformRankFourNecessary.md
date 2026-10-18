# Uniform rank-four necessary inequality

## Abstract

An actual four-by-four product corner imposes a six-versus-ten mass inequality on every labelled APPT diagonal.

**Theorem 1.1 (First six versus last ten).**

$$\forall (m:Nat), \forall (n:Nat), ((4\leq m)\land (4\leq n))\Rightarrow \forall (e:Equiv\left((Fin\left(m\right)\times Fin\left(n\right)), Fin\left(m\cdot n\right)\right)), \forall (l:Fin\left(m\cdot n\right)\to \mathbb{R}), (APPT\left(diagonal\left((fun(p:(Fin\left(m\right)\times Fin\left(n\right)))\mapsto ofReal\left(l\left(e\left(p\right)\right)\right))\right)\right))\Rightarrow sumFirst\left(6, l\right)\leq sumLast\left(10, l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary.uniform_rank_four_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Roland Hildebrand (2007). *Positive partial transpose from spectra*. DOI: [10.1103/PhysRevA.76.052325](https://doi.org/10.1103/PhysRevA.76.052325). URL: <https://arxiv.org/abs/quant-ph/0502170>.

*Commentary.*

For arbitrary natural m,n at least four, an arbitrary equivalence e:(Fin m × Fin n) ≃ Fin(mn), and arbitrary real l:Fin(mn)→R, assume the actual complex diagonal diag(l composed with e) is APPT: its second-factor partial transpose is positive semidefinite after every global unitary on the full product. Then the sum of coordinates 0 through 5 is at most the sum of coordinates mn−10 through mn−1. The sumFirst and sumLast definitions use zero for out-of-range coordinates; the dimension hypotheses put all sixteen chosen coordinates in range. No ordering, nonnegativity, total mass, strict positivity or distinctness of l is required. Without ordering these are labelled coordinate sums, rather than a claim about largest and smallest eigenvalues.

Inside Fin 4 × Fin 4 let eta=sum_a |aa>. The partial transpose of |eta><eta| is the swap. Its six antisymmetric columns have eigenvalue −1, while its six symmetric off-diagonal and four diagonal columns have eigenvalue +1. The explicit pair rotation assigns the first six values to the former columns and the last ten to the latter. An injective corner and a finite-complement permutation extend this assignment to the whole product. APPT positivity tested at eta and partial_transpose_trace_duality give last10−first6≥0. Only product compression is commuted with partial transpose; an arbitrary labelling is used through global unitary conjugation, with no covariance assertion about that labelling. This is a fixed rank-four instance of the Hildebrand spectral-testing framework, not a generic-rank criterion or a sufficient condition for APPT. The published framework and the prior availability of private construction steps are not claimed as new discoveries.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary.uniform_rank_four_necessary`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
- Dependency: [D5/S3/Quantum/Matrix/PartialTransposeTrace](../../Matrix/PartialTransposeTrace.md)
