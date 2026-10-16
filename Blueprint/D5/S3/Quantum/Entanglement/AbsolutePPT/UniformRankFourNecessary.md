# Uniform rank-four necessity

## Abstract

A fixed rank-four product-local APPT test for arbitrary larger local dimensions.

**Definition 1.1 (Initial spectral mass).**

$$\forall (N:Nat), \forall (k:Nat), \forall (lambda:RealVector\left(N\right)), sumFirst\left(k, lambda\right)=\sum_{i:Fin\left(k\right)} ite\left(val\left(i\right)< N, lambda\left(val\left(i\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary.sumFirst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real vector lambda indexed by Fin N, sumFirst k lambda is the sum at indices 0 through k-1. An index outside Fin N contributes zero. All uses here have k<=N.

**Definition 1.2 (Terminal spectral mass).**

$$\forall (N:Nat), \forall (k:Nat), \forall (lambda:RealVector\left(N\right)), sumLast\left(k, lambda\right)=\sum_{i:Fin\left(k\right)} ite\left((N-k)+val\left(i\right)< N, lambda\left((N-k)+val\left(i\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary.sumLast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k<=N, sumLast k lambda is the sum at indices N-k through N-1. Its guarded Fin k expression uses index N-k+i and contributes zero if that index is out of range. The subtraction N-k is natural-number truncated subtraction.

**Theorem 1.3 (Six initial entries versus ten terminal entries).**

$$\forall (m:Nat), \forall (n:Nat), ((4\leq m)\land (4\leq n))\Rightarrow \forall (e:Equiv\left(Product\left(Fin\left(m\right), Fin\left(n\right)\right), Fin\left(multiply\left(m, n\right)\right)\right)), \forall (lambda:RealVector\left(multiply\left(m, n\right)\right)), APPT\left(diagonal\left(label\left(lambda, e\right)\right)\right)\Rightarrow sumFirst\left(6, lambda\right)\leq sumLast\left(10, lambda\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary.uniform_rank_four_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m,n>=4 and let e be any explicit equivalence from Fin m times Fin n to Fin(m*n). If the complex diagonal matrix with entry lambda(e(i,j)) is absolutely PPT, then sumFirst 6 lambda <= sumLast 10 lambda. This statement does not require sorting, nonnegativity, total mass one, strict positivity or distinct entries. In particular it applies to the ordered nonnegative spectrum of an APPT density matrix. It is uniform in both local dimensions at fixed rank four; it does not assert a theorem for arbitrary rank r.

Inside the actual product-local four-by-four corner, eta=sum_(i=0)^3 e_(i,i) is unnormalized. Gamma(eta eta*) is SWAP: it sends e_(i,j) to e_(j,i). Its six antisymmetric vectors have eigenvalue -1, its six symmetric pair vectors and four diagonal vectors have eigenvalue +1, and the actual finite complement has eigenvalue zero. For pair order 01,02,03,12,13,23, the rotation uses (e_(i,j)+e_(j,i))/sqrt(2) and (e_(i,j)-e_(j,i))/sqrt(2). Assign spectral indices 0 through 5 to the antisymmetric columns, N-10 through N-7 to the diagonals, and N-6 through N-1 to the symmetric columns. A permutation extends this injective assignment across the whole product space; the rotation extends by identity on the actual complement.

APPT applies to the composed global unitary. Compression to the genuine product corner commutes with partial transpose because the embedding is the product of two local Fin.castLE maps. Testing positivity against eta and applying PartialTransposeTrace.partial_transpose_trace_duality gives the terminal mass minus the initial mass, with coefficient one and no normalization factor. No arbitrary global packing is commuted through partial transpose. At N=28 this difference is exactly RankFourLength28Purity.L4.

To combine this inequality with the two rank-three boundary pencils for a physical state, use one sorted diagonalization and apply both necessity arguments to that same APPT diagonal spectrum. A theorem that separately provides an existential spectrum with the pencils does not identify it with the spectrum used here. The common-spectrum implication is the required connection to length-28 purity and to any subsequent dimension-transfer estimate.

Hildebrand's Positive partial transpose from spectra, Phys. Rev. A 76, 052325 (2007), supplies the spectral-test setting; the existing hildebrand2007pptspectra library note is the citation source. This fixed maximally entangled test is a necessary condition and is not an APPT sufficiency theorem or a priority claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary.sumFirst`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary.sumLast`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary.uniform_rank_four_necessary`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
- Dependency: [D5/S3/Quantum/Matrix/PartialTransposeTrace](../../Matrix/PartialTransposeTrace.md)
