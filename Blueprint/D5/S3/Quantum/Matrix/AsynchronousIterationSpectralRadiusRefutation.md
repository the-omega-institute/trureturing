# Stable synchronous iteration can become unstable with unit remote delays

## Abstract

A real matrix of spectral radius one half has a unit-delay asynchronous iteration of spectral radius at least five quarters.

**Definition 1.1 (The matrix acting on the stacked history).**

$$\forall (\ell: \mathbb{N}), (\forall (n: (\operatorname{Fin}\left(\ell\right)) \to (\mathbb{N})), (\forall (M: \operatorname{Matrix}\left(\operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \mathbb{R}\right)), (\forall (\delta: (\operatorname{Fin}\left(\ell\right)) \to ((\operatorname{Fin}\left(\ell\right)) \to (\mathbb{N}))), (\forall (k: \mathbb{N}), ((\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.asyncMatrix}\left(M, \delta, k\right): \operatorname{Matrix}\left(\operatorname{Fin}\left((k) + ((1: \mathbb{N}))\right) \times \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \operatorname{Fin}\left((k) + ((1: \mathbb{N}))\right) \times \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \mathbb{R}\right)) = (\lambda (rp: \operatorname{Fin}\left((k) + ((1: \mathbb{N}))\right) \times \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right)) \mapsto (\lambda (sq: \operatorname{Fin}\left((k) + ((1: \mathbb{N}))\right) \times \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right)) \mapsto (\operatorname{ite}\left((\operatorname{Fin.val}\left((rp).1\right) = (0: \mathbb{N})), \operatorname{ite}\left((\operatorname{Fin.val}\left((sq).1\right) = \delta\left(\operatorname{Sigma.fst}\left((sq).2\right), \operatorname{Sigma.fst}\left((rp).2\right)\right)), M\left((rp).2, (sq).2\right), (0: \mathbb{R})\right), \operatorname{ite}\left((((\operatorname{Fin.val}\left((sq).1\right)) + ((1: \mathbb{N})) = \operatorname{Fin.val}\left((rp).1\right)) \land ((sq).2 = (rp).2)), (1: \mathbb{R}), (0: \mathbb{R})\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.asyncMatrix` (`✓ std3`).

*Citation.* Sinan G. Aksoy; Ryan Bennink; Yuzhou Chen; José Frías; Yulia R. Gel; Bill Kay; Uwe Naumann; Carlos Ortiz Marrero; Anthony V. Petyuk; Sandip Roy; Ignacio Segovia-Dominguez; Nate Veldt; Stephen J. Young (2023). *Seven open problems in applied combinatorics*. DOI: [10.4310/JOC.2023.v14.n4.a8](https://doi.org/10.4310/JOC.2023.v14.n4.a8). URL: <https://arxiv.org/abs/2303.11464v1>.

*Commentary.*

The block index type Vtx n is the dependent sum of Fin (n i) over i in Fin ℓ. A history coordinate is a pair consisting of a slot and a block coordinate; slot zero is the newest iterate. At slot zero, the entry M p q is taken from the slot whose natural index is δ j i, where i is the block of p and j is the block of q. Every later slot copies the preceding slot at the same coordinate. Fin.val explicitly converts a slot to its natural index. This is the operator M^(δ,k) of Sections/ratfish.tex, lines 48–49, when k bounds all delays. The definition itself accepts every natural k and every delay array; a delay greater than k contributes no entry.

**Definition 1.2 (The complex spectral radius of a real matrix).**

$$\forall (\iota: \operatorname{Type}*), ([\operatorname{Fintype}\left(\iota\right)] [\operatorname{DecidableEq}\left(\iota\right)], (\forall (M: \operatorname{Matrix}\left(\iota, \iota, \mathbb{R}\right)), ((\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.radius}\left(M\right): \operatorname{ENNReal}) = \operatorname{spectralRadius}\left(\mathbb{C}, \operatorname{Matrix.map}\left(M, \operatorname{DFunLike.coe}\left(\operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.radius` (`✓ std3`).

*Citation.* Sinan G. Aksoy; Ryan Bennink; Yuzhou Chen; José Frías; Yulia R. Gel; Bill Kay; Uwe Naumann; Carlos Ortiz Marrero; Anthony V. Petyuk; Sandip Roy; Ignacio Segovia-Dominguez; Nate Veldt; Stephen J. Young (2023). *Seven open problems in applied combinatorics*. DOI: [10.4310/JOC.2023.v14.n4.a8](https://doi.org/10.4310/JOC.2023.v14.n4.a8). URL: <https://arxiv.org/abs/2303.11464v1>.

*Commentary.*

Map every real matrix entry into the complex numbers and take the complex spectral radius, with values in the extended nonnegative reals. The map is the function underlying algebraMap ℝ ℂ. This expresses the spectral radius used for real iteration matrices in Sections/ratfish.tex, lines 48–49.

**Definition 1.3 (The block sizes, delays and original radius).**

$$\forall (\ell: \mathbb{N}), (\forall (n: (\operatorname{Fin}\left(\ell\right)) \to (\mathbb{N})), (\forall (k: \mathbb{N}), (\forall (M: \operatorname{Matrix}\left(\operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \mathbb{R}\right)), (\forall (\delta: (\operatorname{Fin}\left(\ell\right)) \to ((\operatorname{Fin}\left(\ell\right)) \to (\mathbb{N}))), (\forall (lambda: \mathbb{R}), (\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.Admissible}\left(\ell, n, k, M, \delta, lambda\right) = \left((\forall (i: \operatorname{Fin}\left(\ell\right)), ((0: \mathbb{N}) < n\left(i\right))) \land ((\forall (i: \operatorname{Fin}\left(\ell\right)), (\delta\left(i, i\right) = (0: \mathbb{N}))) \land ((\forall (i: \operatorname{Fin}\left(\ell\right)), (\forall (j: \operatorname{Fin}\left(\ell\right)), ((i \ne j) \to (((1: \mathbb{N}) \le \delta\left(i, j\right)) \land (\delta\left(i, j\right) \le k))))) \land (((0: \mathbb{R}) < lambda) \land ((lambda < (1: \mathbb{R})) \land (\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.radius}\left(M\right) = \operatorname{ENNReal.ofReal}\left(lambda\right))))))\right)))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sinan G. Aksoy; Ryan Bennink; Yuzhou Chen; José Frías; Yulia R. Gel; Bill Kay; Uwe Naumann; Carlos Ortiz Marrero; Anthony V. Petyuk; Sandip Roy; Ignacio Segovia-Dominguez; Nate Veldt; Stephen J. Young (2023). *Seven open problems in applied combinatorics*. DOI: [10.4310/JOC.2023.v14.n4.a8](https://doi.org/10.4310/JOC.2023.v14.n4.a8). URL: <https://arxiv.org/abs/2303.11464v1>.

*Commentary.*

Each block is nonempty, each local delay is zero, and each remote delay lies between one and k, inclusive. The real number lambda lies strictly between zero and one and equals the original spectral radius after inclusion into the extended nonnegative reals. These conditions select positive remote delays from the patterns considered in Sections/ratfish.tex, line 76. The displayed implications impose bounds only on distinct block indices.

**Definition 1.4 (The proposed power bound).**

$$\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.Q1} = (\forall (\ell: \mathbb{N}), (\forall (n: (\operatorname{Fin}\left(\ell\right)) \to (\mathbb{N})), (\forall (k: \mathbb{N}), (\forall (M: \operatorname{Matrix}\left(\operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \mathbb{R}\right)), (\forall (\delta: (\operatorname{Fin}\left(\ell\right)) \to ((\operatorname{Fin}\left(\ell\right)) \to (\mathbb{N}))), (\forall (lambda: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.Admissible}\left(\ell, n, k, M, \delta, lambda\right)) \to (\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.radius}\left(\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.asyncMatrix}\left(M, \delta, k\right)\right) \le \operatorname{ENNReal.ofReal}\left((lambda)^{(\frac{(1: \mathbb{R})}{((\operatorname{Nat.cast}\left(k\right): \mathbb{R})) + ((1: \mathbb{R}))})}\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.Q1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sinan G. Aksoy; Ryan Bennink; Yuzhou Chen; José Frías; Yulia R. Gel; Bill Kay; Uwe Naumann; Carlos Ortiz Marrero; Anthony V. Petyuk; Sandip Roy; Ignacio Segovia-Dominguez; Nate Veldt; Stephen J. Young (2023). *Seven open problems in applied combinatorics*. DOI: [10.4310/JOC.2023.v14.n4.a8](https://doi.org/10.4310/JOC.2023.v14.n4.a8). URL: <https://arxiv.org/abs/2303.11464v1>.

*Commentary.*

For every choice of block sizes, matrix and admissible delays, the delayed radius would be at most lambda to the real power 1/(k+1). The natural delay bound k is explicitly cast to a real number before adding the real one in the denominator. This is the first question of Sections/ratfish.tex, lines 75–77, restricted to the stated admissible data.

**Definition 1.5 (A uniform bound below one).**

$$\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.Q2} = (\exists (f: (\mathbb{R}) \to ((\mathbb{N}) \to (\mathbb{R}))), ((\forall (lambda: \mathbb{R}), (\forall (k: \mathbb{N}), (((0: \mathbb{R}) < lambda) \to ((lambda < (1: \mathbb{R})) \to (((0: \mathbb{R}) < f\left(lambda, k\right)) \land (f\left(lambda, k\right) < (1: \mathbb{R}))))))) \land (\forall (\ell: \mathbb{N}), (\forall (n: (\operatorname{Fin}\left(\ell\right)) \to (\mathbb{N})), (\forall (k: \mathbb{N}), (\forall (M: \operatorname{Matrix}\left(\operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \operatorname{D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs.Vtx}\left(n\right), \mathbb{R}\right)), (\forall (\delta: (\operatorname{Fin}\left(\ell\right)) \to ((\operatorname{Fin}\left(\ell\right)) \to (\mathbb{N}))), (\forall (lambda: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.Admissible}\left(\ell, n, k, M, \delta, lambda\right)) \to (\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.radius}\left(\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.asyncMatrix}\left(M, \delta, k\right)\right) \le \operatorname{ENNReal.ofReal}\left(f\left(lambda, k\right)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.Q2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sinan G. Aksoy; Ryan Bennink; Yuzhou Chen; José Frías; Yulia R. Gel; Bill Kay; Uwe Naumann; Carlos Ortiz Marrero; Anthony V. Petyuk; Sandip Roy; Ignacio Segovia-Dominguez; Nate Veldt; Stephen J. Young (2023). *Seven open problems in applied combinatorics*. DOI: [10.4310/JOC.2023.v14.n4.a8](https://doi.org/10.4310/JOC.2023.v14.n4.a8). URL: <https://arxiv.org/abs/2303.11464v1>.

*Commentary.*

One real-valued function f of lambda and the natural delay bound k would bound every admissible delayed radius. For every k and every lambda strictly between zero and one, its value must also lie strictly between zero and one. The function is defined on all real lambda, with no range condition outside this interval. On the interval this states the second question of Sections/ratfish.tex, lines 75–77, for the admissible data.

**Definition 1.6 (At least one proposed bound holds).**

$$\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.claim} = \left((\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.Q1}) \lor (\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.Q2})\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sinan G. Aksoy; Ryan Bennink; Yuzhou Chen; José Frías; Yulia R. Gel; Bill Kay; Uwe Naumann; Carlos Ortiz Marrero; Anthony V. Petyuk; Sandip Roy; Ignacio Segovia-Dominguez; Nate Veldt; Stephen J. Young (2023). *Seven open problems in applied combinatorics*. DOI: [10.4310/JOC.2023.v14.n4.a8](https://doi.org/10.4310/JOC.2023.v14.n4.a8). URL: <https://arxiv.org/abs/2303.11464v1>.

*Commentary.*

The assertion is the disjunction of the power bound and the existence of a uniform bound below one. Both alternatives quantify over arbitrary block arrays and the same admissible delay patterns. Positive remote delays and positive lambda suffice to test both questions in Sections/ratfish.tex, lines 75–77.

**Theorem 1.7 (Both bounds fail for two scalar blocks).**

$$\neg (\operatorname{D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/aksoy-et-al-2023-asynchronous-iteration-spectral-radius-refutation` (refuted) by `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"aksoy-et-al-2023-asynchronous-iteration-spectral-radius-refutation","declaration_gid":"D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sinan G. Aksoy; Ryan Bennink; Yuzhou Chen; José Frías; Yulia R. Gel; Bill Kay; Uwe Naumann; Carlos Ortiz Marrero; Anthony V. Petyuk; Sandip Roy; Ignacio Segovia-Dominguez; Nate Veldt; Stephen J. Young (2023). *Seven open problems in applied combinatorics*. DOI: [10.4310/JOC.2023.v14.n4.a8](https://doi.org/10.4310/JOC.2023.v14.n4.a8). URL: <https://arxiv.org/abs/2303.11464v1>.

*Commentary.*

Take two blocks of size one and the real matrix M with rows (7/4, 5/4) and (−5/4, −3/4). Let A be its entrywise complexification. Direct multiplication gives (A − (1/2)I)² = 0. If z belongs to the complex spectrum of A, spectral translation places z − 1/2 in the spectrum of A − (1/2)I. Squaring then places (z − 1/2)² in the spectrum of the zero matrix, which is {0}, so z = 1/2. Conversely, (1/2)I − A is nilpotent, hence is not a unit, so 1/2 belongs to the spectrum of A. The spectrum is therefore exactly {1/2}, and the supremum of the nonnegative complex norms gives radius M = 1/2.

Set k = 1 and take the delay array with rows (0,1) and (1,0), the natural adjacency matrix of the complete simple graph on Fin 2. Both block sizes are positive, the diagonal delays vanish, the remote delays equal one, and lambda = 1/2 lies in (0,1). Together with the radius calculation, these facts give all the admissibility conditions.

In the order consisting of the two newest coordinates followed by the two preceding coordinates, the asynchronous matrix B has rows (7/4,0,0,5/4), (0,−3/4,−5/4,0), (1,0,0,0) and (0,1,0,0). The complex vector v = (10,−5,8,−4) is nonzero because its first coordinate is 10. Multiplying by the complexification of B gives (25/2,−25/4,10,−5) = (5/4)v. Thus 5/4 lies in its complex spectrum. Its nonnegative norm, included into the extended nonnegative reals, is ENNReal.ofReal (5/4); the supremum defining the radius is at least this value.

If Q1 held, applying it to these admissible data would bound the delayed radius by ENNReal.ofReal ((1/2)^(1/(1+1))). The real power is at most one because its base lies in [0,1] and its exponent is nonnegative. Monotonicity of ENNReal.ofReal would then give ENNReal.ofReal (5/4) ≤ ENNReal.ofReal 1, a contradiction.

If Q2 held, its range condition would give 0 < f (1/2) 1 < 1. Applying its uniform bound to the same data and combining it with the delayed radius lower bound gives ENNReal.ofReal (5/4) ≤ ENNReal.ofReal (f (1/2) 1). Since f (1/2) 1 is nonnegative, this implies 5/4 ≤ f (1/2) 1, contradicting f (1/2) 1 < 1. Each alternative is false, so their disjunction is false.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.Admissible`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.Q1`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.Q2`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.asyncMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.radius`
- Truth anchor: `D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs](../../Combinatorics/Graph/MultipartiteCHS/Defs.md)
- Dependency: [D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree](../../Combinatorics/NonBacktracking/LaplacianGapMinDegree.md)
