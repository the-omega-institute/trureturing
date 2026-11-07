# JenzerPermutedRotorLoop

## Abstract

Permuted rotor loops obey the subset formula without the star condition.

**Theorem 1.1 (Permuted rotor loops without the star condition).**

$$\forall (V : Type), [\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(\mathbb{R}, V\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall (q : \operatorname{QuadraticForm}\left(\mathbb{R}, V\right)), ((q).\operatorname{Nondegenerate}) \Rightarrow (\forall (k : \mathbb{N}), (1 \le (k)) \Rightarrow (\forall (B : (\operatorname{Fin}\left(k\right) \to \operatorname{CliffordAlgebra}\left(q\right))), (\operatorname{AnticommutingUnitFamily}\left(q, k, B\right)) \Rightarrow (\forall (theta : (\operatorname{Fin}\left(k\right) \to \mathbb{R})), \forall (tau : \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(k\right)\right)), \operatorname{scalarProjection}\left(q, \operatorname{loop}\left(B, theta, tau\right)\right) = (\sum_{S \in ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))).\operatorname{powerset}} ((((\operatorname{eta}\left((S).\operatorname{card}\right)) \cdot (((-(1) : \mathbb{R}))^{\operatorname{inversionCount}\left(tau, S\right)})) \cdot (\prod_{i \in S} (\operatorname{w}\left(theta, i\right)))) \cdot (\prod_{i \in ((\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))) \setminus (S)} ((1) - (\operatorname{w}\left(theta, i\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/JenzerPermutedRotorLoop.result` (`✓ std3`). ∎

*Resolves.* `Problems/jen2610` (proved) by `D5/S3/QuadraticForms/JenzerPermutedRotorLoop.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jen2610","declaration_gid":"D5/S3/QuadraticForms/JenzerPermutedRotorLoop.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nik Jenzer (2026). *Star-Ordered Rotor Loops in Clifford Algebras*. DOI: [10.48550/arXiv.2610.21593](https://doi.org/10.48550/arXiv.2610.21593). URL: <https://arxiv.org/abs/2610.21593v1>.

*Commentary.*

Anticommuting conjugations remove all off-diagonal scalar terms except possible odd full support. The top coefficient of the balanced exterior word cancels that aggregate. The remaining diagonal terms give the full subset formula for every source signature, angle and permutation. No nonzero sine or cosine assumption is used.

## References

- Truth anchor: `D5/S3/QuadraticForms/JenzerPermutedRotorLoop.result`
- Dependency: [D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra](JenzerPermutedRotorLoopAlgebra.md)
- Dependency: [D5/S3/QuadraticForms/JenzerPermutedRotorLoopWords](JenzerPermutedRotorLoopWords.md)
