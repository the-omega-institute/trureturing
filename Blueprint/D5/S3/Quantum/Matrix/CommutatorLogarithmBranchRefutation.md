# An obstruction to exponential-dependent logarithm branches

## Abstract

The exponential of a complex matrix does not determine its halved commutator operator.

**Definition 1.1 (Recovering the commutator from the exponential).**

$$\operatorname{claim} = (\exists (\Lambda L: (\operatorname{Matrix}\left(\operatorname{Fin}\left((2: \mathbb{N})\right), \operatorname{Fin}\left((2: \mathbb{N})\right), \mathbb{C}\right)) \to ((\operatorname{Matrix}\left(\operatorname{Fin}\left((2: \mathbb{N})\right), \operatorname{Fin}\left((2: \mathbb{N})\right), \mathbb{C}\right)) \to_{\ell}[\mathbb{C}] (\operatorname{Matrix}\left(\operatorname{Fin}\left((2: \mathbb{N})\right), \operatorname{Fin}\left((2: \mathbb{N})\right), \mathbb{C}\right)))), (\exists (\Lambda R: (\operatorname{Matrix}\left(\operatorname{Fin}\left((2: \mathbb{N})\right), \operatorname{Fin}\left((2: \mathbb{N})\right), \mathbb{C}\right)) \to ((\operatorname{Matrix}\left(\operatorname{Fin}\left((2: \mathbb{N})\right), \operatorname{Fin}\left((2: \mathbb{N})\right), \mathbb{C}\right)) \to_{\ell}[\mathbb{C}] (\operatorname{Matrix}\left(\operatorname{Fin}\left((2: \mathbb{N})\right), \operatorname{Fin}\left((2: \mathbb{N})\right), \mathbb{C}\right)))), (\forall (G: \operatorname{Matrix}\left(\operatorname{Fin}\left((2: \mathbb{N})\right), \operatorname{Fin}\left((2: \mathbb{N})\right), \mathbb{C}\right)), ((\frac{(1: \mathbb{C})}{(2: \mathbb{C})}) \cdot ((\operatorname{LinearMap.mulLeft}\left(\mathbb{C}, G\right)) - (\operatorname{LinearMap.mulRight}\left(\mathbb{C}, G\right))) = (\frac{(1: \mathbb{C})}{(2: \mathbb{C})}) \cdot ((\Lambda L\left((\operatorname{NormedSpace.exp}\left(G\right))\right)) - (\Lambda R\left((\operatorname{NormedSpace.exp}\left(G\right))\right)))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.claim` (`✓ std3`).

*Citation.* Michal Bathory (2025). *Commutator calculus and symbolic differentiation of matrix functions*. DOI: [10.1137/25M1760209](https://doi.org/10.1137/25M1760209). URL: <https://arxiv.org/abs/2505.07987v3>.

*Commentary.*

For a complex two-by-two matrix G, LinearMap.mulLeft ℂ G sends X to GX, and LinearMap.mulRight ℂ G sends X to XG. Half their difference is the halved commutator operator. The claim asks for two functions ΛL and ΛR from complex two-by-two matrices to complex-linear endomorphisms of that matrix space, whose half-difference at exp G equals this operator for every G. Both functions depend only on the exponential, and no further conditions are imposed on them.

Bathory defines the multiplication and halved commutator operators in equation (1.1), cc_arxiv_1_.tex line 38. Lemma 3.4 states the logarithm identity (3.42) for real symmetric matrices at lines 377–387, with the identity itself at line 385. Conjecture 3.7 at lines 505–507 proposes extending these identities to all complex square matrices. The claim is the dimension-two reading of (3.42) in which the generalized logarithm operators are determined by A = exp G.

**Theorem 1.2 (Equal exponentials with different commutators).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bathory-2025-commutator-logarithm-branch-refutation` (refuted) by `D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bathory-2025-commutator-logarithm-branch-refutation","declaration_gid":"D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michal Bathory (2025). *Commutator calculus and symbolic differentiation of matrix functions*. DOI: [10.1137/25M1760209](https://doi.org/10.1137/25M1760209). URL: <https://arxiv.org/abs/2505.07987v3>.

*Commentary.*

Suppose such functions ΛL and ΛR exist. The diagonal matrix diag(0, 2πi) has exponential equal to the identity: exponentiating a diagonal matrix exponentiates its diagonal entries, and exp 0 = 1 and exp(2πi) = 1. Here π is the real number Real.pi included in ℂ, and i is Complex.I.

Apply the asserted identity first to the zero matrix and then to diag(0, 2πi). The exponential of the zero matrix is also the identity. Thus both right sides are the same linear map, namely half of ΛL(1) − ΛR(1), so the two halved commutator operators must agree.

Evaluate this equality on Matrix.single 0 1 1 and take its entry at row 0, column 1. This matrix has complex entry one at that position and zero elsewhere. The zero matrix gives entry zero. Left multiplication by diag(0, 2πi) gives entry zero, while right multiplication gives entry 2πi. Subtracting and multiplying by the complex scalar one half therefore gives −πi. Equality would force 0 = −πi, contradicting π > 0 and i ≠ 0. Hence no such pair of functions exists. The obstruction concerns the exponential-dependent complex extension; the real symmetric identity retains its stated scope.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/CommutatorLogarithmBranchRefutation.result`
