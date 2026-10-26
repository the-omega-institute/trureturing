# A positive map reflecting positive contractions

## Abstract

Bourin's Question 1 has a negative answer for the Frobenius norm and the square-root function.

**Definition 1.1 (Question 1).**

$$\operatorname{claim} = (\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (Phi: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) \to_{l}[\mathbb{C}] \operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \mathbb{C}\right)), ((\forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((0 \le X) \Rightarrow (0 \le Phi\left(X\right)))) \Rightarrow ((Phi^{-1}(\{X: \operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \mathbb{C}\right) | ((0 \le X) \land (X \le 1))\}) \subseteq \{X: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) | ((0 \le X) \land (X \le 1))\}) \Rightarrow (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((0 \le M) \Rightarrow (\forall (N: \operatorname{D5.S3.Quantum.Schatten}.\operatorname{UINorm}\left(k\right)), (\forall (f: \mathbb{R} \to \mathbb{R}), ((\operatorname{ConcaveOn}\left(\mathbb{R}, \operatorname{Set}.\operatorname{Ici}\left(0\right), f\right)) \Rightarrow ((\forall (x: \mathbb{R}), ((0 \le x) \Rightarrow (0 \le f\left(x\right)))) \Rightarrow (N.N\left(\operatorname{cfc}\left(f, Phi\left(M\right)\right)\right) \le N.N\left(Phi\left(\operatorname{cfc}\left(f, M\right)\right)\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.claim` (`✓ std3`).

*Citation.* Jean-Christophe Bourin (2008). *Matrix subadditivity inequalities and block-matrices*. DOI: [10.1142/S0129167X09005509](https://doi.org/10.1142/S0129167X09005509). URL: <https://arxiv.org/abs/0805.1954v1>.

*Commentary.*

Bourin, arXiv:0805.1954v1, p. 3, Question 1: "Let Φ : M_n → M_k be a positive linear map between the algebras of matrices of size n and k and let F_n and F_k be the sets of non-expansive, positive operators in M_n and M_k respectively. Does Φ⁻¹(F_k) ⊂ F_n imply ‖f ∘ Φ(M)‖ ≤ ‖Φ ∘ f(M)‖ for all M ≥ 0, all symmetric norms and all non-negative concave functions on the positive half line?"

The matrices are complex, and 1 is the identity matrix. The order is the Loewner order. Non-expansive positive matrices are exactly the matrices X with 0 ≤ X and X ≤ 1; the preimage is taken in the entire matrix algebra. The type D5.S3.Quantum.Schatten.UINorm contains the norm laws and invariance under left and right multiplication by unitary matrices. Its field N evaluates the norm. The real function f is concave and nonnegative on [0,∞); cfc applies it by continuous functional calculus.

**Theorem 1.2 (The Frobenius inequality fails).**

$$\neg (\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (Phi: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) \to_{l}[\mathbb{C}] \operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \mathbb{C}\right)), ((\forall (X: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((0 \le X) \Rightarrow (0 \le Phi\left(X\right)))) \Rightarrow ((Phi^{-1}(\{X: \operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \mathbb{C}\right) | ((0 \le X) \land (X \le 1))\}) \subseteq \{X: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) | ((0 \le X) \land (X \le 1))\}) \Rightarrow (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), ((0 \le M) \Rightarrow (\forall (N: \operatorname{D5.S3.Quantum.Schatten}.\operatorname{UINorm}\left(k\right)), (\forall (f: \mathbb{R} \to \mathbb{R}), ((\operatorname{ConcaveOn}\left(\mathbb{R}, \operatorname{Set}.\operatorname{Ici}\left(0\right), f\right)) \Rightarrow ((\forall (x: \mathbb{R}), ((0 \le x) \Rightarrow (0 \le f\left(x\right)))) \Rightarrow (N.N\left(\operatorname{cfc}\left(f, Phi\left(M\right)\right)\right) \le N.N\left(Phi\left(\operatorname{cfc}\left(f, M\right)\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bourin-2008-matrix-subadditivity-question-1` (refuted) by `D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bourin-2008-matrix-subadditivity-question-1","declaration_gid":"D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jean-Christophe Bourin (2008). *Matrix subadditivity inequalities and block-matrices*. DOI: [10.1142/S0129167X09005509](https://doi.org/10.1142/S0129167X09005509). URL: <https://arxiv.org/abs/0805.1954v1>.

*Commentary.*

Take n = 1, k = 2, Φ(X) = Matrix.diagonal ![X 0 0, X 0 0 / 4], M = 1 and f = Real.sqrt. Positivity of the first diagonal entry reflects positivity, and the upper bound on that entry reflects the upper bound by 1. The functional-calculus values are Matrix.diagonal ![1, 1/2] and Matrix.diagonal ![1, 1/4]. Their Frobenius norm squares are 5/4 and 17/16, respectively, contradicting the proposed inequality.

The Frobenius norm laws come from Matrix's Frobenius norm. Its two-sided unitary invariance follows from invariance of RHLinalg.frobSq and its equality with the squared Frobenius norm. The first block suffices to reflect positive contractions, whereas the square root increases the second weight from 1/4 to 1/2. This argument concerns Question 1; it makes no assertion about Question 2 or a restriction to the operator norm.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.result`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../GNSMatrix.md)
- Dependency: [D5/S3/Quantum/Matrix/CommutatorGap](../Matrix/CommutatorGap.md)
- Dependency: [D5/S3/Quantum/Schatten/UnitarilyInvariantNorm](UnitarilyInvariantNorm.md)
