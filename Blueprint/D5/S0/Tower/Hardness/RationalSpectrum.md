# Rational-Tower Hardness Spectrum

## Abstract

The rational-tower hardness spectrum has the sharp Hurwitz extremum attained by the golden tail.

**Theorem 1.1 (Definition 4.1 and the sharp Hurwitz extremum).**

$$(\forall X \in Type, beta \in X \to R,\; \operatorname{hardnessSpectrum}\left(beta\right) = \operatorname{range}\left(beta\right)) \land \left((\forall X \in Type, beta \in X \to R, x \in X,\; \operatorname{BadlyApproximable}\left(beta, x\right) \Leftrightarrow 0 < \operatorname{apply}\left(beta, x\right)) \land \left(\operatorname{IsLeast}\left(\operatorname{upperBounds}\left(\operatorname{hardnessSpectrum}\left(rationalHardness\right)\right), \frac{1}{\operatorname{sqrt}\left(5\right)}\right) \land \operatorname{rationalHardness}\left(goldenRatioPoint\right) = \frac{1}{\operatorname{sqrt}\left(5\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Hardness/RationalSpectrum.rational_tower_hardness_spectrum` (`✓ std3`). ∎

*Citation.* Adolf Hurwitz (1891). *Ueber die angenaeherte Darstellung der Irrationalzahlen durch rationale Brueche*. DOI: [10.1007/BF01206656](https://doi.org/10.1007/BF01206656).

*Commentary.*

For any point type X and hardness function beta, the hardness spectrum is the range of beta, and BadlyApproximable(beta,x) holds exactly when beta(x) is positive. These are the first two, definitional, clauses of the packaged declaration.

A rational-tower point is represented in normalized regular-continued-fraction coordinates by positive partial quotients and the exact forward- and backward-tail recurrences. Its approximation coefficient is q_n^2 times the convergent error, and rationalHardness is its filter liminf.

The sharp proof is not assumed by the point structure. If the center coefficient exceeds 1/sqrt(5), a factorization using sqrt(5)^2=5 forces one adjacent coefficient below that constant. Every block of three indices therefore supplies a hit arbitrarily far out, yielding the universal liminf upper bound.

The all-one continued-fraction tail is the golden-ratio class. Its two normalized tails equal the inverse golden ratio, so every coefficient is exactly 1/sqrt(5). Consequently the set of upper bounds of the hardness spectrum has 1/sqrt(5) as its least element, and the golden point attains that value. This is the order-correct meaning of the source phrase 'bottom of the supremum structure'.

The D5 formal library was searched first. Its golden-ratio lower bound and Fibonacci approximation limit cover only the extremal point, not the universal Hurwitz bound. Pinned Mathlib, Loogle, LeanSearch, and GitHub Lean code supplied Dirichlet and Legendre results but no exact sharp theorem, so the local proof fills the missing universal layer.

## References

- Truth anchor: `D5/S0/Tower/Hardness/RationalSpectrum.rational_tower_hardness_spectrum`
