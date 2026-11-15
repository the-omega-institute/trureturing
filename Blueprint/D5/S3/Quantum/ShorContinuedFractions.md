# Conditional Shor candidate membership

## Abstract

Conditional continued-fraction membership for actual modular phase estimation

Parameters is the actual padded modular-multiplication model: modulus N at least two, base coprime to N, and an independently chosen target width whose dimension holds the residues. The counting width n gives Q equal to two to the n. The true order r is positive and strictly smaller than N. The candidate algorithm takes only y.val, Q and N; s and r occur in the theorem's conditions, not as algorithm inputs.

**Theorem 1.1 (Reduced phase candidate).**

$$\forall c \in \mathit{Parameters},\; \forall n \in \mathit{Nat},\; \forall s \in \operatorname{Fin}\left(\operatorname{period}\left(c\right)\right),\; \forall y \in \operatorname{Fin}\left(2^{n}\right),\; \operatorname{modulus}\left(c\right)^{2} \le 2^{n} \Rightarrow \left(\operatorname{Nearest}\left(2^{n}, \frac{\operatorname{val}\left(s\right)}{\operatorname{period}\left(c\right)}, y\right) \Rightarrow \left(\operatorname{reduced}\left(\operatorname{val}\left(s\right), \operatorname{period}\left(c\right)\right) \in \operatorname{candidates}\left(\operatorname{val}\left(y\right), 2^{n}, \operatorname{modulus}\left(c\right)\right) \land \operatorname{Dvd}\left(\operatorname{den}\left(\operatorname{reduced}\left(\operatorname{val}\left(s\right), \operatorname{period}\left(c\right)\right)\right), \operatorname{period}\left(c\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ShorContinuedFractions.shor_nearest_candidate` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

For every c, n, hsize : N squared at most Q, s : Fin r and y : Fin Q, the hypothesis is the existing circular Nearest Q (s.val / r) y. The conclusion places the distinguished reduced s/r in candidates and says that this fraction's denominator divides r. Its denominator is exactly r divided by gcd(s.val,r), by the generic rational denominator formula. No assertion is made that every list entry divides the order.

Nearest means that some integer z makes the absolute difference s.val/r minus y.val/Q minus z at most 1/(2Q). Since s.val is below r, y.val is below Q and r is below N, the resolution N squared at most Q excludes nonzero z. This includes s equal to zero and either non-strict rounding tie. The reduced denominator is at most r and its square is strictly below Q, converting the non-strict grid error into the strict Legendre bound. Mathlib's existing Legendre theorem supplies a real-convergent index. The exact finite-list correspondence supplies membership, and the denominator bound passes the observable filter.

**Theorem 1.2 (Coprime true-order membership).**

$$\forall c \in \mathit{Parameters},\; \forall n \in \mathit{Nat},\; \forall s \in \operatorname{Fin}\left(\operatorname{period}\left(c\right)\right),\; \forall y \in \operatorname{Fin}\left(2^{n}\right),\; \operatorname{modulus}\left(c\right)^{2} \le 2^{n} \Rightarrow \left(\operatorname{Nearest}\left(2^{n}, \frac{\operatorname{val}\left(s\right)}{\operatorname{period}\left(c\right)}, y\right) \Rightarrow \left(\operatorname{Coprime}\left(\operatorname{val}\left(s\right), \operatorname{period}\left(c\right)\right) \Rightarrow \operatorname{period}\left(c\right) \in \operatorname{mapRatDen}\left(\operatorname{candidates}\left(\operatorname{val}\left(y\right), 2^{n}, \operatorname{modulus}\left(c\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/ShorContinuedFractions.shor_coprime_candidate` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

Under the same hypotheses and Nat.Coprime s.val r, the true order r belongs to the list obtained by mapping Rat.den over candidates. mapRatDen in the displayed statement denotes this map. The proof consumes reduced-phase membership and the exact denominator formula with gcd equal to one. This establishes existence within observable candidates; it does not provide an observable certified selector of the exact order.

The generic list admits zero and integer rationals, and the recovery theorem admits r equal to one and s equal to zero. Since N is at least two, the recovery resolution excludes n equal to zero; the existing QPE marginal still admits that counting width. No assumption r divides Q is used. A passing modular exponentiation test alone says that the tested exponent is a multiple of the order, by the pinned orderOf_dvd_iff_pow_eq_one theorem. Exactness needs additional information.

The supplied actual QPE uses the inverse final Fourier transform. Using the chapter's positive Fourier convention reflects the observed grid label through negation modulo Q, as described by the owning counting-marginal result. One must apply the nearest condition to the reflected label before using this recovery statement. The normalization and existing pointwise peak lower bound are unchanged.

This conditional deterministic theorem does not establish an aggregate quantum success probability, a random coprimality rate, repeated-sample independence, the ideal least-common-multiple product law, a factoring reduction, a certified selection procedure, full bit or gate complexity or empirical performance. A finite recursively generated list alone supplies no such complexity claim. The general supplied-R clock statement remains broader than this actual modular N-bound specialization.

## References

- Truth anchor: `D5/S3/Quantum/ShorContinuedFractions.shor_coprime_candidate`
- Truth anchor: `D5/S3/Quantum/ShorContinuedFractions.shor_nearest_candidate`
- Dependency: [D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents](../../S1/Depth/ContinuedFractions/FiniteRationalConvergents.md)
- Dependency: [D5/S3/Quantum/ShorCountingMarginal](ShorCountingMarginal.md)
