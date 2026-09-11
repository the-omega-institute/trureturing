# Hanna's Odd-Index Parity Conjecture

## Abstract

Every odd-index coefficient beyond the first in OEIS A389472 is even.

The entry cited in hanna2025a389472 gives the generating equation A(x)=A(x^2+x^3)/x^2-1 and conjectures a(2n-1)=0 modulo two for n>1. The formal equation is x^2(A(x)+1)=A(x^2+x^3), with a(0)=0 and a(1)=a(2)=1. The equation forces a(1)=1 but leaves a(2) free; the seed a(2)=1 selects the sequence in the entry. The separate conjecture modulo three is not asserted here.

All indices and exponents are natural numbers, and subtraction in an index is natural subtraction. Fin(n) consists of k with 0<=k<n, read as natural numbers in coefficients and exponents; range(n) is the same finite set of natural indices. The function div is natural integer division. Values of a and binomial coefficients in products are integers. PowerSeries(Z) is the formal power-series ring with indeterminate X. The notation subst(B,Q) means B composed with Q, coeff(n,B) is coefficient n, and mk(a) constructs the series with coefficient function a.

**Definition 1.1 (The normalized coefficient sequence).**

$$\begin{aligned}\operatorname{a}: \mathbb{N} \to \mathbb{Z}\\\operatorname{a}\left(0\right) = 0\\\operatorname{a}\left(1\right) = 1\\\operatorname{a}\left(2\right) = 1\\\forall n: \mathbb{N}, \operatorname{a}\left(n + 3\right) = \sum_{k: \operatorname{Fin}\left(n + 3\right)} (\operatorname{a}\left(k\right) \cdot \operatorname{coeff}\left(n + 5, (X^{2} + X^{3})^{k}\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three seeds and a recursion using only indices below n+3 define an integer sequence. The substituted powers determine its recursion kernel.

**Definition 1.2 (The generating series).**

$$\operatorname{generatingSeries}: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coefficient n of generatingSeries is a(n).

**Theorem 1.3 (The functional equation and all three seeds).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 0) \land ((\operatorname{coeff}\left(1, \operatorname{generatingSeries}\right) = 1) \land ((\operatorname{coeff}\left(2, \operatorname{generatingSeries}\right) = 1) \land (X^{2} \cdot (\operatorname{generatingSeries} + 1) = \operatorname{subst}\left(\operatorname{generatingSeries}, X^{2} + X^{3}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kth power of X^2+X^3 has no coefficients below degree 2k. Thus each substituted coefficient is a finite sum. The recursion establishes the equation in degrees at least five; the three prescribed seeds establish the remaining degrees and the displayed normalization.

**Theorem 1.4 (Uniqueness with the prescribed seeds).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies ((\operatorname{coeff}\left(1, B\right) = 1) \implies ((\operatorname{coeff}\left(2, B\right) = 1) \implies ((X^{2} \cdot (B + 1) = \operatorname{subst}\left(B, X^{2} + X^{3}\right)) \implies (B = \operatorname{generatingSeries}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least three, coefficient n+2 of the functional equation determines coefficient n using only smaller indices. Strong induction starting from the three seeds proves equality with generatingSeries.

**Theorem 1.5 (The binomial coefficient recurrence).**

$$\forall n: \mathbb{N}, (3 \le n) \implies (\operatorname{a}\left(n\right) = \sum_{k \in \operatorname{range}\left(\operatorname{div}\left(n, 2\right) + 2\right)} (\operatorname{a}\left(k\right) \cdot \operatorname{choose}\left(k, n + 2 - 2 \cdot k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.coeff_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extract coefficient n+2 from the proved generating equation and factor (X^2+X^3)^k as X^(2k)(1+X)^k. The binomial coefficient formula gives the displayed sum, whose upper bound includes exactly 2k<=n+2.

**Theorem 1.6 (The first A389472 conjecture).**

$$\forall n: \mathbb{N}, (1 < n) \implies (2 \mid \operatorname{a}\left(2 \cdot n - 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a389472-square-cube-substitution-odd-index-parity` (proved) by `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a389472-square-cube-substitution-odd-index-parity","declaration_gid":"D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A389472, g.f. satisfying A(x) = A(x^2 + x^3)/x^2 - 1*. URL: <https://oeis.org/A389472>.

*Commentary.*

For an odd index m>=3, the lower binomial index m+2-2k is odd. If k is even, the identity j choose(k,j)=k choose(k-1,j-1) makes the binomial coefficient even. If k is odd and at least three, then k<m, so strong induction makes a(k) even. The only remaining odd index is k=1, whose binomial coefficient is choose(1,m)=0. Every summand is therefore even.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.a`
- Truth anchor: `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.coeff_recurrence`
- Truth anchor: `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity.hanna_conjecture`
