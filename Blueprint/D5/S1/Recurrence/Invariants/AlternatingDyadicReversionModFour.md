# Alternating Dyadic Reversion Modulo Four

## Abstract

The coefficients of OEIS A389537 satisfy Hanna's mod-four classification.

The entry cited in hanna2025a389537 defines A by A(A(x)-x)=A(x)^2. Its conjecture says that for n greater than two, a(n) is congruent to two modulo four exactly at indices 3 times a power of two, and is divisible by four at every other such index.

All indices are natural numbers. The coefficient functions r and a take integer values. R denotes inverseSeries and A denotes generatingSeries in PowerSeries(Z), with indeterminate X. The local coefficient function r is specified together with R below. The operator mk constructs a series from its coefficient function; coeff(n,B) extracts a coefficient; subst(B,C) substitutes C into B. The notation inv(R) is Mathlib's substInvOfIsUnit applied to the proved unit linear coefficient of R. The operator div is natural-number division on the index, and mod is the natural-number remainder.

**Definition 1.1 (The alternating dyadic inverse).**

$$\begin{aligned}R = \operatorname{mk}\left(r\right)\\\forall n: \mathbb{N}, \operatorname{r}\left(n\right) = \operatorname{if} (n = 0) \operatorname{then} 0 \operatorname{else} \operatorname{if} (n = 1) \operatorname{then} 1 \operatorname{else} \operatorname{if} (2 \mid n) \operatorname{then} -\operatorname{r}\left(\operatorname{div}\left(n, 2\right)\right) \operatorname{else} 0\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.inverseSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The recursion sets r(0)=0 and r(1)=1. At every other even index it negates the coefficient at half the index; at every other odd index it vanishes. Thus R is the alternating dyadic series, with coefficient (-1)^j at degree 2^j and zero elsewhere.

**Definition 1.2 (The integer coefficient sequence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{inv}\left(R\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient a(n) is extracted from the integral compositional inverse of R.

**Definition 1.3 (The generating series).**

$$A = \operatorname{mk}\left(a\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series A has coefficient function a and is the compositional inverse of R in both orders.

**Theorem 1.4 (The dyadic reversion identity).**

$$R + \operatorname{subst}\left(R, X^{2}\right) = X$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.inverse_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient comparison reduces every positive even degree to half that degree. The two coefficients have opposite signs and cancel; the linear coefficient remains one.

**Theorem 1.5 (The OEIS equation and normalization).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land (\operatorname{subst}\left(A, (A - X)\right) = A^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting A into R+R(X^2)=X and using R(A)=X gives R(A^2)=A-X. Composing with A gives A(A-X)=A^2. Integral compositional reversion supplies the two normalization conditions.

**Theorem 1.6 (Uniqueness of the normalized solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies (\operatorname{coeff}\left(1, B\right) = 1) \implies (\operatorname{subst}\left(B, (B - X)\right) = B^{2}) \implies B = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any normalized integer solution B, its compositional inverse S satisfies S+S(X^2)=X. Strong induction on the coefficient index shows that S=R, since the only earlier index required is its half. The inverse identities then give B=A.

**Theorem 1.7 (Hanna's coefficient conjecture).**

$$\forall n: \mathbb{N}, (2 < n) \implies ((\operatorname{a}\left(n\right) \bmod 4 = 2 \iff (\exists k: \mathbb{N}, n = 3 \cdot 2^{k})) \land (\operatorname{a}\left(n\right) \bmod 4 = 0 \iff \neg (\exists k: \mathbb{N}, n = 3 \cdot 2^{k})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a389537-alternating-dyadic-reversion-mod-four` (proved) by `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a389537-alternating-dyadic-reversion-mod-four","declaration_gid":"D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2025). *OEIS A389537, g.f. satisfying A(A(x) - x) = A(x)^2*. URL: <https://oeis.org/A389537>.

*Commentary.*

Work over ZMod(4), and let D have coefficient one exactly at indices 3 times a power of two. Halving these indices gives D=X^3+D(X^2). Squaring erases a perturbation 2T, so the inverse equation gives R(S+2T)=R(S)+2T for zero-constant S and T. Set U=X+X^2. Since U^2=U(X^2)+2X^3, H=R(U) satisfies H+H(X^2)=U-2X^3. The series X+2D satisfies the same equation and has the same constant coefficient, so coefficient halving proves H=X+2D. Consequently R(U+2D)=X, and compositional inversion gives A=U+2D modulo four. Extracting every coefficient above degree two proves both biconditionals.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.inverseSeries`
- Truth anchor: `D5/S1/Recurrence/Invariants/AlternatingDyadicReversionModFour.inverse_equation`
