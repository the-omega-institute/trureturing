# Bilateral Quarter-Shift Theta Congruence

## Abstract

The integer solution of the A363104 bilateral equation is theta_3 modulo four.

Paul D. Hanna's entry hanna2023a363104, dated May 21, 2023, defines A by 4 = sum over integer n of (-x)^n (4*A(x)+x^(n-1))^(n+1). It conjectures the theta_3 congruence and the square classification of the positive coefficients modulo four.

The terms at n=0 and n=-1 contain opposite Laurent monomials x^(-1) and -x^(-1). They cancel, leaving 4*A and zero respectively. For n=-m-2 with m natural, factoring the negative power gives the displayed negativeTerm. The formal equation below uses exact finite coefficient windows; it does not assert a bilateral infinite-sum operation on formal power series.

All series are over the integers unless mapped to ZMod(4). The indices m, n in a(n), N, and d are natural; the index n in bilateralTerm is an integer. The function toNat sends negative integers to zero. Subtraction after toNat is natural truncated subtraction; the window endpoints and -n-2 use integer arithmetic. The operations div and mod are integer division and remainder. The operator mk builds a series from coefficients, and invOfUnit is the formal unit inverse. The symbols positiveTerm, negativeTerm, R, and P below are the private auxiliary definitions.

The imported thetaSeries and its coefficient formula are from `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.thetaSeries` and `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.coeff_thetaSeries`. Its constant coefficient is one, and each positive square coefficient is two; all other coefficients are zero.

**Definition 1.1 (The reindexed bilateral terms).**

$$\begin{aligned}\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall n: \mathbb{Z}, \operatorname{bilateralTerm}\left(A, n\right) = (\operatorname{if} (n = 0) \operatorname{then} (4) \cdot (A) \operatorname{else} (\operatorname{if} (n = -(1)) \operatorname{then} 0 \operatorname{else} (\operatorname{if} (0 < n) \operatorname{then} \operatorname{positiveTerm}\left(A, \operatorname{toNat}\left(n\right) - (1)\right) \operatorname{else} \operatorname{negativeTerm}\left(A, \operatorname{toNat}\left(-(n) - (2)\right)\right))))\\\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall m: \mathbb{N}, \operatorname{positiveTerm}\left(A, m\right) = (((-(1))^{m + 1}) \cdot ((X)^{m + 1})) \cdot (((4) \cdot (A) + (X)^{m})^{m + 2})\\\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall m: \mathbb{N}, \operatorname{negativeTerm}\left(A, m\right) = (((-(1))^{m + 2}) \cdot ((X)^{(m)^{2} + (3) \cdot (m) + 1})) \cdot ((\operatorname{invOfUnit}\left(1 + ((4) \cdot (A)) \cdot ((X)^{m + 3}), 1\right))^{m + 1})\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.bilateralTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive index m+1 and negative index -m-2 use nonnegative exponents and an inverse whose constant coefficient is one.

**Theorem 1.2 (Exact finite windows).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall N: \mathbb{N}, \forall n: \mathbb{Z}, ((n < -(N) - (2)) \lor (N < n)) \implies (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(A, n\right)\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.bilateralTerm_coeff_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both terms indexed by m contain at least X^(m+1). Every integer index outside [-N-2,N] therefore has zero coefficient at degree N.

**Definition 1.3 (The stabilized integer coefficients).**

$$\begin{aligned}\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{coeff}\left(n, \operatorname{P}\left(n + 1\right)\right)\\\operatorname{P}\left(0\right) = 1\\\forall d: \mathbb{N}, \operatorname{P}\left(d + 1\right) = 1 - (\operatorname{mk}\left((N: \mathbb{N} \mapsto \operatorname{div}\left(\operatorname{coeff}\left(N, \operatorname{R}\left(\operatorname{P}\left(d\right)\right)\right), 4\right))\right))\\\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall N: \mathbb{N}, \operatorname{coeff}\left(N, \operatorname{R}\left(B\right)\right) = \sum_{m \in \operatorname{range}\left(N + 1\right)} (\operatorname{coeff}\left(N, \operatorname{positiveTerm}\left(B, m\right) + \operatorname{negativeTerm}\left(B, m\right)\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each positive-negative pair vanishes at A=0. Differences of powers and the unit-inverse difference identity show that every pair is divisible by four. Thus the displayed division is exact over the integers. Agreement below degree d improves to agreement below degree d+1 under the iteration, so the selected coefficients stabilize.

**Definition 1.4 (The integer generating series).**

$$\operatorname{generatingSeries} = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient function of generatingSeries is a.

**Theorem 1.5 (The defining bilateral equation).**

$$(\operatorname{constantCoeff}\left(\operatorname{generatingSeries}\right) = 1) \land (\forall N: \mathbb{N}, \operatorname{coeff}\left(N, 4\right) = \operatorname{coeff}\left(N, \sum_{n \in \operatorname{Icc}\left(-(N) - (2), N\right)} (\operatorname{bilateralTerm}\left(\operatorname{generatingSeries}, n\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stabilized series is fixed by the integral iteration. Rejoining the pairs restores the finite integer window. Its extra positive endpoint has zero coefficient, and the index-zero term gives 4*A.

**Theorem 1.6 (Uniqueness of the solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 1) \implies ((\forall N: \mathbb{N}, \operatorname{coeff}\left(N, 4\right) = \operatorname{coeff}\left(N, \sum_{n \in \operatorname{Icc}\left(-(N) - (2), N\right)} (\operatorname{bilateralTerm}\left(B, n\right))\right)) \implies (B = \operatorname{generatingSeries}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every series satisfying the same finite-window equation is fixed by the iteration. Degree contraction proves equality at every coefficient.

**Theorem 1.7 (The constant coefficient).**

$$\operatorname{a}\left(0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.a_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every paired term has positive order, so the iteration has constant coefficient one.

**Theorem 1.8 (Cancellation over the integers).**

$$\exists Q: \operatorname{PowerSeries}\left(\mathbb{Z}\right), 1 = (\operatorname{generatingSeries}) \cdot (\operatorname{thetaSeries}) + (4) \cdot (Q)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.cancellation_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Modulo sixteen, (4*A)^2 vanishes. Expanding each pair leaves its linear terms, whose weighted finite sum telescopes to eight times A times the positive-square support series. Multiplication by eight removes the alternating signs modulo sixteen. Hence the difference between the remainder and 4*A*(thetaSeries-1) is 16*Q with integral Q. The generating equation gives 4=4*(A*thetaSeries+4*Q); cancelling the nonzero factor four in the integer series ring gives the statement.

**Theorem 1.9 (The series congruence).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(4\right)\right), \operatorname{generatingSeries}\right) = \operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(4\right)\right), \operatorname{thetaSeries}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.mod_four_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reduction of thetaSeries is 1+2*S, where S indicates the positive squares. Its square is one over ZMod(4). Reducing the integer cancellation identity and multiplying by this self-inverse series identifies the reduction of generatingSeries.

**Theorem 1.10 (Hanna's A363104 conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((((\operatorname{a}\left(n\right) \bmod 4 = 2) \iff (\operatorname{IsSquare}\left(n\right))) \land ((\operatorname{a}\left(n\right) \bmod 4 = 0) \iff (\neg (\operatorname{IsSquare}\left(n\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a363104-bilateral-quarter-shift-theta-mod-four` (proved) by `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a363104-bilateral-quarter-shift-theta-mod-four","declaration_gid":"D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2023). *OEIS A363104, g.f. satisfying 4 = Sum_{n in Z} (-x)^n (4 A(x) + x^(n-1))^(n+1)*. URL: <https://oeis.org/A363104>.

*Commentary.*

At a positive index, the imported theta coefficient is two exactly at squares and zero otherwise. Coefficient comparison and the integer-cast remainder equivalence prove both biconditionals in hanna2023a363104.

## References

- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.a`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.a_zero`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.bilateralTerm`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.bilateralTerm_coeff_eq_zero`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.cancellation_identity`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Bilateral/BilateralQuarterShiftThetaModFour.mod_four_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.coeff_thetaSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.thetaSeries`
- Dependency: [D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour](../Parity/ThetaSelfCompositionModFour.md)
