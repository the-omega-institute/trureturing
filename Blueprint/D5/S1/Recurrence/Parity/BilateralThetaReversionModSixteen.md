# Bilateral Theta Reversion Modulo Sixteen

## Abstract

The bilateral theta equation of OEIS A355872 implies Hanna's three congruences.

The entry cited in hanna2022a355872 defines A by the bilateral equation x = sum over integer j of (-x)^(j^2) A(x)^((j-1)^2). Its three conjectures concern a(n) modulo four and a(2n-1), a(2n) modulo eight, for every positive n.

Here A denotes generatingSeries, an integer formal power series with indeterminate X. The indices m, n, N, d are natural numbers; j is an integer. The function natAbs takes an integer's absolute value as a natural number. Subtraction in natural indices is truncated subtraction; j-1 and -N in the bilateral window are integer expressions. The operator mod denotes remainder. The operator coeff extracts a coefficient, mk constructs a series from its coefficients, and invOfUnit denotes the formal inverse with the specified unit constant coefficient.

**Definition 1.1 (An integer-indexed summand).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall j: \mathbb{Z}, \operatorname{bilateralTerm}\left(F, j\right) = (-X)^{\operatorname{natAbs}\left(j\right)^{2}} \cdot F^{\operatorname{natAbs}\left(j - 1\right)^{2}}$$

*Formalization.* `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.bilateralTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Natural absolute-value squares give the nonnegative exponents in the bilateral equation.

**Definition 1.2 (The stabilized integer coefficients).**

$$\begin{aligned}\forall m: \mathbb{N}, \operatorname{c}\left(m\right) = \operatorname{coeff}\left(m, \operatorname{P}\left(m + 1\right)\right)\\\operatorname{P}\left(0\right) = 0\\\forall d: \mathbb{N}, \operatorname{P}\left(d + 1\right) = 2 \cdot X - \operatorname{T}\left(\operatorname{P}\left(d\right)\right)\\\forall N: \mathbb{N}, \operatorname{W}\left(N\right) = \operatorname{Icc}\left(-N, N\right)\\\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), \forall N: \mathbb{N}, \operatorname{coeff}\left(N, \operatorname{T}\left(B\right)\right) = \sum_{j \in \operatorname{erase}\left(\operatorname{erase}\left(\operatorname{W}\left(N\right), 0\right), 1\right)} (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(B, j\right)\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The auxiliary P(d) is approximation at depth d. The auxiliary T(B) is tail(B), whose coefficient at N omits indices zero and one from W(N). Each remaining summand contains a positive power of X, so one iteration improves coefficient agreement by one degree. The coefficient at m therefore stabilizes at depth m+1.

**Definition 1.3 (The OEIS indexing).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = \operatorname{c}\left(4 \cdot n - 3\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence selects degree 4n-3 of A. The conjectures use n at least one; the definition itself uses natural subtraction for every n.

**Definition 1.4 (The integer generating series).**

$$A = \operatorname{mk}\left(c\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.generatingSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient function of A is c.

**Theorem 1.5 (The bilateral generating equation).**

$$(\operatorname{constantCoeff}\left(A\right) = 0) \land (\forall N: \mathbb{N}, \operatorname{coeff}\left(N, X\right) = \sum_{j \in \operatorname{Icc}\left(-N, N\right)} (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(A, j\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.generating_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stabilized iteration satisfies A=2X-T(A). At every positive degree the window contains zero and one, whose summands are A and -X. Restoring them gives the stated equation; the constant coefficient is zero.

**Theorem 1.6 (Uniqueness of the zero-constant solution).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(B\right) = 0) \implies ((\forall N: \mathbb{N}, \operatorname{coeff}\left(N, X\right) = \sum_{j \in \operatorname{Icc}\left(-N, N\right)} (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(B, j\right)\right))) \implies (B = A))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Isolating the same two indices turns every solution into a fixed point of the same operator. Induction on degree proves agreement of all coefficients and hence equality of the series.

**Theorem 1.7 (The coefficient order bound).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Z}\right), (\operatorname{constantCoeff}\left(F\right) = 0) \implies (\forall N: \mathbb{N}, \forall j: \mathbb{Z}, (N < \operatorname{natAbs}\left(j\right)^{2} + \operatorname{natAbs}\left(j - 1\right)^{2}) \implies (\operatorname{coeff}\left(N, \operatorname{bilateralTerm}\left(F, j\right)\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.bilateralTerm_coeff_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero constant coefficient makes F divisible by X. Raising this divisibility to the indicated powers shows that a summand is divisible by X to the sum of the two squares. Its lower coefficients vanish. An index outside the window [-N,N] has j^2>N, so the finite window is exact.

**Theorem 1.8 (Support in one residue class).**

$$\forall m: \mathbb{N}, (m \bmod 4 \neq 1) \implies (\operatorname{c}\left(m\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.support_one_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication adds support residues and taking powers multiplies them. The identity j^2+(j-1)^2 congruent to one modulo four makes every bilateral summand preserve support in that residue class. Iteration and coefficient stabilization transfer this support to A.

**Theorem 1.9 (The full reduction modulo sixteen).**

$$\operatorname{map}\left(\operatorname{intCastRingHom}\left(\operatorname{ZMod}\left(16\right)\right), A\right) = 2 \cdot X \cdot \operatorname{invOfUnit}\left(1 + X^{4}, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.mod_sixteen_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over ZMod(16), put S=2X invOfUnit(1+X^4,1). Then S^4=0. Every term of T(S) except index two contains at least the fourth power of S and vanishes. Thus T(S)=X^4 S. The inverse identity gives S+X^4 S=2X, so S is a fixed point. Reduction of A commutes with the finite-window operator; degree contraction identifies it with S. In the formula map applies the canonical integer-to-ZMod(16) ring homomorphism coefficientwise; intCastRingHom denotes Int.castRingHom. The right side is over ZMod(16).

**Theorem 1.10 (Hanna's congruence modulo four).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{a}\left(n\right) \bmod 4 = 2)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a355872-bilateral-theta-reversion-mod-sixteen` (proved) by `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a355872-bilateral-theta-reversion-mod-sixteen","declaration_gid":"D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2022). *OEIS A355872, g.f. satisfying x = Sum_{n=-oo..+oo} (-x)^(n^2) * A(x)^((n-1)^2)*. URL: <https://oeis.org/A355872>.

*Commentary.*

Coefficient comparison in S+X^4 S=2X gives coefficient 2(-1)^k at degree 4k+1. With k=n-1, reduction modulo four gives two for either sign.

**Theorem 1.11 (Hanna's two congruences modulo eight).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (((\operatorname{a}\left(2 \cdot n - 1\right) \bmod 8 = 2) \land (\operatorname{a}\left(2 \cdot n\right) \bmod 8 = 6)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.hanna_conjecture_mod_eight` (`✓ std3`). ∎

*Citation.* Paul D. Hanna (2022). *OEIS A355872, g.f. satisfying x = Sum_{n=-oo..+oo} (-x)^(n^2) * A(x)^((n-1)^2)*. URL: <https://oeis.org/A355872>.

*Commentary.*

At index 2n-1 the exponent k is even, so the coefficient is two modulo sixteen. At index 2n it is odd, so the coefficient is minus two modulo sixteen. Reduction modulo eight gives two and six.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.a`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.bilateralTerm`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.bilateralTerm_coeff_eq_zero`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.c`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.generatingSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.generating_equation`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.hanna_conjecture_mod_eight`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.mod_sixteen_identity`
- Truth anchor: `D5/S1/Recurrence/Parity/BilateralThetaReversionModSixteen.support_one_mod_four`
