# OEIS A392208: Parity Has Period Three

## Abstract

The implicit exponential generating function of OEIS A392208 has coefficient parity of period three.

**Definition 1.1 (egfOne).**

$$\forall R: Type, [\operatorname{CommSemiring}\left(R\right)], \forall n \in \mathbb{N},\; \operatorname{egfOne}\left(n\right) = (\operatorname{ite}\left(n = 0, 1, 0\right): R)$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula gives the coefficient operation or identity with all parameters quantified.

**Theorem 1.2 (egfPow congr at).**

$$\forall R: Type, [\operatorname{CommSemiring}\left(R\right)], \forall f \in (\mathbb{N} \to R),\; \forall fp \in (\mathbb{N} \to R),\; \forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \left(\forall k \in \mathbb{N},\; k \le n \Rightarrow f\left(k\right) = fp\left(k\right)\right) \Rightarrow \operatorname{egfPow}\left(f, m, n\right) = \operatorname{egfPow}\left(fp, m, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfPow_congr_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula gives the coefficient operation or identity with all parameters quantified.

**Theorem 1.3 (egfSeries mul).**

$$\forall f \in (\mathbb{N} \to \mathbb{Q}),\; \forall g \in (\mathbb{N} \to \mathbb{Q}),\; \operatorname{egfSeries}\left(\operatorname{egfMul}\left(f, g\right)\right) = \operatorname{egfSeries}\left(f\right) \cdot \operatorname{egfSeries}\left(g\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfSeries_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula gives the coefficient operation or identity with all parameters quantified.

**Theorem 1.4 (egfSeries pow).**

$$\forall f \in (\mathbb{N} \to \mathbb{Q}),\; \forall m \in \mathbb{N},\; \operatorname{egfSeries}\left(\operatorname{egfPow}\left(f, m\right)\right) = (\operatorname{egfSeries}\left(f\right))^{m}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfSeries_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula gives the coefficient operation or identity with all parameters quantified.

**Definition 1.5 (egfCoeffs).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall n \in \mathbb{N},\; \operatorname{egfCoeffs}\left(A, n\right) = ((n)!: \mathbb{Q}) \cdot \operatorname{coeff}\left(n, A\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfCoeffs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula gives the coefficient operation or identity with all parameters quantified.

**Theorem 1.6 (egfSeries egfCoeffs).**

$$\forall A \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{egfSeries}\left(\operatorname{egfCoeffs}\left(A\right)\right) = A$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfSeries_egfCoeffs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula gives the coefficient operation or identity with all parameters quantified.

OEIS A392208 (entry dated 2026-01-24) supplies the defining equation A'(x) = exp(A(x) A'(x)^3) and the conjecture that a(n) is even if and only if 3 divides n for n >= 1. The entry supplies context rather than the repository's strengthened integer recurrence, ODE uniqueness theorem, period-three proof, or theorem quantified over every integer sequence satisfying the equation.

**Definition 1.7 (Binomial convolution).**

$$\forall R: Type, (\operatorname{CommSemiring}\left(R\right)), f: (\mathbb{N} \to R), g: (\mathbb{N} \to R), n: \mathbb{N}, \operatorname{egfMul}\left(f, g, n\right) = \sum_{k \in \operatorname{range}\left(n + 1\right)} (\operatorname{choose}\left(n, k\right) \cdot \operatorname{f}\left(k\right) \cdot \operatorname{g}\left(n - k\right))$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfMul` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OEIS A392208 (2026-01-24) uses exponential generating functions. This definition is the binomial convolution whose nth value is the displayed finite sum; range(n+1) contains exactly 0 through n, and natural subtraction in n-k is truncated at zero.

**Definition 1.8 (Iterated binomial convolution).**

$$\forall R: Type, (\operatorname{CommSemiring}\left(R\right)), f: (\mathbb{N} \to R), n: \mathbb{N}, (\operatorname{egfPow}\left(f, 0, n\right) = \operatorname{ite}\left(n = 0, 1, 0\right)) \land (\forall m: \mathbb{N}, \operatorname{egfPow}\left(f, m + 1, n\right) = \operatorname{egfMul}\left(f, \operatorname{egfPow}\left(f, m\right), n\right))$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfPow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OEIS A392208 (2026-01-24) contains the third and fifth powers of the derivative. The zero convolution power is the sequence that is one at zero and zero elsewhere; the successor clause is left binomial convolution by f.

**Definition 1.9 (Recursive next-coefficient expression).**

$$\forall s: (\mathbb{N} \to \mathbb{Z}), n: \mathbb{N}, \operatorname{recurrenceRhs}\left(s, n\right) = \operatorname{egfPow}\left((j \mapsto \operatorname{s}\left(j + 1\right)), 5, n\right) + 3 \cdot \operatorname{egfMul}\left(\operatorname{egfMul}\left(s, \operatorname{egfPow}\left((j \mapsto \operatorname{s}\left(j + 1\right)), 3\right)\right), (j \mapsto \operatorname{ite}\left(j < n, \operatorname{s}\left(j + 2\right), 0\right)), n\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.recurrenceRhs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The repository defines this integer expression to append the next triangular recurrence coefficient. OEIS A392208 (2026-01-24) supplies context through its defining equation; this explicit integer recurrence expression is a repository strengthening beyond the OEIS wording.

**Definition 1.10 (Finite recursive coefficient table).**

$$\begin{aligned}table: (\mathbb{N} \to \operatorname{List}\left(\mathbb{Z}\right))\\\operatorname{table}\left(0\right) = [0, 1]\\\forall n: \mathbb{N}, \operatorname{table}\left(n + 1\right) = \operatorname{append}\left(\operatorname{table}\left(n\right), [\operatorname{recurrenceRhs}\left((k \mapsto \operatorname{getD}\left(\operatorname{table}\left(n\right), k, 0\right)), n\right)]\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public table starts with the exact list [0,1]. At the successor step it appends exactly one value of recurrenceRhs, evaluated on getD of the preceding table with default zero. This repository object makes the definition of a self-contained.

**Definition 1.11 (The recurrence-defined integer sequence).**

$$\begin{aligned}a: \mathbb{N} \to \mathbb{Z}\\\operatorname{a}\left(0\right) = 0\\\operatorname{a}\left(1\right) = 1\\\forall n: \mathbb{N}, \operatorname{a}\left(n + 2\right) = \operatorname{getD}\left(\operatorname{table}\left(n + 1\right), n + 2, 0\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OEIS A392208 (2026-01-24) supplies the initial coefficients 0,1 for A itself. The public finite table starts at [0,1], appends the triangular recurrence value at every step, and getD returns zero only outside that table; the displayed clauses are the literal definition of a. The next theorem exports its recurrence without the auxiliary table.

**Theorem 1.12 (Initial residues modulo two).**

$$(\operatorname{cast}\left(\operatorname{a}\left(0\right), \operatorname{ZMod}\left(2\right)\right) = 0) \land \left((\operatorname{cast}\left(\operatorname{a}\left(1\right), \operatorname{ZMod}\left(2\right)\right) = 1) \land (\operatorname{cast}\left(\operatorname{a}\left(2\right), \operatorname{ZMod}\left(2\right)\right) = 1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.initial_residues_mod_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrence-defined sequence has the right-associated initial residue triple (0,1,1) in ZMod(2), exactly as named in the candidate theorem atom.

**Theorem 1.13 (Triangular integer recurrence).**

$$\forall n: \mathbb{N}, \operatorname{a}\left(n + 2\right) = \operatorname{egfPow}\left((j \mapsto \operatorname{a}\left(j + 1\right)), 5, n\right) + 3 \cdot \operatorname{egfMul}\left(\operatorname{egfMul}\left(a, \operatorname{egfPow}\left((j \mapsto \operatorname{a}\left(j + 1\right)), 3\right)\right), (j \mapsto \operatorname{a}\left(j + 2\right)), n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.a_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ODE obtained from OEIS A392208 (2026-01-24) gives this integer recurrence. The apparent top second-derivative coefficient in the second summand vanishes because a(0)=0, so the recurrence is triangular with leading coefficient one.

**Theorem 1.14 (Period three modulo two).**

$$\forall n: \mathbb{N}, \operatorname{ModEqZ}\left(2, \operatorname{a}\left(n + 3\right), \operatorname{a}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.recurrence_coefficient_period_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the recurrence-defined sequence attached to OEIS A392208 (2026-01-24), every coefficient three places later is congruent modulo two. ModEqZ denotes integer congruence, not a cast or rational equality.

**Definition 1.15 (Implicit exponential power-series equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{ExpDefines}\left(A\right) = \left((\operatorname{constantCoeff}\left(A\right) = 0) \land (\operatorname{DQ}\left(A\right) = \operatorname{subst}\left(\operatorname{expQ}\left(\right), A \cdot (\operatorname{DQ}\left(A\right))^{3}\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.ExpDefines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the exact formal power-series equation from OEIS A392208 (2026-01-24), together with A(0)=0. DQ is formal differentiation over the rationals, expQ is the rational formal exponential series, and subst is formal substitution.

**Theorem 1.16 (The implicit equation implies the ODE).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{ExpDefines}\left(A\right)) \Rightarrow \left(1 - 3 \cdot A \cdot (\operatorname{DQ}\left(A\right))^{3}\right) \cdot \operatorname{DQ}\left(\operatorname{DQ}\left(A\right)\right) = (\operatorname{DQ}\left(A\right))^{5}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.exp_definition_implies_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the equation in OEIS A392208 (2026-01-24) with the formal substitution chain rule yields the displayed denominator-free ODE. No analytic convergence is assumed.

**Definition 1.17 (Rational exponential generating series).**

$$\forall s: (\mathbb{N} \to \mathbb{Q}), \operatorname{egfSeries}\left(s\right) = \operatorname{mk}\left((n \mapsto \frac{\operatorname{s}\left(n\right)}{(n)!})\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For OEIS A392208 (2026-01-24), the ordinary coefficient of x^n is s(n)/n!. The displayed fraction is rational division; no natural-number or integer division is used.

**Theorem 1.18 (The first derivative has constant coefficient one).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{ExpDefines}\left(A\right)) \Rightarrow \operatorname{constantCoeff}\left(\operatorname{DQ}\left(A\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.exp_definition_derivative_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the defining equation at constant coefficient zero yields A'(0)=1, which the identification of the OEIS-defined sequence with the recurrence uses.

**Definition 1.19 (Coefficient form of the ODE).**

$$\forall s: (\mathbb{N} \to \mathbb{Q}), \operatorname{EgfOde}\left(s\right) = \forall n: \mathbb{N}, \operatorname{s}\left(n + 2\right) = \operatorname{egfPow}\left((j \mapsto \operatorname{s}\left(j + 1\right)), 5, n\right) + 3 \cdot \operatorname{egfMul}\left(\operatorname{egfMul}\left(s, \operatorname{egfPow}\left((j \mapsto \operatorname{s}\left(j + 1\right)), 3\right)\right), (j \mapsto \operatorname{s}\left(j + 2\right)), n\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.EgfOde` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the coefficient recurrence for the ODE derived from OEIS A392208 (2026-01-24), written over rational sequences using the public binomial convolution operations.

**Theorem 1.20 (Uniqueness of the coefficient ODE).**

$$\forall s: (\mathbb{N} \to \mathbb{Q}), t: (\mathbb{N} \to \mathbb{Q}), ((\operatorname{s}\left(0\right) = 0) \land \left((\operatorname{s}\left(1\right) = 1) \land \left((\operatorname{t}\left(0\right) = 0) \land \left((\operatorname{t}\left(1\right) = 1) \land \left((\operatorname{EgfOde}\left(s\right)) \land (\operatorname{EgfOde}\left(t\right))\right)\right)\right)\right)) \Rightarrow s = t$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfOde_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For OEIS A392208 (2026-01-24), two rational coefficient sequences satisfying the same triangular ODE recurrence and initial coefficients 0,1 agree everywhere. Strong induction uses the vanished top coefficient in the nonlinear term.

**Definition 1.21 (Exact OEIS integer-sequence predicate).**

$$\forall s: (\mathbb{N} \to \mathbb{Z}), \operatorname{OEISDefines}\left(s\right) = \left((\operatorname{constantCoeff}\left(\operatorname{egfSeries}\left((n \mapsto \operatorname{castQ}\left(\operatorname{s}\left(n\right)\right))\right)\right) = 0) \land (\operatorname{DQ}\left(\operatorname{egfSeries}\left((n \mapsto \operatorname{castQ}\left(\operatorname{s}\left(n\right)\right))\right)\right) = \operatorname{subst}\left(\operatorname{expQ}\left(\right), \operatorname{egfSeries}\left((n \mapsto \operatorname{castQ}\left(\operatorname{s}\left(n\right)\right))\right) \cdot (\operatorname{DQ}\left(\operatorname{egfSeries}\left((n \mapsto \operatorname{castQ}\left(\operatorname{s}\left(n\right)\right))\right)\right))^{3}\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.OEISDefines` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This expands the defining expression from OEIS A392208 (2026-01-24): castQ maps every integer coefficient to the rationals before forming its EGF, whose constant coefficient is zero and whose derivative is the substituted exponential shown here.

**Theorem 1.22 (The recurrence sequence satisfies the OEIS equation).**

$$\operatorname{OEISDefines}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.a_oeisDefines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named witness connects the repository sequence a to the exact generating-function predicate from OEIS A392208 (2026-01-24). Its proof follows the integer recurrence through the rational coefficient ODE and reconstructs the implicit exponential equation.

**Theorem 1.23 (The OEIS equation determines the recurrence sequence).**

$$\forall s: (\mathbb{N} \to \mathbb{Z}), (\operatorname{OEISDefines}\left(s\right)) \Rightarrow s = a$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.oeis_defined_eq_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer sequence satisfying the exact equation of OEIS A392208 (2026-01-24) equals a. The proof derives the ODE and A'(0)=1, applies triangular uniqueness over the rationals, and then recovers equality of the integer coefficients.

**Theorem 1.24 (Every OEIS-defined sequence has period three modulo two).**

$$\forall s: (\mathbb{N} \to \mathbb{Z}), (\operatorname{OEISDefines}\left(s\right)) \Rightarrow \forall n: \mathbb{N}, \operatorname{ModEqZ}\left(2, \operatorname{s}\left(n + 3\right), \operatorname{s}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.oeis_coefficient_period_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identification with a transfers the kernel-verified period-three congruence to every integer sequence satisfying OEIS A392208 (2026-01-24).

**Theorem 1.25 (Every OEIS-defined sequence satisfies the parity law).**

$$\forall s: (\mathbb{N} \to \mathbb{Z}), (\operatorname{OEISDefines}\left(s\right)) \Rightarrow \forall n: \mathbb{N}, (1 \le n) \Rightarrow (\operatorname{Even}\left(\operatorname{s}\left(n\right)\right)) \Leftrightarrow (3 \mid n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.parity_conjecture_of_oeisDefines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This public companion transfers the parity theorem for a to every integer sequence satisfying the exact OEIS A392208 (2026-01-24) equation. It remains conditional on that defining predicate and is distinct from the unconditional atom anchor.

**Theorem 1.26 (The A392208 parity conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \Rightarrow (\operatorname{Even}\left(\operatorname{a}\left(n\right)\right)) \Leftrightarrow (3 \mid n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.a392208_parity_conjecture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the unconditional atom clause for the repository sequence a: at every positive index, a(n) is even if and only if three divides n. Its live proof specializes the general OEIS-defined parity theorem with the named witness a_oeisDefines.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.EgfOde`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.ExpDefines`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.OEISDefines`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.a`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.a392208_parity_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.a_oeisDefines`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.a_recurrence`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfCoeffs`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfMul`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfOde_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfOne`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfPow`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfPow_congr_at`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfSeries`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfSeries_egfCoeffs`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfSeries_mul`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.egfSeries_pow`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.exp_definition_derivative_zero`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.exp_definition_implies_ode`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.initial_residues_mod_two`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.oeis_coefficient_period_three`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.oeis_defined_eq_recurrence`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.parity_conjecture_of_oeisDefines`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.recurrenceRhs`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.recurrence_coefficient_period_three`
- Truth anchor: `D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.table`
