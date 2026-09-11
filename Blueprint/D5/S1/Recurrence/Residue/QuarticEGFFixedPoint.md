# The Quartic EGF Fixed Point

## Abstract

OEIS A396804 has a unique zero-constant rational formal solution with natural EGF coefficients.

The superscript four in the source denotes four compositional iterations. The zeroth iterate is the identity series X. The sequence a is constructed in Nat first; no integrality premise is assumed.

**Remark 1.1 (Encoding EGF coefficients).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Encoding a rational sequence s means taking ordinary coefficient s(n)/n!. Factorial normalization recovers s(n) exactly, including n=0.

**Remark 1.2 (Formal compositional iteration).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.iterateComp`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.iterateComp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zeroth iterate is X; each successor is f composed with the previous iterate. When f has constant coefficient zero, every iterate does too.

**Remark 1.3 (Contraction by one degree).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.step_contract`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.step_contract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If two coefficient sequences agree below d, applying the coefficient transformation for X exp(A fourth) gives agreement below d+1. This follows from the prefix locality of integral composition.

**Remark 1.4 (Natural approximations).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.approximation`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.approximation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Start with the natural sequence n, the EGF coefficients of X exp(X), and repeatedly apply step. The use of Nat gives a separate integrality proof.

**Remark 1.5 (The stabilized sequence).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.a`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

a(n) is coefficient n of approximation n+1. Prefix stability shows that all later approximations have the same value.

**Remark 1.6 (The rational formal series).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.A`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A encodes the natural sequence a as sum a(n) X^n/n!. Its constant term is zero.

**Remark 1.7 (Independent natural integrality).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.integral_coefficients`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.integral_coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, (a(n):Rat)=n! [X^n]A. This statement connects the natural construction with ordinary rational coefficients.

**Remark 1.8 (The exact source equation).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.A_equation`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.A_equation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructed A has constant coefficient zero and satisfies A=X*(exp Rat).subst(iterateComp A 4). Every substitution is justified.

**Remark 1.9 (Uniqueness among rational series).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.fixed_unique`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.fixed_unique` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Any two zero-constant rational solutions agree through every finite degree by contraction, and hence are equal. No coefficient integrality premise is imposed on these competing solutions.

**Remark 1.10 (Existence and uniqueness).**

Lean statement: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.unique_solution`

*Formalization.* `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.unique_solution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructed A supplies existence; fixed_unique gives uniqueness. Together these identify the formal series used in the final congruence.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.A`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.A_equation`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.a`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.approximation`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.fixed_unique`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.integral_coefficients`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.iterateComp`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.step_contract`
- Truth anchor: `D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.unique_solution`
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](IntegralEGFComposition.md)
