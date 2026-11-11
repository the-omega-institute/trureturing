# SixRowHeadPolynomial

## Abstract

The integer polynomial is the exact residual after two squaring steps in the K6 head estimate. Homogeneous Bernstein rows evaluate nonnegatively when their natural-number coefficients and six interval coordinates are nonnegative. The constraint bound excludes only boxes on which the feasibility polynomial is strictly negative.

The integer polynomial is the exact residual after two squaring steps in the K6 head estimate. Homogeneous Bernstein rows evaluate nonnegatively when their natural-number coefficients and six interval coordinates are nonnegative. The constraint bound excludes only boxes on which the feasibility polynomial is strictly negative.

**Definition 1.1 (P).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.P`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def P (z k h : ℝ) : ℝ

**Definition 1.2 (numerator).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.numerator`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.numerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def numerator (z k h : ℝ) : ℝ

**Theorem 1.3 (numerator identity).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.numerator_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.numerator_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem numerator_identity (z k h : ℝ) : numerator z k h = 16*k*z^4*P z k h

**Definition 1.4 (row).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.row`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def row (cs : List ℝ) (x y : ℝ) : ℝ

**Definition 1.5 (tensor).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.tensor`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.tensor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def tensor (cs : List (List (List ℕ))) (z Z k K h H : ℝ) : ℝ

**Theorem 1.6 (tensor nonneg).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.tensor_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.tensor_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem tensor_nonneg (cs : List (List (List ℕ))) (z Z k K h H : ℝ) (hz : 0 ≤ z) (hZ : 0 ≤ Z) (hk : 0 ≤ k) (hK : 0 ≤ K) (hh : 0 ≤ h) (hH : 0 ≤ H) : 0 ≤ tensor cs z Z k K h H

**Definition 1.7 (constraint).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.constraint`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.constraint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def constraint (z k h : ℝ) : ℝ

**Theorem 1.8 (constraint upper).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.constraint_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.constraint_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem constraint_upper (z k h a b c : ℝ) (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1) (hk : 0 ≤ k) (hkb : k ≤ b) (hh : 0 ≤ h) (hhc : h ≤ c) : constraint z k h ≤ constraint a b c

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.P`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.constraint`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.constraint_upper`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.numerator`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.numerator_identity`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.row`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.tensor`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.tensor_nonneg`
