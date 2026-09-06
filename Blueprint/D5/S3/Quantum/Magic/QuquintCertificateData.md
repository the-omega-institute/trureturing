# Ququint Numerical Certificate Data

## Abstract

Exact numerical branch data in a real quartic field.

**Definition 1.1 (The real radical).**

$$\mathrm{radical}=\sqrt{10+2\cdot\sqrt{5}}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateData.radical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive real square root fixes the radical used in every numerical entry.

**Theorem 1.2 (Quartic identity).**

$$\mathrm{radical}^{4}-20\cdot\mathrm{radical}^{2}+80=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateData.radical_quartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squaring the defining radical and using Real.sq_sqrt gives the exact quartic relation.

**Theorem 1.3 (Bounds for the squared radical).**

$$14<\mathrm{radical}^{2} \land \mathrm{radical}^{2}<15$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateData.radical_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared radical lies strictly between fourteen and fifteen; these bounds certify the pivots.

**Remark 1.4 (The numerical base matrix).**

Lean statement: `D5/S3/Quantum/Magic/QuquintCertificateData.base`

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateData.base` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

base is the explicit four-by-four real matrix whose entries are rational polynomials in radical. QuquintCertificateBridge.base_eq identifies it with the signed nonzero phase-point contribution minus the norm contribution.

**Remark 1.5 (The five numerical matrices).**

Lean statement: `D5/S3/Quantum/Magic/QuquintCertificateData.zeroQ`

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateData.zeroQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

zeroQ lists five explicit four-by-four real matrices with entries in the same quartic field. QuquintCertificateBridge.zeroQ_eq identifies them with the five vanishing phase-point forms.

**Definition 1.6 (The thirty-two branches).**

$$\forall s:\mathrm{Fin} 32,\mathrm{branch}(s)=\mathrm{base}+\sum_{i:\mathrm{Fin} 5}\mathrm{ite}(\mathrm{Nat}.\mathrm{mod}(\mathrm{Nat}.\mathrm{div}(\mathrm{val}(s),2^{4-\mathrm{val}(i)}),2) = 0,-1,1)\cdot\mathrm{zeroQ}(i)$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateData.branch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.div denotes natural-number quotient and Nat.mod denotes remainder; they extract the five bits of the branch index, with the highest bit first. A zero bit contributes minus one and a one bit contributes plus one.

## References

- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateData.base`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateData.branch`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateData.radical`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateData.radical_bounds`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateData.radical_quartic`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateData.zeroQ`
