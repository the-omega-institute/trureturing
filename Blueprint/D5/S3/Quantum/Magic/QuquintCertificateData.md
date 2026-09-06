# Ququint Numerical Certificate Data

## Abstract

Exact numerical branch data in a real quartic field.

**Definition 1.1 (The real radical).**

$$\mathrm{radical}=\sqrt{10+2\cdot\sqrt{5}}$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateData.radical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive real square root fixes the radical used in every numerical entry.

**Theorem 1.2 (Square identity).**

$$\mathrm{radical}^{2}=10+2\cdot\sqrt{5}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateData.radical_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real.sq_sqrt gives the shared square identity used by the quartic relation and bounds.

**Theorem 1.3 (Quartic identity).**

$$\mathrm{radical}^{4}-20\cdot\mathrm{radical}^{2}+80=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateData.radical_quartic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squaring the defining radical and using Real.sq_sqrt gives the exact quartic relation.

**Theorem 1.4 (Bounds for the squared radical).**

$$14<\mathrm{radical}^{2} \land \mathrm{radical}^{2}<15$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/QuquintCertificateData.radical_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared radical lies strictly between fourteen and fifteen; these bounds certify the pivots.

**Definition 1.5 (The numerical base matrix).**

$$\mathrm{base}=[[5-3\cdot\mathrm{radical}^{2}/4,\mathrm{radical}^{2}/8,-\mathrm{radical}^{3}/8+\mathrm{radical}/2,-3\cdot\mathrm{radical}^{3}/16+5\cdot\mathrm{radical}/4],[\mathrm{radical}^{2}/8,5-3\cdot\mathrm{radical}^{2}/4,3\cdot\mathrm{radical}^{3}/16-5\cdot\mathrm{radical}/4,\mathrm{radical}^{3}/8-\mathrm{radical}/2],[-\mathrm{radical}^{3}/8+\mathrm{radical}/2,3\cdot\mathrm{radical}^{3}/16-5\cdot\mathrm{radical}/4,21-61\cdot\mathrm{radical}^{2}/20,10-83\cdot\mathrm{radical}^{2}/40],[-3\cdot\mathrm{radical}^{3}/16+5\cdot\mathrm{radical}/4,\mathrm{radical}^{3}/8-\mathrm{radical}/2,10-83\cdot\mathrm{radical}^{2}/40,21-61\cdot\mathrm{radical}^{2}/20]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateData.base` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Matrices are vectors of rows. QuquintCertificateBridge.base_eq identifies base with the signed nonzero phase-point contribution minus the norm contribution.

**Definition 1.6 (The five numerical matrices).**

$$\mathrm{zeroQ}=[[[1-\mathrm{radical}^{2}/20,1-3\cdot\mathrm{radical}^{2}/40,\mathrm{radical}^{3}/20-\mathrm{radical}/2,\mathrm{radical}^{3}/80-\mathrm{radical}/20],[1-3\cdot\mathrm{radical}^{2}/40,1-\mathrm{radical}^{2}/20,\mathrm{radical}^{3}/80-7\cdot\mathrm{radical}/20,-\mathrm{radical}/10],[\mathrm{radical}^{3}/20-\mathrm{radical}/2,\mathrm{radical}^{3}/80-7\cdot\mathrm{radical}/20,9\cdot\mathrm{radical}^{2}/100-1/5,17\cdot\mathrm{radical}^{2}/200-2/5],[\mathrm{radical}^{3}/80-\mathrm{radical}/20,-\mathrm{radical}/10,17\cdot\mathrm{radical}^{2}/200-2/5,9\cdot\mathrm{radical}^{2}/100-1]],[[1-\mathrm{radical}^{2}/20,1-3\cdot\mathrm{radical}^{2}/40,\mathrm{radical}^{3}/20-7\cdot\mathrm{radical}/10,-3\cdot\mathrm{radical}^{3}/80+13\cdot\mathrm{radical}/20],[1-3\cdot\mathrm{radical}^{2}/40,1-\mathrm{radical}^{2}/20,3\cdot\mathrm{radical}^{3}/80-13\cdot\mathrm{radical}/20,-\mathrm{radical}^{3}/20+7\cdot\mathrm{radical}/10],[\mathrm{radical}^{3}/20-7\cdot\mathrm{radical}/10,3\cdot\mathrm{radical}^{3}/80-13\cdot\mathrm{radical}/20,7/5-11\cdot\mathrm{radical}^{2}/100,17\cdot\mathrm{radical}^{2}/200-7/5],[-3\cdot\mathrm{radical}^{3}/80+13\cdot\mathrm{radical}/20,-\mathrm{radical}^{3}/20+7\cdot\mathrm{radical}/10,17\cdot\mathrm{radical}^{2}/200-7/5,7/5-11\cdot\mathrm{radical}^{2}/100]],[[1-\mathrm{radical}^{2}/20,1-3\cdot\mathrm{radical}^{2}/40,\mathrm{radical}/10,-\mathrm{radical}^{3}/80+7\cdot\mathrm{radical}/20],[1-3\cdot\mathrm{radical}^{2}/40,1-\mathrm{radical}^{2}/20,-\mathrm{radical}^{3}/80+\mathrm{radical}/20,-\mathrm{radical}^{3}/20+\mathrm{radical}/2],[\mathrm{radical}/10,-\mathrm{radical}^{3}/80+\mathrm{radical}/20,9\cdot\mathrm{radical}^{2}/100-1,17\cdot\mathrm{radical}^{2}/200-2/5],[-\mathrm{radical}^{3}/80+7\cdot\mathrm{radical}/20,-\mathrm{radical}^{3}/20+\mathrm{radical}/2,17\cdot\mathrm{radical}^{2}/200-2/5,9\cdot\mathrm{radical}^{2}/100-1/5]],[[1-\mathrm{radical}^{2}/20,1-3\cdot\mathrm{radical}^{2}/40,-\mathrm{radical}/10,-\mathrm{radical}^{3}/80+\mathrm{radical}/20],[1-3\cdot\mathrm{radical}^{2}/40,1-\mathrm{radical}^{2}/20,\mathrm{radical}^{3}/80-\mathrm{radical}/4,-\mathrm{radical}^{3}/40+3\cdot\mathrm{radical}/10],[-\mathrm{radical}/10,\mathrm{radical}^{3}/80-\mathrm{radical}/4,3/5-11\cdot\mathrm{radical}^{2}/100,3/5-23\cdot\mathrm{radical}^{2}/200],[-\mathrm{radical}^{3}/80+\mathrm{radical}/20,-\mathrm{radical}^{3}/40+3\cdot\mathrm{radical}/10,3/5-23\cdot\mathrm{radical}^{2}/200,1/5-11\cdot\mathrm{radical}^{2}/100]],[[1-\mathrm{radical}^{2}/20,1-3\cdot\mathrm{radical}^{2}/40,\mathrm{radical}^{3}/40-3\cdot\mathrm{radical}/10,-\mathrm{radical}^{3}/80+\mathrm{radical}/4],[1-3\cdot\mathrm{radical}^{2}/40,1-\mathrm{radical}^{2}/20,\mathrm{radical}^{3}/80-\mathrm{radical}/20,\mathrm{radical}/10],[\mathrm{radical}^{3}/40-3\cdot\mathrm{radical}/10,\mathrm{radical}^{3}/80-\mathrm{radical}/20,1/5-11\cdot\mathrm{radical}^{2}/100,3/5-23\cdot\mathrm{radical}^{2}/200],[-\mathrm{radical}^{3}/80+\mathrm{radical}/4,\mathrm{radical}/10,3/5-23\cdot\mathrm{radical}^{2}/200,3/5-11\cdot\mathrm{radical}^{2}/100]]]$$

*Formalization.* `D5/S3/Quantum/Magic/QuquintCertificateData.zeroQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These five matrices use the same row convention and index order as QuquintCertificateBridge.zeroIndex. QuquintCertificateBridge.zeroQ_eq identifies them with the five vanishing phase-point forms.

**Definition 1.7 (The thirty-two branches).**

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
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateData.radical_sq`
- Truth anchor: `D5/S3/Quantum/Magic/QuquintCertificateData.zeroQ`
