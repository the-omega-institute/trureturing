# Record Entropy Integrals

## Abstract

Two real interval integrals give the exact uniform binary-entropy average.

**Theorem 1.1 (Negative u log u integrates to one quarter).**

$$\int_{0}^{1} -u \log u du=\frac{1}{4}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/RecordEntropy.neg_mul_log_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous primitive built from u log u handles the singular logarithmic endpoint. Mathlib's endpoint fundamental theorem of calculus then evaluates the real interval integral exactly.

**Theorem 1.2 (The uniform binary-entropy integral in bits).**

$$\int_{0}^{1} \frac{-u \log u - (1-u) \log (1-u)}{\log 2} du=\frac{1}{2 \log 2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/RecordEntropy.haar_record_entropy_bits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The substitution u maps to 1 - u identifies the two entropy summands. Their integrals therefore add to one half, and division by the natural logarithm of two converts the result to bits.

**Remark 1.3 (The physical pushforward is out of scope).**

Lean statement: `D5/S3/Constants/RecordEntropy.haar_record_entropy_bits`

*Formalization.* `D5/S3/Constants/RecordEntropy.haar_record_entropy_bits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The checked declaration is only a real interval identity for a uniform parameter u. It does not construct Bloch-sphere Haar measure or prove that measurement probability pushes that measure forward to the uniform distribution on [0, 1]. That bridge remains an unresolved X_Assumptions question, including how a classical assumption would relate to the no-new-axiom objective. The phrase record entropy carries the intended physical reading in this prose; the Lean type makes no physical claim and adds no axiom.

## References

- Truth anchor: `D5/S3/Constants/RecordEntropy.neg_mul_log_integral`
- Truth anchor: `D5/S3/Constants/RecordEntropy.haar_record_entropy_bits`
- Truth anchor: `D5/S3/Constants/RecordEntropy.haar_record_entropy_bits`
