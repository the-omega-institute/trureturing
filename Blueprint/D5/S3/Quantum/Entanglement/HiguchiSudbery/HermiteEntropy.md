# HermiteEntropy

## Abstract

A cubic touching negMulLog at one sixth and one half majorizes it on the nonnegative half-line.

**Definition 1.1 (The cubic majorant).**

$$\forall (x : \operatorname{Real}), (\operatorname{pNat}\left(x\right) = \frac{4-3\cdot \operatorname{Real.log}\left(3\right)}{8}+(\frac{-11+2\cdot \operatorname{Real.log}\left(2\right)+12\cdot \operatorname{Real.log}\left(3\right)}{2})\cdot x+(\frac{36-39\cdot \operatorname{Real.log}\left(3\right)}{2})\cdot x^{2}+18\cdot (\operatorname{Real.log}\left(3\right)-1)\cdot x^{3})$$

*Formalization.* `D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteEntropy.pNat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four coefficients are displayed in full. The argument and logarithms are real; the divisions are real divisions.

**Theorem 1.2 (Majorization including zero).**

$$\forall (x : \operatorname{Real}), ((0 \le x) \Rightarrow (\operatorname{Real.negMulLog}\left(x\right) \le \operatorname{pNat}\left(x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteEntropy.hermite_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference has two double contacts and a positive fourth derivative on the positive half-line. Continuity of negMulLog and the polynomial includes zero.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteEntropy.hermite_majorant`
- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteEntropy.pNat`
- Dependency: [D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteMajorant](HermiteMajorant.md)
