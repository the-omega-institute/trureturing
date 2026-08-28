# Local Precision Unit

## Abstract

The prime's p-adic norm fixes its real logarithmic precision unit.

**Theorem 1.1 (The logarithmic unit is unique).**

$$\forall p: \mathbb{N}, \operatorname{Fact}(p.Prime) \Rightarrow (\exp(-\operatorname{precisionLength}(p)) = \Vert p \Vert_p \land \operatorname{precisionLength}(p) = \log(p) \land \forall ell: \mathbb{R}, \exp(-ell) = \Vert p \Vert_p \Rightarrow ell = \operatorname{precisionLength}(p)) \land \forall s: \mathbb{R}, p^{-s} = \exp(-s \times \log(p)).$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/LocalPrecisionUnit.local_precision_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p, precisionLength is the source logarithmic length constructed from the canonical p-adic norm. Its exponential weight equals the norm of p, the value is log p, and no other real length has that weight.

The final clause rewrites the real power p^(-s) as the exponential of -s log p for every real s.

## References

- Truth anchor: `D5/S3/AnalyticClosure/LocalPrecisionUnit.local_precision_unit`
