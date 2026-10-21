# A local flat mismatch certificate

## Abstract

An exact local certificate permits different flat pi-edge labels on equal shared-face lengths.

**Definition 1.1 (The forbidden local certificate).**

$$claim \Leftrightarrow \left(\neg \left(\operatorname{sigma}\left(0\right) = \operatorname{tau}\left(0\right) \land \left(\operatorname{sigma}\left(1\right) = \operatorname{tau}\left(1\right) \land \left(\operatorname{sigma}\left(5\right) = \operatorname{tau}\left(5\right) \land \left(\left(\neg \operatorname{sigmaPi}\left(\right) = \operatorname{tauPi}\left(\right)\right) \land \left(\operatorname{cosine}\left(\operatorname{sigma}\left(0\right), \operatorname{sigma}\left(1\right), \operatorname{sigma}\left(2\right), \operatorname{sigma}\left(3\right), \operatorname{sigma}\left(4\right), \operatorname{sigma}\left(5\right)\right) = -\frac{4}{3} \land \left(\operatorname{cosine}\left(\operatorname{tau}\left(0\right), \operatorname{tau}\left(1\right), \operatorname{tau}\left(2\right), \operatorname{tau}\left(4\right), \operatorname{tau}\left(3\right), \operatorname{tau}\left(5\right)\right) = -\frac{4}{3} \land \left(\operatorname{cosine}\left(20, 2, 2, 2, 2, 2\right) = -\frac{10}{9} \land 7 < 8\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/Hyperideal/LocalMismatchCertificate.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the coordinate order (12, 13, 14, 34, 24, 23). The first vector is (2,2,2,20,2,2) and the second is (2,2,2,2,20,2). The shared face 123 therefore has the same three cosine lengths on both sides, while the selected flat pi pairs are (12,34) and (13,24). The claim says that this complete finite certificate cannot occur.

**Theorem 1.2 (The finite mismatch certificate).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LocalMismatchCertificate.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three shared coordinates agree and the two pair labels are different. For the selected edge in each orientation, the original cosine is -4/3, with denominator 27 and numerator -36. After orienting the long edge first, the original cosine is -10/9, with denominator 567 and numerator -630. The strict length comparison uses cosh(2 arccosh 2)=7<8. This is a local arithmetic certificate; it makes no claim about global face pairing, edge degree, total angle, or a closed CFMP realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LocalMismatchCertificate.claim`
- Truth anchor: `D5/S3/Geometry/Hyperideal/LocalMismatchCertificate.result`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
