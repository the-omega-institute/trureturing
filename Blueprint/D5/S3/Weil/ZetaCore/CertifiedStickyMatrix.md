# Certified Sticky Matrix

## Abstract

A conservative finite lower form certifies Schur and full block positivity.

**Theorem 1.1 (Finite lower matrix certification).**

$$\forall HP \in Type, HQ \in Type, APP \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), HP, HP\right), AQP \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), HP, HQ\right), AQQ \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), HQ, HQ\right), AQQInv \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), HQ, HQ\right), delta \in \operatorname{Real}\left(\right),\; \left(\operatorname{NormedAddCommGroup}\left(HP\right) \land \left(\operatorname{InnerProductSpace}\left(\operatorname{Real}\left(\right), HP\right) \land \left(\operatorname{NormedAddCommGroup}\left(HQ\right) \land \left(\operatorname{InnerProductSpace}\left(\operatorname{Real}\left(\right), HQ\right) \land \left(0 < delta \land \left(\left(\forall q \in HQ,\; \operatorname{mul}\left(delta, \operatorname{pow}\left(\operatorname{norm}\left(q\right), 2\right)\right) \le \operatorname{inner}\left(\operatorname{Real}\left(\right), \operatorname{apply}\left(AQQ, q\right), q\right)\right) \land \left(\left(\forall x \in HQ, y \in HQ,\; \operatorname{inner}\left(\operatorname{Real}\left(\right), \operatorname{apply}\left(AQQ, x\right), y\right) = \operatorname{inner}\left(\operatorname{Real}\left(\right), x, \operatorname{apply}\left(AQQ, y\right)\right)\right) \land \operatorname{comp}\left(AQQ, AQQInv\right) = \operatorname{id}\left(\operatorname{Real}\left(\right), HQ\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(\left(\forall p \in HP,\; 0 \le \operatorname{sub}\left(\operatorname{inner}\left(\operatorname{Real}\left(\right), \operatorname{apply}\left(APP, p\right), p\right), \operatorname{mul}\left(\operatorname{inv}\left(delta\right), \operatorname{pow}\left(\operatorname{norm}\left(\operatorname{apply}\left(AQP, p\right)\right), 2\right)\right)\right)\right) \Rightarrow \left(\forall p \in HP,\; 0 \le \operatorname{schurEnergy}\left(APP, AQP, AQQ, AQQInv, p\right)\right)\right) \land \left(\left(\forall p \in HP,\; 0 \le \operatorname{schurEnergy}\left(APP, AQP, AQQ, AQQInv, p\right)\right) \Rightarrow \left(\forall z \in \operatorname{Prod}\left(HP, HQ\right),\; 0 \le \operatorname{blockEnergy}\left(APP, AQP, AQQ, z\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaCore/CertifiedStickyMatrix.certified_sticky_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive complementary gap controls the coupling term. Positivity of the conservative lower form therefore implies Schur positivity, which implies positivity of the full block energy.

## References

- Truth anchor: `D5/S3/Weil/ZetaCore/CertifiedStickyMatrix.certified_sticky_matrix`
- Dependency: [D5/S3/Weil/ZetaLinear/ExactStickyReduction](../ZetaLinear/ExactStickyReduction.md)
