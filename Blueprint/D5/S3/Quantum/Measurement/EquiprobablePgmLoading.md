# The complete loading domain and the global complement

## Abstract

The complete loading domain and the global complement

**Theorem 1.1 (Full physical domain and closed activity boundary).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmLoading.loading_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmLoading.loading_classification` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

Fix 0<kappa<1 and K>1. For every t>0 with t^2<1-kappa^2 and K t^2<1, the actual symmetric matrices a=1-t^2,b=kappa t,c=1-K t^2 are strictly positive and trace one. The actual piecewise optimal POVM is feasible and uniquely maximizes success over every complex finitePOVM. Its actual nonzero-effect label set is {0,1} exactly in the closed region t<=kappa/(K-1); above it all three labels are active. Equality belongs to the two-active regime. The physical conditions here are the entire strict admissible loading domain.

**Theorem 1.2 (Exact spectral ratio on the physical interval).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmLoading.spectral_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmLoading.spectral_ratio` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every t>0 with t^2<1, the ratio D/q for a=1-t^2 and c=1-Kt^2 is 3(K+2)-(K+2)(K-1)t^2/(1-t^2). This identity is consumed by the global nonviolation theorem, where positivity and the full actual failure iff supply its semantic significance.

**Theorem 1.3 (Global nonviolation through the sharp boundary).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmLoading.global_nonviolation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmLoading.global_nonviolation` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every 0<kappa<1, 1<K<=10/3 and every admissible t>0, use the actual optimalPovm and its nonzero-effect set A. Then (|A|-1)(P_A-1/3)<=2(P_all-1/3). This includes K=10/3 and both activity regimes. The full strict failure criterion and D/q<=16 exclude violation; in the three-active region the comparison is equality.

Attribution remains separate: anonymous mechanism; old literal byline Wenlin Zhang and Haobo / trureturing; new note Haobo Ma then Wenlin Zhang. Hyunho Cha is credited for the symmetric score, qubit slice and commuting constructions. CC BY 4.0 applies only to the new note. Active means nonzero effects, including rank-one effects; the source wording about positive definite effects is ambiguous. No priority or publication claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmLoading.global_nonviolation`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmLoading.loading_classification`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmLoading.spectral_ratio`
- Dependency: [D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric](EquiprobablePgmSymmetric.md)
