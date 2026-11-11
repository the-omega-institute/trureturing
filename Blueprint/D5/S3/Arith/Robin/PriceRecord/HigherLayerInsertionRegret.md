# D5 source compiled; RegUNVALIDATED

## Abstract

HigherLayerInsertionRegret

The D5 source target has a current scoped Lean build. The Reg mirror remains unvalidated for compiler/kernel audit, lawful registration, source occurrence binding and official/RH acceptance; no literature novelty or consensus claim is made. Every public declaration below has a faithful full-telescope typed Reg attempt. The terminal elementary coercivity snapshot and completed D5 producers retain their attribution; no proof escapes or external target suppliers are introduced.

**Theorem 1.1 (insertion regret).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/HigherLayerInsertionRegret.insertion_regret`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/HigherLayerInsertionRegret.insertion_regret` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source header: theorem insertion_regret {j p : ℕ} (hj : 2 ≤ j) (hp : p.Prime)     {u priceLambda κ : ℝ} (hu : 2 ≤ u) (hLambda : 0 < priceLambda) (hroot : beta j u = priceLambda)     (hκ : 0 ≤ κ) (hpu : u ≤ (p : ℝ)) (hup : (p : ℝ) ≤ u * (1 + κ)) :     0 ≤ priceLambda - goldenLayerMarginal p j ∧       priceLambda - goldenLayerMarginal p j ≤ 2 * j * κ * priceLambda

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/HigherLayerInsertionRegret.insertion_regret`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff](HigherLayerClampedCutoff.md)
