# Fixed-layer source components

## Abstract

FixedLayerRootAsymptotic

The module supplies fixed-layer asymptotic and shrinking-roster components. These components do not establish the final uniform paid-prefix repair, its uniform original-price consumer or an elementary-energy consumer. RegUNVALIDATED under issue 28966: faithful full-telescope typed Reg attempts are present; lawful families, whole-family variation, sensitivity, observational dependence and exact source binding remain unfinished.

**Theorem 1.1 (fixed layer root offset tendsto).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/FixedLayerRootAsymptotic.fixed_layer_root_offset_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/FixedLayerRootAsymptotic.fixed_layer_root_offset_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete candidate Lean telescope: theorem fixed_layer_root_offset_tendsto {j : ℕ} (hj : 2 ≤ j) :     Tendsto (fun X : ℝ => (j : ℝ) * log (cutoff j (referencePrice X)) - log X)       atTop (𝓝 (log (j : ℝ)))

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/FixedLayerRootAsymptotic.fixed_layer_root_offset_tendsto`
- Dependency: [D5/S3/Arith/GoldenResource/ActualReserve/ActualReservePrimeMask](../../GoldenResource/ActualReserve/ActualReservePrimeMask.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff](HigherLayerClampedCutoff.md)
