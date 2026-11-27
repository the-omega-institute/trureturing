# Canonical record harmonic defect

## Abstract

A weighted harmonic sum bounds the complete defect of the canonical strict record and gives little-o decay relative to log X/X².

**Theorem 1.1 (Harmonic bound for the combined higher loss).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_higher_loss_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_higher_loss_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be real with X ≥ max(exp(4), 729). Set q = referencePrice(X) = 1/(X log X), μ = firstLayerPrice(X + 1) = log(1 + 1/(X + 1))/log(X + 1), and m = strictInteger(μ). Write B = 6 log 2 + 1 + log(6 log X). The sum completeSecondLayerLoss(X, m) + completeHigherLayerLoss(X, m) lies between 0 and 3B/X², inclusive.

The relative price bracket uses the prices (1 ± 3/X)q. Every active layer j ≥ 2 has a half-open cutoff interval of width at most 27/√X ≤ 1, so at most one prime crosses in that layer. The lower-price cutoff is at most 2X^(1/j) and active layers have j < 6 log X. Charge the crossing log p ≤ log 2 + log X/j and sum these weights up to the integer part of 6 log X. The harmonic-number estimate gives total mass at most (log X)B. The inventory at q is contained in the inventory at μ. Each additional coordinate costs at most (q − μ) log p and q − μ ≤ 3q/X. Multiplying by the mass bound gives 3B/X².

**Theorem 1.2 (Harmonic bound for the complete defect).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_harmonic_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_harmonic_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real X ≥ max(exp(4), 729), set m = strictInteger(firstLayerPrice(X + 1)), D = actualDefect(X, m) and R = D − completeFirstLayerLoss(X, m). With B = 6 log 2 + 1 + log(6 log X), the residual satisfies 0 ≤ R ≤ 3B/X² and the complete defect satisfies 0 ≤ D ≤ (3B + 7/4)/X². The decomposition of D identifies R with the combined loss from layers two and higher. The canonical record power bound gives completeFirstLayerLoss(X, m) ≤ (7/4)/X² for the same strict optimizer.

**Theorem 1.3 (Little-o decay of the combined higher loss).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_higher_loss_isLittleO`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_higher_loss_isLittleO` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real X tending to positive infinity and m = strictInteger(firstLayerPrice(X + 1)), completeSecondLayerLoss(X, m) + completeHigherLayerLoss(X, m) is little-o of log X/X². Dividing the harmonic bound by log X/X² gives a sum of a constant divided by log X and 3 log(log X)/log X, which both tend to zero.

**Theorem 1.4 (Little-o decay of the complete defect).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_defect_isLittleO`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_defect_isLittleO` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As real X tends to positive infinity, actualDefect(X, strictInteger(firstLayerPrice(X + 1))) is little-o of log X/X². The first-layer allowance contributes at most 7/(4 log X) to the normalized bound and therefore tends to zero as well.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_defect_isLittleO`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_harmonic_defect`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_higher_loss_bound`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CanonicalRecordHarmonicDefect.canonical_record_higher_loss_isLittleO`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/CanonicalRecordPowerDefect](CanonicalRecordPowerDefect.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff](HigherLayerClampedCutoff.md)
