# Width-five HDA transfer

## Abstract

Exact width-five HDA transfer.

**Theorem 1.1 (Exact successor count).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass3.transition_counts`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass3.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

For every actual row p : Fin 5 to Fin 3 and residual d : Fin 2 satisfying Valid, the number of successor rows r whose horizontal and cross-bond defects fit d and whose new residual class is 3 equals T (cl p d) 3. Finite kernel evaluation checks this exact column of the 20 by 20 transfer. The combined successor identity applies this column in its corresponding target case.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripClass3.transition_counts`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData](HardinA229531StripData.md)
