# Forward steps 20 through 29

## Abstract

At each index, the next cached row vector agrees with one exact sparse step.

**Theorem 1.1 (Forward steps 20 through 29).**

$$\forall k: \operatorname{\mathit{Fin}}\left(10\right), (\operatorname{\mathit{let}} i: \operatorname{\mathit{Fin}}\left(30\right) := 20 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(k\right); (\operatorname{\mathit{power}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{step}}\left(\operatorname{\mathit{power}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck2.checked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229635: width-six arrays with two monochromatic bonds*. URL: <https://oeis.org/A229635/internal>.

*Commentary.*

At each index, the next cached row vector agrees with one exact sparse step.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635PowerCheck2.checked`
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Powers](HardinA229635Powers.md)
