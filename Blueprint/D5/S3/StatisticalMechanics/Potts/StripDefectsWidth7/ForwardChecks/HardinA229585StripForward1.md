# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

The forward table records the exact labelled weights of the 72 boundary classes.

**Theorem 1.1 (Two exact forward steps).**

$$\forall i: \operatorname{\mathit{Fin}}\left(2\right), (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(2 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right) + 1\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(2 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)\right)\right), \operatorname{\mathit{HardinA229585StripData}}.\operatorname{T}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/ForwardChecks/HardinA229585StripForward1.forward_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

The finite indices carry the displayed natural values, each less than eleven. Multiplication by the transition matrix advances the row count by one.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/ForwardChecks/HardinA229585StripForward1.forward_steps`
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](../HardinA229585StripData.md)
