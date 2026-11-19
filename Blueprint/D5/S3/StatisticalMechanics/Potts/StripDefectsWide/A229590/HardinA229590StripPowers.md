# Five-row one-defect strips

## Abstract

Five-row HA arrays with exactly one equal-colour bond.

The zero-defect powers and their polynomial relation determine the second summand. The one-defect suffix vectors determine the first summand.

**Theorem 1.1 (powers table).**

$$\forall (k: \operatorname{Fin}\left(19\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229590StripData}.\operatorname{T}\left(\right)^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, \operatorname{HardinA229590StripData}.\operatorname{terminal}\left(\right)\right) = \operatorname{Sum}.\operatorname{elim}\left(\operatorname{HardinA229590StripData}.\operatorname{U}\left(k\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA233260Literal}.\operatorname{Q}\left(\right)^{\operatorname{Fin}.\operatorname{val}\left(k\right)}, (1: \operatorname{Fin}\left(41\right) \to \operatorname{Int})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripPowers.powers_table` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

The first summand records exactly one defect over the suffix; the second summand uses the original zero-defect matrix powers.

**Theorem 1.2 (power polynomial).**

$$\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229590StripData}.\operatorname{T}\left(\right)^{4 + 14}, \operatorname{HardinA229590StripData}.\operatorname{terminal}\left(\right)\right) = \sum_{j: \operatorname{Fin}\left(14\right)} (\operatorname{HSMul}.\operatorname{hSMul}\left(\begin{pmatrix}(-64)&768&(-3648)&8336&(-7472)&(-5464)&18879&(-14888)&(-816)&9016&(-6494)&2200&(-384)&32\end{pmatrix}\left(j\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HardinA229590StripData}.\operatorname{T}\left(\right)^{4 + \operatorname{Fin}.\operatorname{val}\left(j\right)}, \operatorname{HardinA229590StripData}.\operatorname{terminal}\left(\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripPowers.power_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229590: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229590>.

*Commentary.*

The degree-fourteen polynomial is the square of the degree-seven polynomial of Q. Its vector relation holds after four steps.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripPowers.power_polynomial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripPowers.powers_table`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../../../../Combinatorics/TraceAvoidingArrays/TransferMatrix.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut](HardinA229590StripCut.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](HardinA229590StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripInjection](HardinA229590StripInjection.md)
