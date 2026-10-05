# Silver-Slope Abelian Periods

## Abstract

The silver-slope abelian-period conjecture.

**Definition 1.1 (Peltomäki's silver-slope conjecture).**

$$\operatorname{claim}() \Leftrightarrow \operatorname{silverAbelianPeriodSet}() = \operatorname{silverCandidateSet}()$$

*Formalization.* `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods.claim` (`✓ std3`).

*Citation.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

Verbatim source sentence (p. 283, line 1722): Let $\alpha = [0; \overline{2}]$. The abelian period set of a Sturmian word of slope $\alpha$ is $\mathcal{Q}^{+}_{\alpha} \cup \mathcal{M}_{\alpha}$.

The displayed equality encodes that sentence with the literal period-set and candidate-set definitions.

**Theorem 1.2 (The silver-slope period set equality).**

$$\operatorname{silverAbelianPeriodSet}() = \operatorname{silverCandidateSet}()$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2020). *Abelian periods of factors of Sturmian words*. DOI: [10.1016/j.jnt.2020.04.007](https://doi.org/10.1016/j.jnt.2020.04.007). URL: <https://arxiv.org/abs/1905.06138>.

*Commentary.*

Every Pell denominator, twice a denominator and positive adjacent-denominator sum is realised. Singular-window packing excludes all other minimum periods.

## References

- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods.claim`
- Truth anchor: `D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods.result`
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianPeriodTerrain](SilverSlopeAbelianPeriodTerrain.md)
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianUpperInclusion](SilverSlopeAbelianUpperInclusion.md)
- Dependency: [D5/S1/Words/Mechanical/SilverSlopeAbelianWitnesses](SilverSlopeAbelianWitnesses.md)
