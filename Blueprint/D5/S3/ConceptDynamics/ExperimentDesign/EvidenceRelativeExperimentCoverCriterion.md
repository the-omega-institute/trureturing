# Evidence-Relative Experiment Cover Criterion

## Abstract

Finite experiment selection identifies a target exactly by covering the ordered pairs unresolved by current evidence.

**Theorem 1.1 (Target identification is ordered-pair cover).**

$$\begin{aligned}\forall Model, Experiment, Evidence, Target: \operatorname{Type},\\Response: Experiment \to \operatorname{Type}, A0: \operatorname{Finset}\left(Experiment\right),\\E: Model \to Evidence, Ea: \forall a: Experiment, Model \to Response\left(a\right),\\T: Model \to Target,\\\operatorname{FactorsThrough}\left(T, (m \mapsto (E\left(m\right), \operatorname{jointReadout}\left(\operatorname{restrict}\left(Ea, A0\right), m\right)))\right) \iff \\\{p \in Model \times Model \mid E\left(\operatorname{fst}\left(p\right)\right) = E\left(\operatorname{snd}\left(p\right)\right) \land T\left(\operatorname{fst}\left(p\right)\right) \ne T\left(\operatorname{snd}\left(p\right)\right)\} \subseteq \operatorname{Union}\left(a \in A0, \{p \in Model \times Model \mid \left(E\left(\operatorname{fst}\left(p\right)\right) = E\left(\operatorname{snd}\left(p\right)\right) \land T\left(\operatorname{fst}\left(p\right)\right) \ne T\left(\operatorname{snd}\left(p\right)\right)\right) \land Ea\left(a\right)\left(\operatorname{fst}\left(p\right)\right) \ne Ea\left(a\right)\left(\operatorname{snd}\left(p\right)\right)\}\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/EvidenceRelativeExperimentCoverCriterion.evidence_relative_experiment_cover_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current evidence, dependent experiment readouts, and target are source primitives on one model carrier. The selected experiment interface is the canonical dependent joint readout.

The left set contains ordered model pairs with equal current evidence and unequal target values. Each selected experiment contributes the members of that same set whose experiment responses differ.

Target factorization through current evidence paired with the selected joint readout is equivalent to coverage of every unresolved ordered pair. The argument does not require the model carrier itself to be finite.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/EvidenceRelativeExperimentCoverCriterion.evidence_relative_experiment_cover_criterion`
- Dependency: [D5/S3/ConceptDynamics/Experiment/FiniteExperimentCoverCriterion](../Experiment/FiniteExperimentCoverCriterion.md)
