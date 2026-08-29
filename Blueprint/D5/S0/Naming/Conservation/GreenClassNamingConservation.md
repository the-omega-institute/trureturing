# Green-Class Mass and Naming Conservation

## Abstract

Uniform Green mass and countable-name conservation share one product carrier.

**Theorem 1.1 (Finite certificates retain mass while countable names remain null).**

$$\begin{gathered}\forall O: \operatorname{Type},\\{}[\operatorname{Fintype}(O)], [\operatorname{Nonempty}(O)], [\operatorname{Nontrivial}(O)],\\{}[\operatorname{MeasurableSpace}(O)], [\operatorname{MeasurableSingletonClass}(O)],\\{}[\operatorname{TopologicalSpace}(O)], [\operatorname{DiscreteTopology}(O)],\\{}\forall S: \operatorname{Finset}\left(\mathbb{N}\right), t: \mathbb{N} \to O,\\{}\mu:=\operatorname{stringMeasure}\left(O\right),\\{}\forall J: \operatorname{Type}, [\operatorname{Countable}(J)],\\{}\forall systems: J \to \operatorname{NamingSystem}\left(\mathbb{N} \to O\right),\\{}\mu(\operatorname{greenClass}\left(S, t\right)) = \operatorname{inv}\left(\operatorname{card}\left(O\right)\right)^{\operatorname{card}\left(S\right)} \land \\{}0 < \mu(\operatorname{greenClass}\left(S, t\right)) \land \\{}\operatorname{Countable}\left(\operatorname{iUnion}\left(\Lambda j \mapsto \operatorname{named}\left(\operatorname{systems}\left(j\right)\right)\right)\right) \land \\{}\mu(\operatorname{iUnion}\left(\Lambda j \mapsto \operatorname{named}\left(\operatorname{systems}\left(j\right)\right)\right)) = 0 \land \\{}\mu(\operatorname{iUnion}\left(\Lambda j \mapsto \operatorname{named}\left(\operatorname{systems}\left(j\right)\right)\right)^{c}) = 1 \land \\{}\forall j: J, Q: \mathbb{N}, \mu(\left\{\exists a: \operatorname{Name}\left(\operatorname{systems}\left(j\right)\right), a \in \operatorname{layer}\left(\operatorname{systems}\left(j\right), Q\right) \land \operatorname{assignment}\left(\operatorname{systems}\left(j\right), a\right) = \operatorname{some}\left(x\right) \mid x \in \mathbb{N} \to O\right\}^{c}) = 1.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/Conservation/GreenClassNamingConservation.green_class_naming_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let O be a finite nontrivial discrete measurable alphabet and equip the sequence space N -> O with the canonical uniform product probability measure stringMeasure O. A finite support S and target t determine the canonical greenClass S t.

The green class has mass exactly (card O)^(-1) raised to card S and that mass is positive. Thus the value depends on the certificate budget and not on the pinned content.

For every countably indexed family of canonical NamingSystem values, the union of named images is countable and null, while its complement has measure one. For every system and every height budget, the complement of the corresponding finite layer image also has measure one.

The exact cylinder calculation and positivity are supplied by the frozen GreenClassMeasure declarations. The frozen NamingTowerConservation declaration supplies countability, nullity, and full-measure complement. Atomlessness of the same product measure follows from the imported critical-diameter estimate; probability normalization then also proves the sequence carrier uncountable.

## References

- Truth anchor: `D5/S0/Naming/Conservation/GreenClassNamingConservation.green_class_naming_conservation`
- Dependency: [D5/S0/Asymptotics/MetricGeometry/GreenClassHausdorffDimension](../../Asymptotics/MetricGeometry/GreenClassHausdorffDimension.md)
- Dependency: [D5/S0/Naming/Conservation/NamingTowerConservation](NamingTowerConservation.md)
- Dependency: [D5/S0/Naming/GreenClassMeasure](../GreenClassMeasure.md)
