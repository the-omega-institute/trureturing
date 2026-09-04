# Testing Tower Structure Membership

## Abstract

The testing tower satisfies its carrier, valuation, and two-height classification clauses.

**Lemma 1.1 (The testing tower is a multi-filtration naming system).**

$$\begin{gathered}\forall O: \operatorname{Type},\\{}[\operatorname{Finite}\left(O\right)], [\operatorname{Nontrivial}\left(O\right)],\\{}[\operatorname{TopologicalSpace}\left(\mathbb{N} \to O\right)], [\operatorname{PolishSpace}\left(\mathbb{N} \to O\right)],\\{}[\operatorname{MeasurableSpace}\left(\mathbb{N} \to O\right)], [\operatorname{BorelSpace}\left(\mathbb{N} \to O\right)],\\{}[\operatorname{Uncountable}\left(\mathbb{N} \to O\right)],\\{}\forall o0: O, decode: \mathbb{N} \to \left(\mathbb{N} \to O\right),\\{}input: \mathbb{N},\\{}code: \operatorname{TestingName}\left(O\right) \to \operatorname{List}\left(Bool\right), programCost: \mathbb{N} \to \mathbb{N},\\{}\mu: \operatorname{Measure}\left(\mathbb{N} \to O\right),\\{}[\operatorname{NullSingletonClass}\left(\mu\right)], [\operatorname{SigmaFinite}\left(\mu\right)],\\{}\operatorname{Injective}\left(code\right) \Rightarrow \operatorname{withMeasureSpace}\left(\mu, (\operatorname{Countable}\left(\operatorname{TestingName}\left(O\right)\right) \land\\{}(\forall p: \mathbb{N}, \operatorname{isSome}\left(\operatorname{testingAssignment}\left(o0, decode, input, \operatorname{inr}\left(p\right)\right)\right) \iff \operatorname{Dom}\left(\operatorname{eval}\left(\operatorname{ofNatCode}\left(p\right), input\right)\right)) \land\\{}\neg \operatorname{ComputablePred}\left((c: PartrecCode \mapsto \operatorname{isSome}\left(\operatorname{testingAssignment}\left(o0, decode, input, \operatorname{inr}\left(\operatorname{encodeCode}\left(c\right)\right)\right)\right))\right) \land\\{}(\forall Q: \mathbb{N}, \operatorname{Finite}\left(\left\{\operatorname{length}\left(\operatorname{code}\left(a\right)\right) \leq Q \mid a \in \operatorname{TestingName}\left(O\right)\right\}\right)) \land\\{}\operatorname{Infinite}\left(\left\{\operatorname{testingExecutionCost}\left(programCost, a\right) \leq 1 \mid a \in \operatorname{TestingName}\left(O\right)\right\}\right) \land\\{}(\forall Q: \mathbb{N}, \operatorname{Finite}\left(\left\{\operatorname{length}\left(\operatorname{code}\left(a\right)\right) + \operatorname{natLog}\left(2, \operatorname{testingExecutionCost}\left(programCost, a\right)\right) \leq Q \mid a \in \operatorname{TestingName}\left(O\right)\right\}\right)) \land\\{}\mu\left(\operatorname{named}\left(\operatorname{primary}\left(\operatorname{testingTower}\left(o0, decode, input, code, programCost, \mu\right)\right)\right)\right) = 0)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/TestingTowerStructureMembership.testing_tower_has_multi_filtration_membership` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the sequence space over a finite nontrivial output type, with its Polish and Borel structures and an explicitly supplied atomless sigma-finite measure.

The constructed assignment retains the default table extension. The public clauses expose countability of the exact TestingName carrier, the noncomputable halting domain of program names, finite description-length sublevels, an infinite execution-cost sublevel, finite mixed-cost sublevels, and the null named image.

The constructed tower wraps NamingSystem as its primary coordinate and uses the execution-cost model as its secondary coordinate. The proof applies the three standalone prerequisites and the frozen dark-side conservation owner.

## References

- Truth anchor: `D5/S0/Naming/TestingTowerStructureMembership.testing_tower_has_multi_filtration_membership`
- Dependency: [D5/S0/Naming/MultiFiltrationNamingSystem](MultiFiltrationNamingSystem.md)
- Dependency: [D5/S0/Naming/TestingCostClassification](TestingCostClassification.md)
- Dependency: [D5/S0/Naming/TestingTowerValuation](TestingTowerValuation.md)
