# Visible-Suite and Fresh-Checkpoint Dichotomy

## Abstract

Visible-suite reward optimization and fresh product checkpoints have different deployment force.

**Theorem 1.1 (Judgment origin separates visible optimization from fresh certification).**

$$\begin{gathered}\forall Input, Output: \operatorname{Type},\\{}[\operatorname{MeasurableSpace}(Input)], [\operatorname{MeasurableSingletonClass}(Input)], [\operatorname{Countable}(Input)], [\operatorname{DecidableEq}(Input)], [\operatorname{DecidableEq}(Output)],\\{}\forall \mathcal{D}: \operatorname{PMF}(Input), xStar: Input \to Output,\\{}\forall opposite: Output \to Output, (\forall y: Output, opposite(y) \neq y),\\{}\forall m: \mathbb{N}, T_{train}: \operatorname{Fin}(m) \to Input,\\{}\forall programCost: \operatorname{VisibleSuiteProgram}(Input, m) \to \mathbb{N}, suiteComplexity: (\operatorname{Fin}(m) \to Input) \to \mathbb{N}, overhead: \mathbb{N},\\{}\forall compiler: \operatorname{LookupCompiler}(\operatorname{Fin}(m) \to Input, \operatorname{VisibleSuiteProgram}(Input, m), (Q: \operatorname{VisibleSuiteProgram}(Input, m) \mapsto (Tprime: \operatorname{Fin}(m) \to Input \mapsto \operatorname{suite}(Q) = Tprime)), programCost, suiteComplexity, overhead),\\{}\forall P_{frozen}: Input \to Output, epsilon: \mathbb{R},\\{}0 \leq epsilon \land epsilon \leq 1 \land epsilon \leq \operatorname{real}(\operatorname{toMeasure}(\mathcal{D}), \left\{P_{frozen}(x) \neq xStar(x) \mid x \in Input\right\}) \Rightarrow\\{}programCost(\operatorname{VisibleSuiteProgram}(T_{train})) \leq suiteComplexity(T_{train}) + overhead \land\\{}(\forall j: \operatorname{Fin}(m), \operatorname{run}(xStar, opposite, \operatorname{VisibleSuiteProgram}(T_{train}))(T_{train}(j)) = xStar(T_{train}(j))) \land\\{}\operatorname{suiteReward}(xStar, \operatorname{run}(xStar, opposite, \operatorname{VisibleSuiteProgram}(T_{train})), T_{train}) = m \land\\{}(\forall P: Input \to Output, \operatorname{suiteReward}(xStar, P, T_{train}) \leq \operatorname{suiteReward}(xStar, \operatorname{run}(xStar, opposite, \operatorname{VisibleSuiteProgram}(T_{train})), T_{train})) \land\\{}\operatorname{real}(\operatorname{toMeasure}(\mathcal{D}), \left\{\operatorname{run}(xStar, opposite, \operatorname{VisibleSuiteProgram}(T_{train}))(x) \neq xStar(x) \mid x \in Input\right\}) = \operatorname{real}(\operatorname{toMeasure}(\mathcal{D}), \operatorname{compl}(\operatorname{observedInputs}(\operatorname{VisibleSuiteProgram}(T_{train})))) \land\\{}\operatorname{real}(\operatorname{pi}((j: \operatorname{Fin}(m) \mapsto \operatorname{toMeasure}(\mathcal{D}))), \left\{\forall j: \operatorname{Fin}(m), P_{frozen}(T(j)) = xStar(T(j)) \mid T \in \operatorname{Fin}(m) \to Input\right\}) = \operatorname{real}(\operatorname{toMeasure}(\mathcal{D}), \left\{P_{frozen}(x) = xStar(x) \mid x \in Input\right\})^{m} \land\\{}\operatorname{real}(\operatorname{pi}((j: \operatorname{Fin}(m) \mapsto \operatorname{toMeasure}(\mathcal{D}))), \left\{\forall j: \operatorname{Fin}(m), P_{frozen}(T(j)) = xStar(T(j)) \mid T \in \operatorname{Fin}(m) \to Input\right\}) \leq \operatorname{exp}(-(epsilon \times (m: \mathbb{R}))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interpretation/VisibleSuiteFreshCheckpointDichotomy.visible_suite_and_fresh_checkpoint_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A visible-suite program carries the training suite that selected it. Its behavior agrees with the expected output on every observed input and uses a supplied fixed-point-free alternative off that finite image.

The source objective contains only the number of passed training checks. The lookup program attains every check and therefore maximizes that unregularized reward, while its deployment loss is exactly the mass outside the observed image.

The canonical lookup compiler identifies this program as the unique program consistent with its suite record. The frozen spectrum-bottom theorem then gives the suite-description bound with fixed overhead.

A separate implementation is fixed before the checkpoint tuple is sampled. The tuple law is the joint product of the deployment law, so the frozen fresh-checkpoint theorem gives both the exact all-pass mass and its exponential envelope.

The source's multi-version observations are empirical context and are not asserted as universal theorem clauses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interpretation/VisibleSuiteFreshCheckpointDichotomy.visible_suite_and_fresh_checkpoint_dichotomy`
- Dependency: [D5/S0/Computability/DescriptionComplexity/LookupProgramUpperBound](../../../S0/Computability/DescriptionComplexity/LookupProgramUpperBound.md)
- Dependency: [D5/S3/ConceptDynamics/Interpretation/FreshIndependentCheckpointGuarantee](FreshIndependentCheckpointGuarantee.md)
