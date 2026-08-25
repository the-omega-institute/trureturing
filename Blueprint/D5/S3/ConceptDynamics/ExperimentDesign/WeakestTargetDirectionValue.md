# Weakest Target-Direction Experiment Value

## Abstract

Experiment value improves the weakest target direction and maximizes finite target-pair coverage, while trace-only gain can remain target-inert.

**Theorem 1.1 (Experiments should improve weakest target directions).**

$$\begin{aligned}[\forall K, V: \operatorname{Type}, P, W, W_{a}: \operatorname{LinearEnd}\left(K, V\right), \operatorname{RCLike}\left(K\right) \land \operatorname{NormedAddCommGroup}\left(V\right) \land \operatorname{InnerProductSpace}\left(K, V\right) \land \operatorname{FiniteDimensional}\left(K, V\right) \land P \circ P = P \land \operatorname{IsSymmetric}\left(P\right) \land \operatorname{IsSymmetric}\left(W\right) \land \operatorname{IsSymmetric}\left(W_{a}\right) \land \operatorname{Nonempty}\left(\left\{x \neq 0 \land \operatorname{P}\left(x\right) = x \mid x \in V\right\}\right) \land \exists \varepsilon: \mathbb{R}, 0 < \varepsilon \land \forall x\in\left\{x \neq 0 \land \operatorname{P}\left(x\right) = x \mid x \in V\right\}, \varepsilon \leq \operatorname{Rayleigh}\left(P \circ W_{a} \circ P, x\right) \Rightarrow \operatorname{iInfRayleigh}\left(P \circ W \circ P, \left\{x \neq 0 \land \operatorname{P}\left(x\right) = x \mid x \in V\right\}\right) < \operatorname{iInfRayleigh}\left(P \circ (W + W_{a}) \circ P, \left\{x \neq 0 \land \operatorname{P}\left(x\right) = x \mid x \in V\right\}\right)] \land\\{}[\operatorname{trace}\left(0\right) < \operatorname{trace}\left(0 + \operatorname{diag}\left(0, 1\right)\right) \land \operatorname{diag}\left(1, 0\right) \circ 0 \circ \operatorname{diag}\left(1, 0\right) = \operatorname{diag}\left(1, 0\right) \circ (0 + \operatorname{diag}\left(0, 1\right)) \circ \operatorname{diag}\left(1, 0\right) \land \exists x, y: \operatorname{Fin}\left(2\right) \to \mathbb{R}, \operatorname{x}\left(0\right) \neq \operatorname{y}\left(0\right) \land \operatorname{mulVec}\left(\operatorname{diag}\left(1, 0\right) \circ (0 + \operatorname{diag}\left(0, 1\right)) \circ \operatorname{diag}\left(1, 0\right), x\right) = \operatorname{mulVec}\left(\operatorname{diag}\left(1, 0\right) \circ (0 + \operatorname{diag}\left(0, 1\right)) \circ \operatorname{diag}\left(1, 0\right), y\right)] \land\\{}[\forall X, C, R, Y, A: \operatorname{Type}, q: X \to C, e: A \to X \to R, t: X \to Y, \operatorname{Fintype}\left(X\right) \land \operatorname{Fintype}\left(A\right) \land \operatorname{Nonempty}\left(A\right) \Rightarrow \exists b: A, \forall a: A, \operatorname{ncard}\left(\operatorname{experimentGain}\left(q, \operatorname{e}\left(a\right), t\right)\right) \leq \operatorname{ncard}\left(\operatorname{experimentGain}\left(q, \operatorname{e}\left(b\right), t\right)\right)].\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/WeakestTargetDirectionValue.weakest_target_direction_experiment_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite-dimensional real or complex inner-product space, the target projection is idempotent and symmetric, and both Gram operators are symmetric. A uniform positive Rayleigh gain on every nonzero target direction raises the infimum Rayleigh score strictly.

The displayed two-dimensional matrices give the contrast clause. The added operator raises trace in the second coordinate, but target compression to the first coordinate is unchanged and still merges states with distinct first coordinates.

For finite state and candidate types, experimentGain is the canonical set of current target defects removed by a candidate. Finite maximization constructs a candidate whose covered-pair cardinality is maximal.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/WeakestTargetDirectionValue.weakest_target_direction_experiment_value`
- Dependency: [D5/S3/ConceptDynamics/Experiments/ExperimentRefinementGainMonotone](../Experiments/ExperimentRefinementGainMonotone.md)
