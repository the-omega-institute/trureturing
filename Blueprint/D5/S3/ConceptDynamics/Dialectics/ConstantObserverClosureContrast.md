# Constant Observer Closure Contrast

## Abstract

A constant observer can be dynamically closed while losing state and target distinctions.

**Theorem 1.1 (Constant closure can be coarse).**

$$\begin{gathered}\forall X: \operatorname{Type}, [\operatorname{Nontrivial}\left(X\right)] \Rightarrow\\{}\forall F: X \to X,\\{}\operatorname{EffectiveDescent}\left((x \mapsto ()), F\right) \land\\{}(\forall x, y: X, \neg \operatorname{IsCarryWitness}\left((x \mapsto ()), F, (x \mapsto ()), x, y\right)) \land\\{}\neg \operatorname{Injective}\left((x \mapsto ())\right) \land\\{}(\forall Target: \operatorname{Type}, T: X \to Target, (\exists x, y: X, T(x) \neq T(y)) \Rightarrow \neg \operatorname{FactorsThrough}\left(T, (x \mapsto ())\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Dialectics/ConstantObserverClosureContrast.constant_observer_closure_can_be_coarse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state carrier is arbitrary but nontrivial, and the dynamics is an arbitrary self-map. The observer is the actual constant map into the one-point type.

The first two public clauses apply the frozen deterministic-interface equivalence to give effective descent and absence of every carry witness for the same observer and dynamics.

The remaining public clauses report the other dimensions separately: the observer is noninjective, and every target that distinguishes a state pair is not sufficient through this observer.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Dialectics/ConstantObserverClosureContrast.constant_observer_closure_can_be_coarse`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](DeterministicInterfaceEquivalence.md)
