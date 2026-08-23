# Left-Invertible Processes Recover All Targets

## Abstract

A left-invertible process recovers every target, while a nonconstant target can survive without left invertibility.

**Lemma 1.1 (Identity erasure preserves a nontrivial value).**

$$\begin{gathered}(\neg \exists R: Bool \to Bool \times Bool, \operatorname{LeftInverse}\left(R, eraseIdentity\right)) \land\\{}\exists recover: Bool \to \mathbb{N},\\{}retainedValue = recover \circ eraseIdentity \land\\{}retainedValue((false, false)) \neq retainedValue((true, false)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reversibility/LeftInvertibleRecoversAllTargets.identity_erasure_preserves_nontrivial_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projecting a pair of Booleans to its first coordinate cannot have a left inverse: the two states with first coordinate false and different identity coordinates have the same image.

Nevertheless, the numerical target that assigns zero or one from the retained first coordinate factors through this projection. It distinguishes a false-valued state from a true-valued state, so the preserved target is genuinely nonconstant.

**Theorem 1.2 (A left inverse recovers every target).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}U: X \to B, R: B \to X,\\{}\operatorname{LeftInverse}\left(R, U\right) \Rightarrow\\{}(\forall Y: \operatorname{Type}, T: X \to Y,\\{}T = (T \circ R) \circ U \land \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), U\right)) \land\\{}((\neg \exists R: Bool \to Bool \times Bool, \operatorname{LeftInverse}\left(R, eraseIdentity\right)) \land\\{}\exists recover: Bool \to \mathbb{N},\\{}retainedValue = recover \circ eraseIdentity \land\\{}retainedValue((false, false)) \neq retainedValue((true, false))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reversibility/LeftInvertibleRecoversAllTargets.left_invertible_recovers_all_targets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If R is a left inverse of a process U, every target T is recovered by applying T after R to the process output. Consequently the canonical readout of T factors through U, so it refines U.

This conclusion covers every target codomain and also the empty-state case. The accompanying finite witness shows the converse fails for preservation of a particular target: erasing identity is not left-invertible even though it preserves a nonconstant value.

The refinement conclusion uses the repository's universal sufficiency factorization theorem. The finite obstruction uses the fact that a map with a left inverse is injective.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Reversibility/LeftInvertibleRecoversAllTargets.identity_erasure_preserves_nontrivial_value`
- Truth anchor: `D5/S3/ConceptDynamics/Reversibility/LeftInvertibleRecoversAllTargets.left_invertible_recovers_all_targets`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
