# Reputation Sufficiency Criterion

## Abstract

Reputation determines a target exactly by canonical target refinement.

**Theorem 1.1 (Reputation sufficiency is target-relative factorization).**

$$\begin{gathered}\forall X, B_{H}, S, Y: \operatorname{Type},\\{}H: X \to B_{H}, r: B_{H} \to S, T: X \to Y,\\{}R := r \circ H,\\{}((\exists p: S \to \operatorname{TargetImage}\left(T\right), \forall x, \operatorname{val}\left(p(R(x))\right) = T(x)) \Leftrightarrow \operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), R\right)) \land\\{}((\exists x, y, R(x) = R(y) \land T(x) \neq T(y)) \Rightarrow (\neg\operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), R\right) \land \operatorname{ker}\left(R\right) \neq \operatorname{ker}\left(T\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Trust/ReputationSufficiencyCriterion.reputation_sufficiency_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full history, the score map, and future trustworthiness are independent source channels. Reputation is constructed publicly as the score map composed with full history.

Exact determination exposes a predictor from score coordinates into the realized target image. Pointwise agreement of that predictor is equivalent to refinement of the canonical target readout by reputation.

A pair with the same reputation and different future trustworthiness publicly refutes target sufficiency and proves that reputation and the target induce different kernels.

The public construction R := r composed with H states directly that the score is a history compression. Its adequacy is relative to the chosen trustworthiness target.

The exact family collision theorem is applied directly. Repository and pinned-library searches found no theorem combining the target-image predictor, collision, and compression clauses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Trust/ReputationSufficiencyCriterion.reputation_sufficiency_criterion`
- Dependency: [D5/S3/ConceptDynamics/Governance/JudgmentRelativeAnalogyCriterion](../Governance/JudgmentRelativeAnalogyCriterion.md)
