# Domain Immunization Audit

## Abstract

Target-dependent domain restriction can erase admitted defects while deleting empirical states.

**Theorem 1.1 (Domain immunization requires deletion and dependence audits).**

$$\begin{gathered}(\forall X, B, Y: \operatorname{Type}, [\operatorname{Finite}\left(X\right)],\\{}C: X \to B, T: X \to Y,\\{}\operatorname{Nonempty}\left(\operatorname{Defect}\left(C, T\right)\right) \Rightarrow \exists z: X \times X, \exists A: \operatorname{Set}\left(X\right),\\{}z \in \operatorname{Defect}\left(C, T\right) \land A = \operatorname{singleton}\left(\operatorname{fst}\left(z\right)\right) \land\\{}\operatorname{Defect}\left(\operatorname{restrict}\left(C, A\right), \operatorname{restrict}\left(T, A\right)\right) = \emptyset \land \operatorname{ncard}\left(A\right) = 1 \land\\{}\operatorname{ncard}\left(\operatorname{compl}\left(A\right)\right) = \operatorname{NatCard}\left(X\right) - 1) \land\\{}(Czero = \operatorname{constant}\left(unit\right), Tzero = id, Azero = \{x \mid Tzero(x) = false\}:\\{}\operatorname{Nonempty}\left(\operatorname{Defect}\left(Czero, Tzero\right)\right) \land \operatorname{Defect}\left(\operatorname{restrict}\left(Czero, Azero\right), \operatorname{restrict}\left(Tzero, Azero\right)\right) = \emptyset \land\\{}\operatorname{ncard}\left(Azero\right) = 1 \land \operatorname{ncard}\left(\operatorname{compl}\left(Azero\right)\right) = 1 \land\\{}\forall x: Bool, x \in Azero \iff Tzero(x) = false) \land\\{}(\forall S: \operatorname{Type}, E: \mathbb{N} \to \operatorname{Set}\left(S\right),\\{}\operatorname{Monotone}\left(E\right) \Rightarrow \exists M: \mathbb{N} \to \operatorname{Set}\left(S\right),\\{}(\forall n, M(n) = \operatorname{compl}\left(E(n)\right)) \land \operatorname{Antitone}\left(M\right) \land\\{}(\forall n, \operatorname{inter}\left(M(n), E(n)\right) = \emptyset) \land\\{}(\forall n, E(n) \subset E(n + 1) \Rightarrow M(n + 1) \subset M(n))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/DomainImmunizationAudit.domain_immunization_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every defective readout on a finite state carrier, a witnessed target collision selects a singleton admitted domain. The restricted readout has empty target defect, and the displayed complement count records exactly how many states were deleted.

The Boolean clause is the required contrast model: the constant readout has a full-domain target defect, while the target-defined one-state domain has none. Both retained and deleted counts are explicit.

For a cumulative family of counterexamples, the admitted domains are their complements. They remain disjoint from all current counterexamples, are antitone, and shrink strictly whenever the counterexample set grows strictly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/DomainImmunizationAudit.domain_immunization_audit`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
