# Principal Classes and Faithful Prime Counts

## Abstract

The class map detects principality, while every integer prime count detects ideals.

**Theorem 1.1 (The trivial ideal class is exactly the principal locus).**

$$\forall R, K, I,\\{}\operatorname{CommRing}\left(R\right) \land \operatorname{IsDomain}\left(R\right) \land \operatorname{Field}\left(K\right) \land \operatorname{Algebra}\left(R, K\right) \land \operatorname{IsFractionRing}\left(R, K\right) \Rightarrow (\operatorname{IsPrincipal}\left(\operatorname{Submodule}\left(R, K, I\right)\right) \iff \operatorname{ClassGroupMk}\left(K, I\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/IdealClassGroups/PrincipalIdealCriterion.principal_ideal_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the orientation matching the source statement of Mathlib's ClassGroup.mk_eq_one_iff. No Dedekind-domain assumption is added: the upstream interface requires a domain and a chosen field of fractions.

## References

- Truth anchor: `D5/S3/Factorization/IdealClassGroups/PrincipalIdealCriterion.principal_ideal_criterion`
