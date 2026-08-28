# Common-Prior Posterior Agreement

## Abstract

Commonly known posteriors from a positive finite common prior agree.

**Theorem 1.1 (Commonly known posterior values agree).**

$$\operatorname{Finite}(\omega), [\operatorname{DecidableEq}(\omega)], \mu: \omega \to \mathbb{R},\\{}(\forall w \in \omega, 0 < \operatorname{apply}(\mu, w)), \sum_{w \in \omega} \operatorname{apply}(\mu, w) = 1,\\{}E, K \subseteq \omega, K \neq \emptyset,\\{}\pi_{1}, \pi_{2} \in \operatorname{Finpartition}(K),\\{}\operatorname{mass}(C) = \sum_{w \in C} \operatorname{apply}(\mu, w), \operatorname{eventMass}(E, C) = \sum_{w \in C, w \in E} \operatorname{apply}(\mu, w), \operatorname{post}(E, C) = \frac{\operatorname{eventMass}(E, C)}{\operatorname{mass}(C)},\\{}\forall C \in \operatorname{parts}(\pi_{1}), \operatorname{post}(E, C) = a,\\{}\forall C \in \operatorname{parts}(\pi_{2}), \operatorname{post}(E, C) = b\\{}\Rightarrow a = b.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationOrder/CommonPriorPosteriorAgreement.common_knowledge_posteriors_agree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The world type is finite and mu is a strictly positive normalized common prior. The event E and nonempty common-knowledge cell K are finite subsets of that exact world carrier.

Each information structure is a finite partition of K. This is the restriction of the agent's information partition to the common-knowledge cell; closure of a common-knowledge cell makes every such part a whole information cell.

The posterior on a cell C is constructed as common-prior mass of E inside C divided by common-prior mass of C. Strict positivity and nonempty partition parts make every denominator positive.

Summing the constant posterior identity over either partition gives the same event mass on K: a times mu(K) for the first agent and b times mu(K) for the second. Since mu(K) is positive, a equals b.

Repository and pinned Mathlib searches found no exact common-prior agreement theorem. The proof directly applies Mathlib's canonical finite-partition union and disjoint-sum machinery.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationOrder/CommonPriorPosteriorAgreement.common_knowledge_posteriors_agree`
