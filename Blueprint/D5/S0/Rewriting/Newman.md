# Newman Normal Forms

## Abstract

Terminating locally confluent rewrite systems have unique reachable normal forms.

**Theorem 1.1 (Unique reachable normal forms).**

$$\operatorname{WellFounded}(\operatorname{swap}(r)) \land (\forall h, a, b, r(h, a) \land r(h, b) \Rightarrow \exists c, \operatorname{ReflTransGen}(r)(a, c) \land \operatorname{ReflTransGen}(r)(b, c)) \Rightarrow \forall h, \exists! n, \operatorname{ReflTransGen}(r)(h, n) \land \neg\exists x, r(n, x).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Newman.newman_unique_normal_form` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

For every terminating and locally confluent rewrite relation, each starting history reaches exactly one irreducible normal form through the reflexive transitive closure of the relation.

Newman 1942, literature-attested; this repository gives a direct proof because the pinned Mathlib version does not provide this lemma.

## References

- Truth anchor: `D5/S0/Rewriting/Newman.newman_unique_normal_form`
