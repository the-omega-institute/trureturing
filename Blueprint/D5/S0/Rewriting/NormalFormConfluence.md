# Normal Form Confluence

## Abstract

Confluence makes reachable and equivalent normal forms unique.

**Theorem 1.1 (Reachable normal forms are unique).**

$$(\forall h, a, b, \operatorname{ReflTransGen}(r)(h, a) \land \operatorname{ReflTransGen}(r)(h, b) \Rightarrow \exists c, \operatorname{ReflTransGen}(r)(a, c) \land \operatorname{ReflTransGen}(r)(b, c)) \Rightarrow \operatorname{ReflTransGen}(r)(a, n1) \land \operatorname{ReflTransGen}(r)(a, n2) \land \operatorname{IsNormalForm}(r)(n1) \land \operatorname{IsNormalForm}(r)(n2) \Rightarrow n1 = n2.$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NormalFormConfluence.normal_form_unique_of_confluent` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

For a confluent rewrite relation, any two normal forms reachable from the same source are equal.

A common successor supplied by confluence must equal each normal form because no nontrivial rewrite leaves a normal form.

**Theorem 1.2 (Equivalent normal forms are equal).**

$$(\forall h, a, b, \operatorname{ReflTransGen}(r)(h, a) \land \operatorname{ReflTransGen}(r)(h, b) \Rightarrow \exists c, \operatorname{ReflTransGen}(r)(a, c) \land \operatorname{ReflTransGen}(r)(b, c)) \Rightarrow \operatorname{EqvGen}(r)(n1, n2) \land \operatorname{IsNormalForm}(r)(n1) \land \operatorname{IsNormalForm}(r)(n2) \Rightarrow n1 = n2.$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NormalFormConfluence.eqvGen_normal_form_eq` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

For a confluent rewrite relation, equivalent normal forms are equal even when their equivalence uses reverse rewrite steps.

Induction on the generated equivalence produces a common successor; the transitive case rejoins its intermediate reductions by confluence.

## References

- Truth anchor: `D5/S0/Rewriting/NormalFormConfluence.eqvGen_normal_form_eq`
- Truth anchor: `D5/S0/Rewriting/NormalFormConfluence.normal_form_unique_of_confluent`
