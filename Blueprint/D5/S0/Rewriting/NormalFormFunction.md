# Normal Form Function

## Abstract

Terminating locally confluent rewrite systems admit a canonical normal-form function.

**Theorem 1.1 (The chosen normal form is reachable and irreducible).**

$$\operatorname{ReflTransGen}(r)(a, nf(r, termination, localConfluence, a)) \land \operatorname{IsNormalForm}(r)(nf(r, termination, localConfluence, a).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NormalFormFunction.nf_spec` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

The function is defined by choosing the unique normal form supplied by the frozen Newman theorem.

Its specification records both the reflexive-transitive reduction from the source and irreducibility of the chosen endpoint.

**Theorem 1.2 (Normal-form selection is idempotent).**

$$nf(r, termination, localConfluence, nf(r, termination, localConfluence, a)) = nf(r, termination, localConfluence, a).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NormalFormFunction.nf_idempotent` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

The first selection reaches a normal form from the second selection's source; uniqueness therefore identifies the two choices.

**Theorem 1.3 (Equivalent starting points share a normal form).**

$$\operatorname{EqvGen}(r)(a, b) \Rightarrow nf(r, termination, localConfluence, a) = nf(r, termination, localConfluence, b).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/NormalFormFunction.nf_eq_of_eqvGen` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

Church-Rosser converts the generated equivalence into a common reduct, and Newman normal-form uniqueness identifies both choices with the normal form of that reduct.

## References

- Truth anchor: `D5/S0/Rewriting/NormalFormFunction.nf_eq_of_eqvGen`
- Truth anchor: `D5/S0/Rewriting/NormalFormFunction.nf_idempotent`
- Truth anchor: `D5/S0/Rewriting/NormalFormFunction.nf_spec`
- Dependency: [D5/S0/Rewriting/ChurchRosser](ChurchRosser.md)
- Dependency: [D5/S0/Rewriting/NormalFormConfluence](NormalFormConfluence.md)
