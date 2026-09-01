# Natural Invariants Across Naming Systems

## Abstract

Compatible quantities across naming interfaces are sections of their value functor.

**Theorem 1.1 (Natural invariants are compatible families and admit a constant witness).**

$$\forall Name: Type, [\operatorname{Category}\left(Name\right)],\ (\forall Q: \operatorname{Functor}\left(Name, Type\right), \phi: \prod_{r \in Name} \operatorname{obj}\left(Q, r\right),\ \phi \in \operatorname{sections}\left(Q\right) \iff \forall r_2, r_1: Name, f: \operatorname{Hom}\left(r_2, r_1\right),\ \operatorname{map}\left(Q, f, \operatorname{apply}\left(\phi, r_2\right)\right) = \operatorname{apply}\left(\phi, r_1\right)) \land \ \exists \phi: \operatorname{sections}\left(\operatorname{const}\left(Name, \mathbb{Z}\right)\right), \phi = (r \mapsto 1).$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/NaturalInvariant.naming_natural_invariant_iff_and_integer_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Name be the category of admissible naming interfaces and let a quantity functor send each interface to its type of quantities. A cross-naming trace is a dependent family with one quantity at every interface. Membership in the functor's sections is definitionally equivalent to compatibility with every refinement morphism: pushing the fine-interface value forward gives the coarse-interface value.

The statement uses Mathlib's Functor.sections as the lightweight explicit form of a categorical compatible family. This records the source atom's naturality condition without adding uniqueness, cofilteredness, finiteness, or quantitative hypotheses not present in the source.

The definition is inhabited nontrivially: the constant functor with value the integers has the section taking every naming interface to one. The value one makes the witness explicitly nonzero-valued rather than an empty or zero-family artifact.

Repository searches found only preorder-indexed inverse-system variants and a finite cofiltered existence theorem. Pinned Mathlib supplies the exact Functor.sections compatibility predicate and Functor.const for the witness, so the Lean proof reuses both primitives directly.

## References

- Truth anchor: `D5/S0/Naming/NaturalInvariant.naming_natural_invariant_iff_and_integer_witness`
