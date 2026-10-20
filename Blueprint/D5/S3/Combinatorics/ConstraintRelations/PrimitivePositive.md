# Primitive-positive definitions and preservation

## Abstract

Generator-preserving operations preserve primitive-positive definitions.

**Definition 1.1 (Finite atoms with repeated variables).**

$$\forall S \in \mathrm{Type},\; \forall q \in (S) \to \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \operatorname{Atom}\left(q, n\right) = \operatorname{Sigma}\left(S, \operatorname{Arguments}\left(q, n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.Atom` (`✓ std3`).

*Citation.* David Geiger (1968). *Closed systems of functions and predicates*. DOI: [10.2140/pjm.1968.27.95](https://doi.org/10.2140/pjm.1968.27.95). URL: <https://msp.org/pjm/1968/27-1/p8.xhtml>.

*Commentary.*

A symbol s has arity q(s). An atom consists of s and a function from Fin(q(s)) to Fin(n). There is no injectivity condition: an argument variable may occur several times. Sigma here means the dependent collection of symbols and their argument functions. The carrier and the symbol type can be arbitrary.

**Definition 1.2 (Interpretation of an atom).**

$$\forall D \in \mathrm{Type},\; \forall S \in \mathrm{Type},\; \forall q \in (S) \to \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall R \in \operatorname{Relations}\left(D, S, q\right),\; \forall b \in \operatorname{Atom}\left(q, n\right),\; \forall v \in (\operatorname{Fin}\left(n\right)) \to D,\; \operatorname{Holds}\left(R, b, v\right) \Leftrightarrow \operatorname{ApplyAtom}\left(R, b, v\right)$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.Holds` (`✓ std3`).

*Citation.* David Geiger (1968). *Closed systems of functions and predicates*. DOI: [10.2140/pjm.1968.27.95](https://doi.org/10.2140/pjm.1968.27.95). URL: <https://msp.org/pjm/1968/27-1/p8.xhtml>.

*Commentary.*

Relations assigns each symbol s a predicate on Fin(q(s)) to D. ApplyAtom means R(s) applied to the tuple whose ith entry is v(b.arguments(i)).

**Definition 1.3 (Finite conjunction).**

$$\forall D \in \mathrm{Type},\; \forall S \in \mathrm{Type},\; \forall q \in (S) \to \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall R \in \operatorname{Relations}\left(D, S, q\right),\; \forall L \in \operatorname{List}\left(\operatorname{Atom}\left(q, n\right)\right),\; \forall v \in (\operatorname{Fin}\left(n\right)) \to D,\; \operatorname{HoldsAll}\left(R, L, v\right) \Leftrightarrow \operatorname{Conjunction}\left(R, L, v\right)$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.HoldsAll` (`✓ std3`).

*Citation.* David Geiger (1968). *Closed systems of functions and predicates*. DOI: [10.2140/pjm.1968.27.95](https://doi.org/10.2140/pjm.1968.27.95). URL: <https://msp.org/pjm/1968/27-1/p8.xhtml>.

*Commentary.*

Conjunction is true on the empty list and is the conjunction of the head atom and the remaining list otherwise. Lists are finite and may contain duplicate atoms.

**Definition 1.4 (Existentially hidden variables).**

$$\forall D \in \mathrm{Type},\; \forall S \in \mathrm{Type},\; \forall q \in (S) \to \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall R \in \operatorname{Relations}\left(D, S, q\right),\; \forall L \in \operatorname{List}\left(\operatorname{Atom}\left(q, n + m\right)\right),\; \forall a \in (\operatorname{Fin}\left(n\right)) \to D,\; \operatorname{Defines}\left(R, L, a\right) \Leftrightarrow \left(\exists h \in (\operatorname{Fin}\left(m\right)) \to D,\; \operatorname{HoldsAll}\left(R, L, \operatorname{append}\left(a, h\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.Defines` (`✓ std3`).

*Citation.* David Geiger (1968). *Closed systems of functions and predicates*. DOI: [10.2140/pjm.1968.27.95](https://doi.org/10.2140/pjm.1968.27.95). URL: <https://msp.org/pjm/1968/27-1/p8.xhtml>.

*Commentary.*

Variables 0 through n-1 are free. The following m variables are hidden. Defines is the existence of one hidden assignment satisfying every atom under the concatenated assignment. No equality or constants are implicit; they must be supplied as relation symbols when desired.

**Definition 1.5 (Coordinatewise preservation).**

$$\forall D \in \mathrm{Type},\; \forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall f \in ((\operatorname{Fin}\left(k\right)) \to D) \to D,\; \forall R \in ((\operatorname{Fin}\left(n\right)) \to D) \to \mathrm{Prop},\; \operatorname{Preserves}\left(f, R\right) \Leftrightarrow \operatorname{CoordinatewiseClosed}\left(f, R\right)$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.Preserves` (`✓ std3`).

*Citation.* David Geiger (1968). *Closed systems of functions and predicates*. DOI: [10.2140/pjm.1968.27.95](https://doi.org/10.2140/pjm.1968.27.95). URL: <https://msp.org/pjm/1968/27-1/p8.xhtml>.

*Commentary.*

For every family of k tuples in R, applying f at each coordinate yields another tuple in R. Both k and the relation arity n may be zero. This is preservation by an operation, also called a relational polymorphism.

**Theorem 1.6 (Polymorphisms preserve pp definitions).**

$$\forall D \in \mathrm{Type},\; \forall S \in \mathrm{Type},\; \forall q \in (S) \to \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall R \in \operatorname{Relations}\left(D, S, q\right),\; \forall f \in ((\operatorname{Fin}\left(k\right)) \to D) \to D,\; \left(\forall s \in S,\; \operatorname{Preserves}\left(f, \operatorname{R}\left(s\right)\right)\right) \Rightarrow \left(\forall L \in \operatorname{List}\left(\operatorname{Atom}\left(q, n + m\right)\right),\; \operatorname{Preserves}\left(f, \operatorname{Defines}\left(R, L\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.polymorphism_preserves_pp` (`✓ std3`). ∎

*Citation.* David Geiger (1968). *Closed systems of functions and predicates*. DOI: [10.2140/pjm.1968.27.95](https://doi.org/10.2140/pjm.1968.27.95). URL: <https://msp.org/pjm/1968/27-1/p8.xhtml>.

*Commentary.*

For arbitrary carrier D, symbol type S, arities q, operation arity k, free arity n and hidden arity m, an operation preserving each generating relation preserves every relation defined by a finite atom list. Induction on the list proves preservation of its conjunction. Choose one hidden assignment for each input tuple and apply the same operation to those assignments. Variable substitution commutes with this coordinatewise operation, including repeated arguments. The concatenated free and hidden assignments therefore satisfy the entire list. This is the preservation direction of the classical pp/polymorphism correspondence; no converse is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.Atom`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.Defines`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.Holds`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.HoldsAll`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.Preserves`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive.polymorphism_preserves_pp`
