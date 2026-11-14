# Uniform weighted square certificates

## Abstract

Uniform weighted square certificates

A square has four distinct vertices and the four cyclic edges; diagonals are allowed. Every dissociation selection meets it in at most two vertices. Finite weighted incidence is counted exactly by interchanging the vertex and square sums. Nonnegative rational square weights with total incident capacity one at every vertex imply two beta two<=n. For a bipartite graph the color-class lower bound attains equality. No SF equality, strict gain in a connected cover, or preservation of a positive gap is inferred.

**Definition 1.1 (Square).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.Square`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.Square` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: structure Square (G : SimpleGraph V).

**Definition 1.2 (Square.carrier).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.carrier`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.carrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def Square.carrier {G : SimpleGraph V} (C : Square G) : Finset V.

**Theorem 1.3 (carrier card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.carrier_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.carrier_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem carrier_card {G : SimpleGraph V} (C : Square G) : C.carrier.card = 4.

**Theorem 1.4 (intersection cap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.intersection_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.intersection_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem intersection_cap (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hS : IsKIndependent G 2 S) (C : Square G) : (S ∩ C.carrier).card ≤ 2.

**Theorem 1.5 (weighted intersections).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.weighted_intersections`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.weighted_intersections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem weighted_intersections {Q : Type*} [Fintype Q] (C : Q → Finset V) (weight : Q → ℚ) (S : Finset V) : ∑ q : Q, weight q * ((S ∩ C q).card : ℚ) = ∑ v ∈ S, ∑ q : Q, if v ∈ C q then weight q else 0.

**Theorem 1.6 (uniform intersections).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.uniform_intersections`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.uniform_intersections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem uniform_intersections {Q : Type*} [Fintype Q] (C : Q → Finset V) (weight : Q → ℚ) (huniform : ∀ v, (∑ q : Q, if v ∈ C q then weight q else 0) = 1) (S : Finset V) : ∑ q : Q, weight q * ((S ∩ C q).card : ℚ) = S.card.

**Theorem 1.7 (selection bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.selection_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.selection_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem selection_bound (G : SimpleGraph V) [DecidableRel G.Adj] {Q : Type*} [Fintype Q] (C : Q → Square G) (weight : Q → ℚ) (hweight : ∀ q, 0 ≤ weight q) (huniform : ∀ v, (∑ q : Q, if v ∈ (C q).carrier then weight q else 0) = 1) (S : Finset V) (hS : IsKIndependent G 2 S) : 2 * S.card ≤ Fintype.card V.

**Theorem 1.8 (beta bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.beta_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.beta_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem beta_bound (G : SimpleGraph V) [DecidableRel G.Adj] {Q : Type*} [Fintype Q] (C : Q → Square G) (weight : Q → ℚ) (hweight : ∀ q, 0 ≤ weight q) (huniform : ∀ v, (∑ q : Q, if v ∈ (C q).carrier then weight q else 0) = 1) : 2 * beta G 2 ≤ Fintype.card V.

**Theorem 1.9 (beta exact).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.beta_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.beta_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem beta_exact (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Colorable 2) {Q : Type*} [Fintype Q] (C : Q → Square G) (weight : Q → ℚ) (hweight : ∀ q, 0 ≤ weight q) (huniform : ∀ v, (∑ q : Q, if v ∈ (C q).carrier then weight q else 0) = 1) : 2 * beta G 2 = Fintype.card V.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.Square`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.beta_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.beta_exact`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.carrier`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.carrier_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.intersection_cap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.selection_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.uniform_intersections`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/SquareCapacity.weighted_intersections`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds](BipartiteBounds.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DissociationCover](DissociationCover.md)
