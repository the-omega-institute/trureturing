# Exact actual graph deficiency

## Abstract

Exact actual graph deficiency

For any finite simple graph of maximum degree at most d with d positive, every dissociation set satisfies the exact cut identity with the actual selected isolates, actual complementary edges and degree deficiencies. Dropping nonnegative terms gives the deficiency upper bound. These statements are graph identities, not an assumed port-count certificate.

**Definition 1.1 (deficiency).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.deficiency`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.deficiency` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def deficiency (d : ℕ) (S : Finset V) : ℕ.

**Definition 1.2 (complementEdges).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.complementEdges`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.complementEdges` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def complementEdges (S : Finset V) : ℕ.

**Theorem 1.3 (exact identity).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.exact_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.exact_identity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem exact_identity (D : Finset V) (hD : IsKIndependent G 2 D) (d : ℕ) (hdpos : 1≤d) (hd : ∀ v, degree G v≤d) : (2*d-1)*D.card + deficiency G d Finset.univ + (isolates G D).card + 2*complementEdges G D = d*Fintype.card V + 2*deficiency G d D.

**Theorem 1.4 (deficiency bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.deficiency_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.deficiency_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem deficiency_bound (D : Finset V) (hD : IsKIndependent G 2 D) (d : ℕ) (hdpos : 1≤d) (hd : ∀ v, degree G v≤d) : (2*d-1)*D.card + deficiency G d Finset.univ ≤ d*Fintype.card V + 2*deficiency G d D.

**Theorem 1.5 (tight degrees).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.tight_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.tight_degrees` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_degrees (D : Finset V) (hD : IsKIndependent G 2 D) (hi : (isolates G D).card = 0) (he : complementEdges G D = 0) (v : V) : selectedDegree G D v = if v ∈ D then 1 else degree G v.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.complementEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.deficiency`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.deficiency_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.exact_identity`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency.tight_degrees`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
