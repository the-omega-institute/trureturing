# Compatible witness-pair augmentation

## Abstract

Compatible witness-pair augmentation

Compatible isolated witness/leaf pairs can be adjoined to an existing dissociation selection. The extra-leaf failure lemma identifies witness capacity outside the high image. These are graph-level augmentation statements with the complete compatibility hypotheses, not a proof that the original unaugmented exchanges are maximum or that their accounting normal form classifies graph-parameter equality.

**Theorem 1.1 (augment isolated pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicPathAccounting.augment_isolated_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicPathAccounting.augment_isolated_pairs` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem augment_isolated_pairs {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection added : Vertex → Prop) (partner : Vertex → Vertex) (hsymmetric : ∀ first second, adjacency first second → adjacency second first) (hdissociates : Dissociates adjacency selection) (hisolated : ∀ vertex, added vertex → ∀ neighbor, selection neighbor → ¬ adjacency (partner vertex) neighbor) (hneighbor : ∀ vertex, added vertex → ∀ neighbor, selection neighbor → adjacency vertex neighbor → neighbor = partner vertex) (hindependent : ∀ first second, added first → added second → ¬ adjacency first second) (hinjective : ∀ first second, added first → added second → partner first = partner second → first = second) : Dissociates adjacency (fun vertex => selection vertex ∨ added vertex).

**Theorem 1.2 (extra leaf failure is unused).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CubicPathAccounting.extra_leaf_failure_is_unused`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CubicPathAccounting.extra_leaf_failure_is_unused` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem extra_leaf_failure_is_unused {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (htrianglefree : ∀ outside first second, adjacency outside first → adjacency outside second → adjacency first second → False) (witness reserved : Vertex → Vertex) (hfailure : ∀ owner, High adjacency selection owner → Failure adjacency selection owner (witness owner)) (hreserved : ∀ owner, High adjacency selection owner → ¬ adjacency (witness owner) owner → ∀ neighbor, selection neighbor → adjacency (witness owner) neighbor → neighbor = reserved owner) (leaf support outside : Vertex) (hleaf : selection leaf) (hsupport : selection support) (hleafedge : adjacency leaf support) (houtsideedge : adjacency outside leaf) (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support) (hextra : leaf ≠ reserved support) : ∀ owner, High adjacency selection owner → outside ≠ witness owner.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicPathAccounting.augment_isolated_pairs`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CubicPathAccounting.extra_leaf_failure_is_unused`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CubicStability](CubicStability.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DissociationCover](DissociationCover.md)
