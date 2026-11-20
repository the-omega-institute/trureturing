# The enlarged shared-port core architecture

## Abstract

The enlarged shared-port core architecture

The graph has exactly high, leaf, X, hub and broken-Heawood vertices with the displayed incidence rules. Actual dissociation witnesses give both lower bounds, with repeated attachments allowed. Actual deletion failures give the forming witness, and cubic regularity supplies hub surjectivity and the attachment budget. The finite cardinalities, 3/62 upper coefficient, exact two-case slack identities and equality iff block count is 3r and beta is 33r concern this precise graph and color balance. Z_r attainment and general graph structural claims remain separate obligations.

**Definition 1.1 (Vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.Vertex`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.Vertex` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Vertex (H Y B : Type).

**Definition 1.2 (high).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.high`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.high` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev high {H Y B : Type} (h : H) : Vertex H Y B.

**Definition 1.3 (leaf).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.leaf`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.leaf` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev leaf {H Y B : Type} (h : H) : Vertex H Y B.

**Definition 1.4 (outside).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.outside`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.outside` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev outside {H Y B : Type} (h : H) : Vertex H Y B.

**Definition 1.5 (hub).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.hub`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.hub` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev hub {H Y B : Type} (y : Y) : Vertex H Y B.

**Definition 1.6 (block).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.block`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.block` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev block {H Y B : Type} (b : B) (v : Fin 14) : Vertex H Y B.

**Definition 1.7 (adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.adjacency`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.adjacency` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def adjacency (Q X : SimpleGraph H) (group : H → Y) (attach : B × Fin 2 → H) : Vertex H Y B → Vertex H Y B → Prop | .inl h,.inl k => Q.Adj h k | .inl h,.inr (.inl k) => h = k | .inr (.inl h),.inl k => h = k | .inr (.inl h),.inr (.inr (.inl k)) => h = k | .inr (.inr (.inl h)),.inr (.inl k) => h = k | .inr (.inl h),.inr (.inr (.inr (.inl y))) => group h = y | .inr (.inr (.inr (.inl y))),.inr (.inl h) => group h = y | .inr (.inr (.inl h)),.inr (.inr (.inl k)) => X.Adj h k | .inr (.inr (.inl h)),.inr (.inr (.inr (.inr (b,v)))) => ∃ p : Fin 2, v = HeawoodInterfaces.port p ∧ attach (b,p) = h | .inr (.inr (.inr (.inr (b,v)))),.inr (.inr (.inl h)) => ∃ p : Fin 2, v = HeawoodInterfaces.port p ∧ attach (b,p) = h | .inr (.inr (.inr (.inr (b,v)))),.inr (.inr (.inr (.inr (c,w)))) => b = c ∧ BrokenAdj v w | _,_ => False /-- The graph contains exactly the specified architecture edges. -/ def graph (Q X : SimpleGraph H) (group : H → Y) (attach : B × Fin 2 → H) : SimpleGraph (Vertex H Y B).

**Definition 1.8 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (Q X : SimpleGraph H) (group : H → Y) (attach : B × Fin 2 → H) : SimpleGraph (Vertex H Y B).

**Definition 1.9 (first).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.first`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.first` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def first (color : H → Bool) : Vertex H Y B → Prop | .inl h => color h = true | .inr (.inl _) => True | .inr (.inr (.inl h)) => color h = false | .inr (.inr (.inr (.inl _))) => False | .inr (.inr (.inr (.inr (_,v)))) => v.val < 7 /-- Second witness: every leaf, odd highs and the original four-edge block eight-set. -/ def second (color : H → Bool) : Vertex H Y B → Prop | .inl h => color h = true | .inr (.inl _) => True | .inr (.inr (.inl _)) => False | .inr (.inr (.inr (.inl _))) => False | .inr (.inr (.inr (.inr (_,v)))) => v ∈ HeawoodPorts.eightSet private theorem port_color : ∀ p : Fin 2, ((HeawoodInterfaces.port p).val < 7 ↔ p = 0).

**Definition 1.10 (second).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.second`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.second` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def second (color : H → Bool) : Vertex H Y B → Prop | .inl h => color h = true | .inr (.inl _) => True | .inr (.inr (.inl _)) => False | .inr (.inr (.inr (.inl _))) => False | .inr (.inr (.inr (.inr (_,v)))) => v ∈ HeawoodPorts.eightSet private theorem port_color : ∀ p : Fin 2, ((HeawoodInterfaces.port p).val < 7 ↔ p = 0).

**Theorem 1.11 (first dissociation).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.first_dissociation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.first_dissociation` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem first_dissociation (Q X : SimpleGraph H) (group : H → Y) (attach : B × Fin 2 → H) (color : H → Bool) (hQ : ∀ h k, Q.Adj h k → color h ≠ color k) (hX : ∀ h k, X.Adj h k → color h ≠ color k) (ha : ∀ b p, color (attach (b,p)) = decide (p = 0)) : DissociationCover.Dissociates (graph Q X group attach).Adj (first color).

**Theorem 1.12 (second dissociation).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.second_dissociation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.second_dissociation` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem second_dissociation (Q X : SimpleGraph H) (group : H → Y) (attach : B × Fin 2 → H) (color : H → Bool) (hQ : ∀ h k, Q.Adj h k → color h ≠ color k) : DissociationCover.Dissociates (graph Q X group attach).Adj (second color).

**Definition 1.13 (forming).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.forming`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.forming` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def forming : Vertex H Y B → Prop | .inl _ => True | .inr (.inl _) => True | .inr (.inr (.inl _)) => False | .inr (.inr (.inr (.inl _))) => False | .inr (.inr (.inr (.inr (_,v)))) => fanoSelected v private theorem selected_fano_broken : ∀ a b : Fin 14, fanoSelected a ∨ fanoSelected b → (FanoAdj a b ↔ BrokenAdj a b).

**Theorem 1.14 (forming minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.forming_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.forming_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_minimal (Q X : SimpleGraph H) (group : H → Y) (attach : B × Fin 2 → H) (hgroup : Function.Surjective group) : Regular.Minimal (graph Q X group attach).Adj forming.

**Theorem 1.15 (sf lower).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.sf_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.sf_lower` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_lower (Q X : SimpleGraph H) (group : H → Y) (attach : B × Fin 2 → H) (hregular : ∀ v, DegreeCapacity.degree (graph Q X group attach) v = 3) : 2*Fintype.card H + 8*Fintype.card B ≤ SF (graph Q X group attach) 2.

**Theorem 1.16 (witness cardinalities).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.witness_cardinalities`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.witness_cardinalities` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem witness_cardinalities (color : H → Bool) : (firstSet (Y.

**Theorem 1.17 (beta lower bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.beta_lower_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.beta_lower_bounds` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem beta_lower_bounds (Q X : SimpleGraph H) (group : H → Y) (attach : B × Fin 2 → H) (color : H → Bool) (hQ : ∀ h k, Q.Adj h k → color h ≠ color k) (hX : ∀ h k, X.Adj h k → color h ≠ color k) (ha : ∀ b p, color (attach (b,p)) = decide (p = 0)) (r : ℕ) (hH : Fintype.card H = 6*r) (ht : (Finset.univ.filter (fun h => color h = true)).card = 3*r) (hf : (Finset.univ.filter (fun h => color h = false)).card = 3*r) : 12*r + 7*Fintype.card B ≤ beta (graph Q X group attach) 2 ∧ 9*r + 8*Fintype.card B ≤ beta (graph Q X group attach) 2.

**Theorem 1.18 (architecture bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.architecture_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.architecture_bounds` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem architecture_bounds (Q X : SimpleGraph H) (group : H → Y) (attach : B × Fin 2 → H) (color : H → Bool) (hQ : ∀ h k, Q.Adj h k → color h ≠ color k) (hX : ∀ h k, X.Adj h k → color h ≠ color k) (ha : ∀ b p, color (attach (b,p)) = decide (p = 0)) (r : ℕ) (hH : Fintype.card H = 6*r) (hY : Fintype.card Y = 2*r) (ht : (Finset.univ.filter (fun h => color h = true)).card = 3*r) (hf : (Finset.univ.filter (fun h => color h = false)).card = 3*r) (hG : (graph Q X group attach).Colorable 2) (hregular : ∀ v, DegreeCapacity.degree (graph Q X group attach) v = 3) : let G.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.adjacency`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.architecture_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.beta_lower_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.block`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.first`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.first_dissociation`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.forming`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.forming_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.high`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.hub`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.leaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.outside`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.second`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.second_dissociation`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.sf_lower`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CoreArchitecture.witness_cardinalities`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces](HeawoodInterfaces.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts](HeawoodPorts.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](RegularCompensation.md)
