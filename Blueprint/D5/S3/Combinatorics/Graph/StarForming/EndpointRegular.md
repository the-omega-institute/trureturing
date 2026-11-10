# All-degree order-bound equality graphs

## Abstract

All-degree order-bound equality graphs

The source four independent parts have sizes d,d,d-1,d-1, a matching between the selected parts, and complete incidence to the opposite omitted parts. Exact neighborhoods give regularity, the actual matching selection attains two d, and the general regular degree bound gives beta two and SF two both equal two d. Explicit deletion paths prove two-connectivity for every d at least two, including the degree-two C6 detour. The parameter theorem includes degree one as a single edge. This construction has order four d minus two and is separate from the positive-gap graphs of order four d plus two.

**Definition 1.1 (Side).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.Side`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.Side` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Side (d : ℕ).

**Definition 1.2 (Vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.Vertex`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.Vertex` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Vertex (d : ℕ).

**Definition 1.3 (link).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.link`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.link` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def link {d : ℕ} : Side d → Side d → Prop | .inl i, .inl j => i = j | .inl _, .inr _ => True | .inr _, .inl _ => True | .inr _, .inr _ => False instance {d : ℕ} : DecidableRel (@link d).

**Definition 1.4 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (d : ℕ) : SimpleGraph (Vertex d).

**Theorem 1.5 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (d : ℕ) : (graph d).Colorable 2.

**Theorem 1.6 (regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular (d : ℕ) (hd : 1 ≤ d) (v : Vertex d) : DegreeCapacity.degree (graph d) v = d.

**Definition 1.7 (matching).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.matching`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.matching` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def matching (d : ℕ) : Finset (Vertex d).

**Theorem 1.8 (matching card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.matching_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.matching_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem matching_card (d : ℕ) : (matching d).card=2*d.

**Theorem 1.9 (matching independent).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.matching_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.matching_independent` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem matching_independent (d : ℕ) : IsKIndependent (graph d) 2 (matching d).

**Theorem 1.10 (parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameters (d : ℕ) (hd : 1 ≤ d) : Fintype.card (Vertex d)=4*d-2 ∧ beta (graph d) 2=2*d ∧ SF (graph d) 2=2*d.

**Theorem 1.11 (delete preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.delete_preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.delete_preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem delete_preconnected (d : ℕ) (hd : 2 ≤ d) (z : Vertex d) : ((graph d).induce {v | v ≠ z}).Preconnected.

**Theorem 1.12 (two connected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.two_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.two_connected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem two_connected (d : ℕ) (hd : 2 ≤ d) : (graph d).Connected ∧ (∀ z : Vertex d, ((graph d).induce {v | v ≠ z}).Connected) ∧ 3 ≤ Fintype.card (Vertex d).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.Side`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.delete_preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.link`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.matching`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.matching_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.matching_independent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EndpointRegular.two_connected`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Comparison](Comparison.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity](FiberConnectivity.md)
