# Upper domination and independence in bipartite graphs

## Abstract

Upper domination and independence in bipartite graphs

Closed-neighborhood domination and inclusion-minimality define the actual finite upper-domination maximum Gamma. The classical private-neighbor exchange sends each minimal dominating selection to an independent selection of the same cardinality, proving Gamma equals Mathlib independence number in every finite bipartite graph. Positive regularity gives twice alpha equal to the order. Empty and disconnected graphs remain included; neither SF nor psiSq is identified with Gamma.

**Definition 1.1 (Dominates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.Dominates`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.Dominates` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Dominates (D : Finset V) : Prop.

**Definition 1.2 (MinimalDominating).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.MinimalDominating`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.MinimalDominating` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def MinimalDominating (D : Finset V) : Prop.

**Theorem 1.3 (minimal dominating exchange).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.minimal_dominating_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.minimal_dominating_exchange` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_dominating_exchange (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (D : Finset V) (hD : MinimalDominating G D) : ∃ J : Finset V, G.IsIndepSet (J : Set V) ∧ J.card = D.card.

**Theorem 1.4 (gamma eq alpha).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.gamma_eq_alpha`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.gamma_eq_alpha` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem gamma_eq_alpha (hG : G.Colorable 2) : Gamma G = G.indepNum.

**Theorem 1.5 (alpha le beta).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.alpha_le_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.alpha_le_beta` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem alpha_le_beta : G.indepNum ≤ beta G 2.

**Theorem 1.6 (regular alpha card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.regular_alpha_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.regular_alpha_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular_alpha_card (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, DegreeCapacity.degree G v = d) : 2 * G.indepNum = Fintype.card V.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.Dominates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.MinimalDominating`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.alpha_le_beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.gamma_eq_alpha`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.minimal_dominating_exchange`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DominationComparison.regular_alpha_card`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](RegularCompensation.md)
