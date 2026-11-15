# Connected balanced-accounting counterexample

## Abstract

Connected balanced-accounting counterexample

The exact source twenty-eight-vertex graph and sixteen-set are kept. Actual deletion failures prove minimality, explicit paths prove connectivity, and kernel checks prove cubic bipartiteness, balanced isolates, the high path, zero witness surplus and the unused resource counts. The source normal-form lists swap leaves8 and10 and resources9 and11: in the stated graph9 has selected degree one and11 degree two. The canonical extraction uses reserved leaf8, extra leaf10 and high witness0-to9. The actual two original unaugmented exchanges each have size fourteen; the unchanged source dissociation fifteen-set makes both nonmaximum and forces compensation slack at least two. The typed closed claim/result pair refutes the candidate maximum-exchange inference. No exact beta upper bound, optimizer result or claim about the later augmented exchanges is made.

**Definition 1.1 (neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.neighbors`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.neighbors` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def neighbors (v : Fin 28) : List (Fin 28).

**Definition 1.2 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Fin 28).

**Definition 1.3 (selection).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.selection`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.selection` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selection : Finset (Fin 28).

**Definition 1.4 (unaugmentedLeft).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.unaugmentedLeft`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.unaugmentedLeft` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def unaugmentedLeft : Finset (Fin 28).

**Definition 1.5 (unaugmentedRight).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.unaugmentedRight`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.unaugmentedRight` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def unaugmentedRight : Finset (Fin 28).

**Definition 1.6 (largerDissociation).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.largerDissociation`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.largerDissociation` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def largerDissociation : Finset (Fin 28).

**Definition 1.7 (highs).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.highs`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.highs` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def highs : Finset (Fin 28).

**Definition 1.8 (extraLeaves).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.extraLeaves`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.extraLeaves` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def extraLeaves : Finset (Fin 28).

**Definition 1.9 (color).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.color`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.color` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def color (v : Fin 28) : Bool.

**Definition 1.10 (failure).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.failure`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.failure` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def failure (v : Fin 28) : Fin 28.

**Theorem 1.11 (minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal : IsMinimalStarForming graph 2 selection.

**Theorem 1.12 (class and balance).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.class_and_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.class_and_balance` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem class_and_balance : (∀ v, degree graph v=3) ∧ (∀ v w, graph.Adj v w → color v≠color w) ∧ isolates graph selection=({24,25} : Finset (Fin 28)) ∧ ((isolates graph selection).filter (fun v => color v=true)).card=1 ∧ ((isolates graph selection).filter (fun v => color v=false)).card=1.

**Theorem 1.13 (preconnected).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.preconnected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.preconnected` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem preconnected : graph.Preconnected.

**Theorem 1.14 (high path).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.high_path`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.high_path` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem high_path : CertificateBound.high graph selection=highs ∧ (∀ v w : Fin 8, graph.Adj ⟨v.val,by omega⟩ ⟨w.val,by omega⟩ ↔ v.val+1=w.val ∨ w.val+1=v.val) ∧ (highs.filter (fun v => selectedDegree graph selection v=2)).card=4 ∧ (highs.filter (fun v => selectedDegree graph selection v=3)).card=4.

**Theorem 1.15 (zero accounting).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.zero_accounting`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.zero_accounting` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem zero_accounting : (∀ h∈highs, 3-selectedDegree graph selection (failure h)= selectedDegree graph selection h-1) ∧ ((Finset.univ\selection)\highs.image failure)=({11,23,26,27} : Finset (Fin 28)) ∧ (∀ v∈({11,23} : Finset (Fin 28)), selectedDegree graph selection v=2) ∧ (∀ v∈({26,27} : Finset (Fin 28)), selectedDegree graph selection v=3) ∧ extraLeaves.card=2.

**Theorem 1.16 (exchanges).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.exchanges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.exchanges` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem exchanges : IsKIndependent graph 2 unaugmentedLeft ∧ unaugmentedLeft.card=14 ∧ IsKIndependent graph 2 unaugmentedRight ∧ unaugmentedRight.card=14 ∧ IsKIndependent graph 2 largerDissociation ∧ largerDissociation.card=15 ∧ selection.card=16.

**Theorem 1.17 (positive slack).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.positive_slack`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.positive_slack` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem positive_slack : 15≤beta graph 2 ∧ unaugmentedLeft.card<beta graph 2 ∧ unaugmentedRight.card<beta graph 2 ∧ 2≤3*Fintype.card (Fin 28)+2*beta graph 2-7*selection.card.

**Definition 1.18 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.claim` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def claim : Prop.

**Theorem 1.19 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.result` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem result : ¬claim.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.class_and_balance`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.color`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.exchanges`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.extraLeaves`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.failure`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.high_path`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.highs`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.largerDissociation`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.positive_slack`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.preconnected`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.unaugmentedLeft`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.unaugmentedRight`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.zero_accounting`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CoverConnectivity](CoverConnectivity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](RegularCompensation.md)
