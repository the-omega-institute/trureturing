# Actual high-witness payments and regular equality resources

## Abstract

Actual high-witness payments and regular equality resources

Each high vertex pays its selected-degree demand to its actual injective deletion witness. Pointwise payment is bounded by the unused selected-degree capacity and sums to every high demand exactly once. The resulting exact regular budget retains selected isolates and nonnegative pointwise residuals. Equality exhausts every outside resource: every unpaid outside vertex has full selected degree, and high owners split into degree d minus one with an adjacent two-neighbor witness or degree d with a nonadjacent one-neighbor witness. This is an actual graph extraction. For isolate-tight bipartite regular graphs of degree at least three, every selected leaf is reserved, full highs have unique selected leaves, and the actual high graph is d-1 regular. For order-bound equality in every regular graph of degree at least two, selected isolates vanish, every high has full selected degree, and each high has exactly one selected leaf; no bipartiteness is needed for these order-tight results. Complete class counts and converse partitions, component path normal forms and Heawood block credits require their separate proofs and are not asserted here.

**Theorem 1.1 (payment le capacity).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_le_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_le_capacity` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem payment_le_capacity (d : ℕ) (hdegree : ∀ v, degree G v ≤ d) (x : V) : payment G S hS x ≤ d-selectedDegree G S x.

**Theorem 1.2 (payment sum).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_sum` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem payment_sum : ∑ x ∈ Finset.univ \ S, payment G S hS x = ∑ v ∈ CertificateBound.high G S, (selectedDegree G S v-1).

**Theorem 1.3 (payment add unused).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_add_unused`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_add_unused` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem payment_add_unused (d : ℕ) (hdegree : ∀ v, degree G v ≤ d) (x : V) : payment G S hS x + unused G S hS d x = d-selectedDegree G S x.

**Theorem 1.4 (regular budget).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.regular_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.regular_budget` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular_budget (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) : (2*d-1)*S.card + (isolates G S).card + (∑ x ∈ Finset.univ \ S, unused G S hS d x) = d*Fintype.card V.

**Theorem 1.5 (payment at witness).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_at_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_at_witness` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem payment_at_witness (v : V) (hv : v ∈ CertificateBound.high G S) : payment G S hS (BipartiteExchange.witness G S hS v) = selectedDegree G S v-1.

**Theorem 1.6 (payment off image).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_off_image`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_off_image` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem payment_off_image (x : V) (hx : ¬ ∃ v ∈ CertificateBound.high G S, BipartiteExchange.witness G S hS v=x) : payment G S hS x=0.

**Theorem 1.7 (tight iff pointwise).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_iff_pointwise`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_iff_pointwise` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_iff_pointwise (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V ↔ ∀ x ∈ Finset.univ \ S, unused G S hS d x=0.

**Theorem 1.8 (tight outside classes).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_outside_classes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_outside_classes` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_outside_classes (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) : (∀ v ∈ CertificateBound.high G S, selectedDegree G S v+selectedDegree G S (BipartiteExchange.witness G S hS v)=d+1) ∧ (∀ x ∈ Finset.univ \ S, (∃ v ∈ CertificateBound.high G S, BipartiteExchange.witness G S hS v=x) ∨ selectedDegree G S x=d).

**Theorem 1.9 (tight witness classes).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_witness_classes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_witness_classes` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_witness_classes (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (v : V) (hv : v ∈ CertificateBound.high G S) : let x.

**Theorem 1.10 (tight no extra).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_no_extra`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_no_extra` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_no_extra (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (u : V) : ¬ BipartiteExchange.Extra G S hS u.

**Theorem 1.11 (tight leaf reserved).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_reserved`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_reserved` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_leaf_reserved (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (u h : V) (hu : BipartiteExchange.LeafAt G S u h) : BipartiteExchange.Reserved G S hS u.

**Theorem 1.12 (tight leaf full).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_full` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_leaf_full (hS : IsMinimalStarForming G 2 S) (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (u h : V) (hu : BipartiteExchange.LeafAt G S u h) : selectedDegree G S h=d.

**Theorem 1.13 (tight full unique leaf).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_full_unique_leaf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_full_unique_leaf` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_full_unique_leaf (hS : IsMinimalStarForming G 2 S) (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (v : V) (hv : v ∈ CertificateBound.high G S) (hfull : selectedDegree G S v=d) : ∃! u, BipartiteExchange.LeafAt G S u v.

**Theorem 1.14 (tight high regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_high_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_high_regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_high_regular (hS : IsMinimalStarForming G 2 S) (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (v : V) (hv : v ∈ CertificateBound.high G S) : selectedDegree G (CertificateBound.high G S) v=d-1.

**Theorem 1.15 (order tight isolates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_isolates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_isolates` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem order_tight_isolates (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card=d*Fintype.card V) : (isolates G S).card=0.

**Theorem 1.16 (order tight leaf witness).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_leaf_witness`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_leaf_witness` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem order_tight_leaf_witness (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 2 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card=d*Fintype.card V) (u h : V) (hu : BipartiteExchange.LeafAt G S u h) : G.Adj (BipartiteExchange.witness G S hS h) u ∧ selectedDegree G S h=d.

**Theorem 1.17 (order tight high full).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_high_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_high_full` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem order_tight_high_full (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 2 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card=d*Fintype.card V) (v : V) (hv : v ∈ CertificateBound.high G S) : selectedDegree G S v=d.

**Theorem 1.18 (order tight unique leaf).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_unique_leaf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_unique_leaf` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem order_tight_unique_leaf (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 2 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card=d*Fintype.card V) (v : V) (hv : v ∈ CertificateBound.high G S) : ∃! u, BipartiteExchange.LeafAt G S u v.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_high_full`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_isolates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_leaf_witness`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_unique_leaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_add_unused`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_at_witness`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_le_capacity`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_off_image`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.regular_budget`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_full_unique_leaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_high_regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_iff_pointwise`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_full`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_reserved`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_no_extra`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_outside_classes`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_witness_classes`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange](BipartiteExchange.md)
