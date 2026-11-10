# Actual high-witness payments and regular equality resources

## Abstract

Actual high-witness payments and regular equality resources

Actual injective deletion witnesses give an exact regular isolate-plus-unused budget. Tightness classifies omitted selected degrees as one, two or d. Every one-neighbor resource has a unique full-high owner; every two-neighbor resource has a unique adjacent degree d-minus-one high owner and an actual isolate as its other selected neighbor. Actual witness and leaf bijections give the corresponding class cardinalities. The high graph is d-minus-one regular under isolate-tight bipartite hypotheses, and under order equality without bipartiteness. Full resources have only selected nonhigh neighbors and selected leaves have only their support, private resource and full resources as neighbors. For every positive-degree finite regular bipartite graph, SF attains the order bound if and only if beta does. Complete converse partitions, all balance and component identities, path forms and Heawood block credits remain separate obligations.

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

**Theorem 1.19 (tight resource degrees).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_resource_degrees`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_resource_degrees` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_resource_degrees (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (x : V) (hx : x ∉ S) : selectedDegree G S x=1 ∨ selectedDegree G S x=2 ∨ selectedDegree G S x=d.

**Theorem 1.20 (tight one owner).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_one_owner`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_one_owner` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_one_owner (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (x : V) (hx : x ∉ S) (hone : selectedDegree G S x=1) : ∃! v, v ∈ CertificateBound.high G S ∧ selectedDegree G S v=d ∧ BipartiteExchange.witness G S hS v=x.

**Theorem 1.21 (tight two owner).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_two_owner`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_two_owner` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_two_owner (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (x : V) (hx : x ∉ S) (htwo : selectedDegree G S x=2) : ∃! v, v ∈ CertificateBound.high G S ∧ selectedDegree G S v=d-1 ∧ BipartiteExchange.witness G S hS v=x ∧ G.Adj x v.

**Theorem 1.22 (tight two isolate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_two_isolate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_two_isolate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_two_isolate (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (x : V) (hx : x ∉ S) (htwo : selectedDegree G S x=2) : ∃ v u, v ∈ CertificateBound.high G S ∧ selectedDegree G S v=d-1 ∧ BipartiteExchange.witness G S hS v=x ∧ S.filter (G.Adj x)={v,u} ∧ BipartiteExchange.Isolate G S u.

**Theorem 1.23 (tight resource cardinalities).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_resource_cardinalities`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_resource_cardinalities` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_resource_cardinalities (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) : ((CertificateBound.high G S).filter (fun v => selectedDegree G S v=d)).card = ((Finset.univ \ S).filter (fun x => selectedDegree G S x=1)).card ∧ ((CertificateBound.high G S).filter (fun v => selectedDegree G S v=d-1)).card = ((Finset.univ \ S).filter (fun x => selectedDegree G S x=2)).card.

**Theorem 1.24 (tight leaf cardinality).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_cardinality` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_leaf_cardinality (hS : IsMinimalStarForming G 2 S) (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) : ((CertificateBound.high G S).filter (fun v => selectedDegree G S v=d)).card = (S.filter (fun u => ∃ v, BipartiteExchange.LeafAt G S u v)).card.

**Theorem 1.25 (order tight high regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_high_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_high_regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem order_tight_high_regular (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 2 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card=d*Fintype.card V) (v : V) (hv : v ∈ CertificateBound.high G S) : selectedDegree G (CertificateBound.high G S) v=d-1.

**Theorem 1.26 (tight high outside).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_high_outside`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_high_outside` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_high_outside (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (v x : V) (hv : v ∈ CertificateBound.high G S) (hx : x ∉ S) (hvx : G.Adj v x) : selectedDegree G S v=d-1 ∧ BipartiteExchange.witness G S hS v=x ∧ selectedDegree G S x=2.

**Theorem 1.27 (tight full resource neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_full_resource_neighbors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_full_resource_neighbors` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_full_resource_neighbors (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (y : V) (hy : y ∉ S) (hyd : selectedDegree G S y=d) (v : V) (hyv : G.Adj y v) : v ∈ S ∧ v ∉ CertificateBound.high G S.

**Theorem 1.28 (tight leaf remaining neighbors).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_remaining_neighbors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_remaining_neighbors` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem tight_leaf_remaining_neighbors (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (d : ℕ) (hd : 3 ≤ d) (hdegree : ∀ v, degree G v=d) (ht : (2*d-1)*S.card+(isolates G S).card=d*Fintype.card V) (u v : V) (hu : BipartiteExchange.LeafAt G S u v) (x : V) (hux : G.Adj u x) (hxv : x≠v) (hxw : x≠BipartiteExchange.witness G S hS v) : x ∉ S ∧ selectedDegree G S x=d.

**Theorem 1.29 (order endpoint iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_endpoint_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_endpoint_iff` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem order_endpoint_iff (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ v, degree G v=d) : (2*d-1)*SF G 2=d*Fintype.card V ↔ (2*d-1)*beta G 2=d*Fintype.card V.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_endpoint_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_high_full`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_high_regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_isolates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_leaf_witness`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.order_tight_unique_leaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_add_unused`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_at_witness`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_le_capacity`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_off_image`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.regular_budget`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_full_resource_neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_full_unique_leaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_high_outside`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_high_regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_iff_pointwise`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_cardinality`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_full`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_remaining_neighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_leaf_reserved`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_no_extra`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_one_owner`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_outside_classes`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_resource_cardinalities`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_resource_degrees`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_two_isolate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_two_owner`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_witness_classes`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange](BipartiteExchange.md)
