# Actual high-witness payments and regular equality resources

## Abstract

Actual high-witness payments and regular equality resources

Each high vertex pays its selected-degree demand to its actual injective deletion witness. Pointwise payment is bounded by the unused selected-degree capacity and sums to every high demand exactly once. The resulting exact regular budget retains selected isolates and nonnegative pointwise residuals. Equality exhausts every outside resource: every unpaid outside vertex has full selected degree, and high owners split into degree d minus one with an adjacent two-neighbor witness or degree d with a nonadjacent one-neighbor witness. This is an actual graph extraction. The additional complete leaf bijections, class balances, component path normal forms and Heawood block credits require their separate proofs and are not asserted here.

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

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_add_unused`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_at_witness`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_le_capacity`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_off_image`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.payment_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.regular_budget`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_iff_pointwise`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_outside_classes`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/WitnessBudget.tight_witness_classes`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange](BipartiteExchange.md)
