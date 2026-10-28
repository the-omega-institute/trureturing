# Double-hub endpoint

## Abstract

The physical double-hub family: endpoint.

A selected edge has total 3 and therefore two admissible split positions. An unselected edge has total 2 and has the unique split 1+1. Subsets of the two selected edges parameterize all admissible splits without omissions. The endpoint product separates into a common power of 12 and factorial ratios at the vertices.

The total mass is the sum of all edge totals. The two-variable source is defined before homogenizing the closed form. When the first coupling is nonzero, each vertex factor yields its mass power times the corresponding one-variable factor at the coupling ratio.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Definition 1.1 (totals).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.totals`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.totals` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines totals for the physical double-hub family.

**Definition 1.2 (shares).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.shares`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.shares` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines shares for the physical double-hub family.

**Theorem 1.3 (split iff).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.split_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.split_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Classifies every admissible split by an endpoint-selection subset. Exact source statement: theorem split_iff {E : Type} [Fintype E] [DecidableEq E]     (A : Finset E) (k : E → ℕ) :     k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits (totals A) ↔       ∀ e, (e ∈ A → k e = 1 ∨ k e = 2) ∧ (e ∉ A → k e = 1).

**Theorem 1.4 (split sum).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.split_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.split_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constructs and checks the split/subset reindexing. Exact source statement: theorem split_sum {E : Type} [Fintype E] [DecidableEq E]     {R : Type} [AddCommMonoid R] (A : Finset E) (a : (E → ℕ) → R) :     (∑ k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits (totals A), a k) =       ∑ S ∈ A.powerset, a (shares S).

**Theorem 1.5 (actual mass).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem actual_mass {V E : Type} [Fintype V] [DecidableEq V]     [Fintype E] [DecidableEq E] (src tgt : E → V)     (A S : Finset E) (hSA : S ⊆ A) (v : V) :     D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass src tgt (totals A) (shares S) v =     ((Finset.univ.filter (fun e : E => src e = v)).card +       (Finset.univ.filter (fun e : E => tgt e = v)).card) +     (Finset.univ.filter (fun e : E => src e = v ∧ e ∈ S)).card +     (Finset.univ.filter (fun e : E => tgt e = v ∧ e ∈ A \ S)).card.

**Definition 1.6 (increments).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.increments`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.increments` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines increments for the physical double-hub family.

**Theorem 1.7 (all endpoint coefficient).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.all_endpoint_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.all_endpoint_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The live extraction path reduces the complete original source to all endpoint selections. Exact source statement: theorem all_endpoint_coefficient (m cutoff : ℕ) (hc : 3 ≤ cutoff) :     sourceCoefficient m cutoff =       ∑ A ∈ (Finset.univ : Finset (Edge m)).powersetCard 2,         Polynomial.C (sourcePrefactor (totals A)) *         ∑ S ∈ A.powerset,           Polynomial.C (physicalWeight (totals A) (shares S)) *           ∏ v : Vertex m, (1+Polynomial.C ((-1:ℝ)^degree v) *             Polynomial.X^(degree v+increments A S v)).

**Theorem 1.8 (mass total).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.mass_total`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.mass_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem mass_total {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]     (src tgt : E → V) (n k : E → ℕ)     (hk : k ∈ D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.splits n) :     (∑ v : V, D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation.mass src tgt n k v) =       ∑ e : E, n e.

**Theorem 1.9 (total degree).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.total_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.total_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem total_degree {E : Type} [Fintype E] [DecidableEq E] (m : ℕ)     (hE : Fintype.card E = 2*m+2) (n : E → ℕ)     (hrange : ∀ e : E, n e = 2 ∨ n e = 3)     (hcount : (Finset.univ.filter (fun e : E => n e = 3)).card = 2) :     (∑ e : E, n e) = 4*m+6.

**Theorem 1.10 (actual homogeneous ratio).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_homogeneous_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_homogeneous_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem actual_homogeneous_ratio (m cutoff : ℕ) (hc : 3 ≤ cutoff)     (lambda1 lambda2 : ℂ) (h1 : lambda1 ≠ 0) :     homogeneousCoefficient m cutoff lambda1 lambda2 =       lambda1^(4*m+6) *         (Polynomial.eval₂RingHom Complex.ofRealHom (lambda2/lambda1))           (sourceCoefficient m cutoff).

**Theorem 1.11 (actual prefactor).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_prefactor`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_prefactor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem actual_prefactor (m : ℕ) (A : Finset (Edge m)) (hA : A.card = 2) :     sourcePrefactor (fun e => if e ∈ A then 3 else 2) =       4 / (9*(automorphismOrder m : ℝ)).

**Theorem 1.12 (center degree).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.center_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.center_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem center_degree (m : ℕ) : degree (none : Vertex m) = 2.

**Theorem 1.13 (hub degree).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.hub_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.hub_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem hub_degree (m : ℕ) (b : Bool) :     degree (some (b,none) : Vertex m) = m+1.

**Theorem 1.14 (leaf degree).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.leaf_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.leaf_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem leaf_degree (m : ℕ) (b : Bool) (i : Fin m) :     degree (some (b,some i) : Vertex m) = 1.

**Theorem 1.15 (physicalWeight by edges).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.physicalWeight_by_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.physicalWeight_by_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem physicalWeight_by_edges {m : ℕ} (n k : Edge m → ℕ) :     physicalWeight n k =       (∏ e : Edge m, (Nat.choose (2*n e) (2*k e) : ℝ) * J (k e) * J (n e-k e)) *       ∏ v : Vertex m, (Nat.factorial (mass n k v-1) : ℝ) /         (Nat.factorial (mass n k v-degree v+2) : ℝ).

**Definition 1.16 (endpointRatio).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.endpointRatio`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.endpointRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines endpointRatio for the physical double-hub family.

**Theorem 1.17 (actual degree positive).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_degree_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_degree_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem actual_degree_positive (m : ℕ) (v : Vertex m) : 1 ≤ degree v.

**Theorem 1.18 (actual weight normalized).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_weight_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_weight_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Derives the uniform physical endpoint-ratio normalization from original factorial weights, not a weight hypothesis. Exact source statement: theorem actual_weight_normalized (m : ℕ) (A S : Finset (Edge m))     (hA : A.card = 2) (hSA : S ⊆ A) :     physicalWeight (totals A) (shares S) =       (16200*(Nat.factorial m:ℝ)^2*(12:ℝ)^(2*m)) *         ∏ v : Vertex m, endpointRatio (degree v) (increments A S v).

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_degree_positive`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_homogeneous_ratio`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_mass`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_prefactor`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.actual_weight_normalized`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.all_endpoint_coefficient`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.center_degree`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.endpointRatio`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.hub_degree`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.increments`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.leaf_degree`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.mass_total`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.physicalWeight_by_edges`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.shares`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.split_iff`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.split_sum`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.total_degree`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubEndpoint.totals`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubGraph](FiolDoubleHubGraph.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
