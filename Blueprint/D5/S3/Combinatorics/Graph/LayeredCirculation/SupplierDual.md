# SupplierDual

## Abstract

The finite path-potential and normalized real dual-certificate interface retains the necessary live upstream proofs. The finite incompatibility adapter directly applies the repository frozen inequality_farkas result instead of copying a second Farkas proof. Source: https://github.com/elazarg/multitubes/tree/20d22aa7ca67f9843e5adf9edf173403a2f4033a. These are necessary reusable prerequisites of the circuit supplier.

Generic declarations use these source contexts: universe uV uE variable {𝕜 : Type*} [AddCommMonoid 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E} variable {𝕜g : Type*} [AddCommGroup 𝕜g] variable {𝕜g : Type*} [AddCommGroup 𝕜g] variable {𝕜p : Type*} [Add 𝕜p] [LE 𝕜p] variable {𝕜g : Type*} [AddCommGroup 𝕜g] [Preorder 𝕜g] [IsOrderedAddMonoid 𝕜g] variable {𝕜o : Type*} [AddCommMonoid 𝕜o] [Preorder 𝕜o] [IsOrderedAddMonoid 𝕜o] variable [IsOrderedCancelAddMonoid 𝕜o] variable [Finite E] variable [IsOrderedCancelAddMonoid 𝕜] universe uS uR variable {State : Type uS} {Row Action : Type uR} variable [Fintype State] [Fintype Row] universe uV uE variable {V : Type uV} {E : Type uE}

**Definition 1.1 (walkWeight).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.walkWeight`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.walkWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def walkWeight (weight : E → 𝕜) {start finish : V} (walk : G.Walk start finish) : 𝕜 := (walk.edges.map weight).sum omit [LinearOrder 𝕜] in

**Theorem 1.2 (walkWeight concat).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.walkWeight_concat`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.walkWeight_concat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem walkWeight_concat (weight : E → 𝕜) {start finish : V} (walk : G.Walk start finish) (edge : E) (legal : G.source edge = finish) : walkWeight weight (walk.concat edge legal) = walkWeight weight walk + weight edge

**Theorem 1.3 (walkWeight castFinish).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.walkWeight_castFinish`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.walkWeight_castFinish` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: @[simp] theorem walkWeight_castFinish (weight : E → 𝕜) {start finish finish' : V} (walk : G.Walk start finish) (hfinish : finish = finish') : walkWeight weight (walk.castFinish hfinish) = walkWeight weight walk

**Definition 1.4 (IsPotential).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.IsPotential`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.IsPotential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def IsPotential (G : EdgeGraph V E) (weight : E → 𝕜p) (φ : V → 𝕜p) : Prop := ∀ e : E, φ (G.source e) + weight e ≤ φ (G.target e)

**Definition 1.5 (defect).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.defect`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.defect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def defect (G : EdgeGraph V E) (weight : E → 𝕜g) (φ : V → 𝕜g) (e : E) : 𝕜g := φ (G.source e) + weight e - φ (G.target e)

**Definition 1.6 (nodupIncomingWeights).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.nodupIncomingWeights`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.nodupIncomingWeights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def nodupIncomingWeights (G : EdgeGraph V E) (weight : E → 𝕜) (vertex : V) : Set 𝕜 := {r | ∃ (start : V) (walk : G.Walk start vertex), walk.edges.Nodup ∧ walkWeight weight walk = r} omit [LinearOrder 𝕜] in

**Definition 1.7 (maxIncomingWeight).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.maxIncomingWeight`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.maxIncomingWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def maxIncomingWeight (G : EdgeGraph V E) (weight : E → 𝕜) (vertex : V) : 𝕜 := Finset.max' (Set.Finite.toFinset (finite_nodupIncomingWeights (G := G) weight vertex)) ((Set.Finite.toFinset_nonempty (finite_nodupIncomingWeights (G := G) weight vertex)).2 ⟨0, zero_mem_nodupIncomingWeights (G := G) weight vertex⟩) omit [IsOrderedAddMonoid 𝕜] in

**Definition 1.8 (IsNormalizedCertificate).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.IsNormalizedCertificate`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.IsNormalizedCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def IsNormalizedCertificate (delta : Row → State → ℝ) (coefficient : Row → ℝ) : Prop := (∀ row, 0 ≤ coefficient row) ∧ (∑ row, coefficient row = 1) ∧ ∀ state, ∑ row, coefficient row * delta row state = 0

**Definition 1.9 (certificateValue).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.certificateValue`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.certificateValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def certificateValue (base : Row → ℝ) (coefficient : Row → ℝ) : ℝ := ∑ row, coefficient row * base row

**Definition 1.10 (WorstResidualAtMost).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.WorstResidualAtMost`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.WorstResidualAtMost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def WorstResidualAtMost (delta : Row → State → ℝ) (base : Row → ℝ) (level : ℝ) : Prop := ∃ potential : State → ℝ, ∀ row, base row - dotProduct (delta row) potential ≤ level

**Theorem 1.11 (worstResidualAtMost iff normalizedDual le).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.worstResidualAtMost_iff_normalizedDual_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.worstResidualAtMost_iff_normalizedDual_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem worstResidualAtMost_iff_normalizedDual_le (delta : Row → State → ℝ) (base : Row → ℝ) (level : ℝ) : WorstResidualAtMost delta base level ↔ ∀ coefficient : Row → ℝ, IsNormalizedCertificate delta coefficient → certificateValue base coefficient ≤ level

**Definition 1.12 (WorstDirectedResidualAtMost).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.WorstDirectedResidualAtMost`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.WorstDirectedResidualAtMost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def WorstDirectedResidualAtMost (G : EdgeGraph V E) (weight : E → ℝ) (level : ℝ) : Prop := ∃ potential : V → ℝ, ∀ edge, MaxPlusPotential.defect G weight potential edge ≤ level

**Theorem 1.13 (worstDirectedResidualAtMost iff closedWalk le).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.worstDirectedResidualAtMost_iff_closedWalk_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.worstDirectedResidualAtMost_iff_closedWalk_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem worstDirectedResidualAtMost_iff_closedWalk_le [Finite E] (G : EdgeGraph V E) (weight : E → ℝ) (level : ℝ) : WorstDirectedResidualAtMost G weight level ↔ ∀ (vertex : V) (cycle : G.Walk vertex vertex), MaxPlusPotential.walkWeight weight cycle ≤ cycle.length * level

**Definition 1.14 (SignedEdge).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.SignedEdge`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.SignedEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: abbrev SignedEdge (E : Type uE) := E × Bool

**Definition 1.15 (signedDelta).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.signedDelta`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.signedDelta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def signedDelta [DecidableEq V] (G : EdgeGraph V E) : SignedEdge E → V → ℝ | (edge, false) => fun vertex => (if vertex = G.target edge then 1 else 0) - (if vertex = G.source edge then 1 else 0) | (edge, true) => fun vertex => (if vertex = G.source edge then 1 else 0) - (if vertex = G.target edge then 1 else 0)

**Theorem 1.16 (dotProduct signedDelta false).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.dotProduct_signedDelta_false`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.dotProduct_signedDelta_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem dotProduct_signedDelta_false [Fintype V] [DecidableEq V] (G : EdgeGraph V E) (edge : E) (potential : V → ℝ) : dotProduct (signedDelta G (edge, false)) potential = potential (G.target edge) - potential (G.source edge)

**Theorem 1.17 (dotProduct signedDelta true).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.dotProduct_signedDelta_true`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.dotProduct_signedDelta_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem dotProduct_signedDelta_true [Fintype V] [DecidableEq V] (G : EdgeGraph V E) (edge : E) (potential : V → ℝ) : dotProduct (signedDelta G (edge, true)) potential = potential (G.source edge) - potential (G.target edge)

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.IsNormalizedCertificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.IsPotential`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.SignedEdge`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.WorstDirectedResidualAtMost`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.WorstResidualAtMost`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.certificateValue`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.defect`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.dotProduct_signedDelta_false`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.dotProduct_signedDelta_true`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.maxIncomingWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.nodupIncomingWeights`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.signedDelta`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.walkWeight`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.walkWeight_castFinish`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.walkWeight_concat`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.worstDirectedResidualAtMost_iff_closedWalk_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual.worstResidualAtMost_iff_normalizedDual_le`
- Dependency: [D5/S3/Analytic/Convexity/FarkasAlternative](../../../Analytic/Convexity/FarkasAlternative.md)
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph](SupplierGraph.md)
