/- GID: D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/LaplacianPeakTransferTrees
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Arbitrarily large non-star trees attain the Laplacian spectral entry bound at pi. -/

/-
admission_basis: open-problem-resolution (#14801; Proved)
proof_shape: every theorem and lemma, including result: bind-only.
Escape witnesses surviving the bypass test: none.
The root decomposition is scalar rational normalization; phases applies parity
and exponential identities. Projection, evolution and transfer apply these
bind-only facts and frozen or Mathlib declarations. result supplies the named
open-problem settlement through the explicit unbounded family.
Direct frozen dependencies:
D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.exp_mulVec_of_eigenvector
statement_id: sha256:4c9f2eff40b9ab9a5dd6bf3511ef67bd738e5144793aa9213135c3c33bf35942
D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
statement_id: sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb
D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.hamiltonianPropagator_neg
statement_id: sha256:5965bdf5e9583b3548e15db5890602825b2142c2be7b5125a36b6586891c2045
Utility: none; symbolic existence over unbounded orders, with no finite computation.
proof_shape: lapPropagator_eq_source: bind-only; consumer: root_evolution.
proof_shape: card_vert: bind-only; consumer: tree_isTree.
proof_shape: neighbor_sum_root: bind-only; consumer: degree_root, lap_cell.
proof_shape: neighbor_sum_hub: bind-only; consumer: degree_hub, lap_cell.
proof_shape: neighbor_sum_leaf: bind-only; consumer: degree_leaf, lap_cell.
proof_shape: degree_root: bind-only; consumer: lap_cell, tree_isTree, tree_not_star.
proof_shape: degree_hub: bind-only; consumer: lap_cell, tree_isTree, tree_not_star.
proof_shape: degree_leaf: bind-only; consumer: lap_cell, tree_isTree.
proof_shape: tree_connected: bind-only; consumer: tree_isTree.
proof_shape: tree_isTree: bind-only; consumer: treeFin_isTree.
proof_shape: star_leaf_degree: bind-only; consumer: tree_not_star.
proof_shape: tree_not_star: bind-only; consumer: treeFin_not_star.
proof_shape: order_strictMono: bind-only; consumer: order_ge.
proof_shape: lap_cell: bind-only; consumer: wa_eigen, wb_eigen.
proof_shape: w0_eigen: bind-only; consumer: v0_eigen.
proof_shape: wa_eigen: bind-only; consumer: va_eigen.
proof_shape: wb_eigen: bind-only; consumer: vb_eigen.
proof_shape: eigA_pos: bind-only; consumer: entryA_nonneg, root_decomposition, tree_bound_coeff, tree_peak.
proof_shape: eigB_pos: bind-only; consumer: entryB_nonneg, root_decomposition, tree_bound_coeff, tree_peak.
proof_shape: eig_gap_pos: bind-only; consumer: entryA_nonneg, entryB_nonneg, root_decomposition, tree_bound_coeff.
proof_shape: order_eq_ab: bind-only; consumer: tree_bound, tree_peak.
proof_shape: root_decomposition: bind-only; consumer: fin_root_decomposition.
proof_shape: treeFin_isTree: bind-only; consumer: result.
proof_shape: treeFin_not_star: bind-only; consumer: result.
proof_shape: iso_lap_entry: bind-only; consumer: iso_lap_eigenvector.
proof_shape: iso_lap_eigenvector: bind-only; consumer: v0_eigen, va_eigen, vb_eigen.
proof_shape: specProj_mulVec: bind-only; consumer: specProj_eigenvector.
proof_shape: eig_dot_zero: bind-only; consumer: specProj_eigenvector.
proof_shape: basis_expansion: bind-only; consumer: specProj_eigenvector.
proof_shape: specProj_eigenvector: bind-only; consumer: root_projection.
proof_shape: eigenvalue_of_nonzero: bind-only; consumer: root_supported_eigenvalues.
proof_shape: v0_eigen: bind-only; consumer: root_evolution, root_projection, root_supported_eigenvalues.
proof_shape: va_eigen: bind-only; consumer: root_evolution, root_projection, root_supported_eigenvalues.
proof_shape: vb_eigen: bind-only; consumer: root_evolution, root_projection, root_supported_eigenvalues.
proof_shape: fin_root_decomposition: bind-only; consumer: root_evolution, root_projection.
proof_shape: lapIdempotent_specProj: bind-only; consumer: root_projection.
proof_shape: root_projection: bind-only; consumer: hub_projection.
proof_shape: entryA_nonneg: bind-only; consumer: tree_bound_coeff, tree_peak.
proof_shape: entryB_nonneg: bind-only; consumer: tree_bound_coeff, tree_peak.
proof_shape: hub_projection: bind-only; consumer: tree_bound_coeff.
proof_shape: root_supported_eigenvalues: bind-only; consumer: tree_bound_coeff.
proof_shape: tree_bound_coeff: bind-only; consumer: tree_bound.
proof_shape: tree_bound: bind-only; consumer: tree_peak.
proof_shape: complexify_eigenvector: bind-only; consumer: real_eigenvector_exp.
proof_shape: real_eigenvector_exp: bind-only; consumer: root_evolution.
proof_shape: complexify_add: bind-only; consumer: root_evolution.
proof_shape: complexify_smul: bind-only; consumer: root_evolution.
proof_shape: complexify_single: bind-only; consumer: root_evolution.
proof_shape: even_phase: bind-only; consumer: phases.
proof_shape: odd_phase: bind-only; consumer: phases.
proof_shape: root_evolution: bind-only; consumer: tree_peak.
proof_shape: phases: bind-only; consumer: tree_peak.
proof_shape: tree_peak: bind-only; consumer: result.
proof_shape: order_ge: bind-only; consumer: result.
proof_shape: result: bind-only; consumer: OpenProblemResolutionClaim (settlement).
proof_shape: lapIdempotent: not-applicable (definition, abbreviation or instance);
consumer: boundingEntry, hub_projection, lapIdempotent_specProj, root_projection, tree_bound_coeff.
proof_shape: boundingEntry: not-applicable (definition, abbreviation or instance);
consumer: PeakTransfer, tree_bound, tree_bound_coeff, tree_peak.
proof_shape: lapPropagator: not-applicable (definition, abbreviation or instance);
consumer: PeakTransfer, root_evolution, tree_peak.
proof_shape: PeakTransfer: not-applicable (definition, abbreviation or instance);
consumer: claim, result.
proof_shape: claim: not-applicable (definition, abbreviation or instance);
consumer: result (type).
proof_shape: tree: not-applicable (definition, abbreviation or instance);
consumer: degree_hub, degree_leaf, degree_root, lap_cell, neighbor_sum_hub, neighbor_sum_leaf, neighbor_sum_root, treeDecidableRel, treeFin, treeFin_isTree, treeFin_not_star, tree_connected, tree_isTree, tree_not_star, v0_eigen, va_eigen, vb_eigen, w0_eigen, wa_eigen, wb_eigen.
proof_shape: treeDecidableRel: not-applicable (definition, abbreviation or instance);
consumer: degree_hub, degree_leaf, degree_root, lap_cell, neighbor_sum_hub, neighbor_sum_leaf, neighbor_sum_root, tree_isTree, tree_not_star, v0_eigen, va_eigen, vb_eigen, w0_eigen, wa_eigen, wb_eigen.
proof_shape: leafCount: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hubCount, hub_projection, order, result, root_decomposition, root_evolution, root_projection, root_supported_eigenvalues, treeFin, treeFin_isTree, treeFin_not_star, tree_bound, tree_bound_coeff, tree_peak, v0, v0_eigen, va, va_eigen, vb, vb_eigen, w0, w0_eigen, wa, wa_eigen, wb, wb_eigen.
proof_shape: hubCount: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, order, result, root_decomposition, root_evolution, root_projection, root_supported_eigenvalues, treeFin, treeFin_isTree, treeFin_not_star, tree_bound, tree_bound_coeff, tree_peak, v0, v0_eigen, va, va_eigen, vb, vb_eigen, w0, w0_eigen, wa, wa_eigen, wb, wb_eigen.
proof_shape: order: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, order_eq_ab, order_ge, order_strictMono, result, root_evolution, root_projection, root_supported_eigenvalues, treeFin, treeFin_not_star, tree_bound, tree_bound_coeff, tree_peak, v0, v0_eigen, va, va_eigen, vb, vb_eigen.
proof_shape: cell: not-applicable (definition, abbreviation or instance);
consumer: lap_cell, w0, w0_eigen, wa, wa_eigen, wb, wb_eigen.
proof_shape: eigA: not-applicable (definition, abbreviation or instance);
consumer: c0, ca, cb, eigA_pos, eig_gap_pos, entryA, entryA_nonneg, entryB, entryB_nonneg, hub_projection, order_eq_ab, phases, root_decomposition, root_evolution, root_projection, root_supported_eigenvalues, tree_bound, tree_bound_coeff, tree_peak, va_eigen, wa_eigen.
proof_shape: eigB: not-applicable (definition, abbreviation or instance);
consumer: c0, ca, cb, eigB_pos, eig_gap_pos, entryA, entryA_nonneg, entryB, entryB_nonneg, hub_projection, order_eq_ab, phases, root_decomposition, root_evolution, root_projection, root_supported_eigenvalues, tree_bound, tree_bound_coeff, tree_peak, vb_eigen, wb_eigen.
proof_shape: w0: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, root_decomposition, root_supported_eigenvalues, tree_peak, v0, v0_eigen, w0_eigen.
proof_shape: wa: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, root_decomposition, root_supported_eigenvalues, tree_peak, va, va_eigen, wa_eigen.
proof_shape: wb: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, root_decomposition, root_supported_eigenvalues, tree_peak, vb, vb_eigen, wb_eigen.
proof_shape: c0: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, root_decomposition, root_evolution, root_projection, tree_bound, tree_bound_coeff, tree_peak.
proof_shape: ca: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, root_decomposition, root_evolution, root_projection, tree_peak.
proof_shape: cb: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, root_decomposition, root_evolution, root_projection, tree_peak.
proof_shape: vertEquiv: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, result, root_evolution, root_projection, root_supported_eigenvalues, treeFin, treeFin_isTree, treeFin_not_star, tree_bound, tree_bound_coeff, tree_peak, v0, v0_eigen, va, va_eigen, vb, vb_eigen.
proof_shape: treeFin: not-applicable (definition, abbreviation or instance);
consumer: hub_projection, result, root_evolution, root_projection, root_supported_eigenvalues, treeFin_not_star, tree_bound, tree_bound_coeff, tree_peak, v0_eigen, va_eigen, vb_eigen.
proof_shape: specProj: not-applicable (definition, abbreviation or instance);
consumer: root_projection, specProj_eigenvector, specProj_mulVec.
proof_shape: v0: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, root_evolution, root_projection, root_supported_eigenvalues, tree_peak.
proof_shape: va: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, root_evolution, root_projection, root_supported_eigenvalues, tree_peak.
proof_shape: vb: not-applicable (definition, abbreviation or instance);
consumer: fin_root_decomposition, hub_projection, root_evolution, root_projection, root_supported_eigenvalues, tree_peak.
proof_shape: entryA: not-applicable (definition, abbreviation or instance);
consumer: entryA_nonneg, hub_projection, tree_bound, tree_bound_coeff, tree_peak.
proof_shape: entryB: not-applicable (definition, abbreviation or instance);
consumer: entryB_nonneg, hub_projection, tree_bound, tree_bound_coeff, tree_peak.
Escape registration: Reg/D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees.lean (DTR-Declared).
-/

import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Dynamics.RationalWeightPathTransfer

open Matrix Finset
open scoped Classical Matrix.Norms.L2Operator
noncomputable section
namespace D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
set_option maxHeartbeats 1000000

section

/-- The spectral idempotent of the real Laplacian, summed over an orthonormal eigenbasis. -/
noncomputable def lapIdempotent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (theta : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := by
  classical
  let hL := G.isHermitian_lapMatrix ℝ
  exact ∑ i with hL.eigenvalues i = theta,
    vecMulVec ⇑(hL.eigenvectorBasis i) ⇑(hL.eigenvectorBasis i)
/-- The (v,u)-entry of the source bounding matrix, with each distinct eigenvalue counted once. -/
noncomputable def boundingEntry {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v u : Fin n) : ℝ := by
  classical
  let hL := G.isHermitian_lapMatrix ℝ
  exact ∑ theta ∈ univ.image hL.eigenvalues, |lapIdempotent G theta v u|
/-- The continuous-time Laplacian propagator exp(i tau L). -/
noncomputable def lapPropagator {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tau : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator
    ((G.lapMatrix ℝ).map (algebraMap ℝ ℂ)) (-tau)
private lemma lapPropagator_eq_source {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (tau : ℝ) :
    lapPropagator G tau =
      NormedSpace.exp (((tau : ℂ) * Complex.I) • (G.lapMatrix ℝ).map (algebraMap ℝ ℂ)) :=
  D5.S3.Quantum.Dynamics.RationalWeightPathTransfer.hamiltonianPropagator_neg _ _
/-- Peak state transfer between distinct vertices, at some real time. -/
def PeakTransfer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) : Prop :=
  u ≠ v ∧ ∃ tau : ℝ, ‖lapPropagator G tau v u‖ = boundingEntry G v u
open scoped Classical in
/-- Open Problem 7.1: arbitrarily large trees outside the star isomorphism class admit peak transfer. -/
def claim : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, ∃ T : SimpleGraph (Fin n),
    T.IsTree ∧ (∀ m : ℕ, IsEmpty (T ≃g completeBipartiteGraph (Fin 1) (Fin m))) ∧
      ∃ u v, PeakTransfer T u v
end

section
private def tree (k l : ℕ) : SimpleGraph (Option (Fin k × Option (Fin l))) where
  Adj x y := match x, y with
    | none, some (_, none) => True
    | some (_, none), none => True
    | some (i, none), some (j, some _) => i = j
    | some (i, some _), some (j, none) => i = j
    | _, _ => False
  symm := ⟨by
    rintro (_ | ⟨i, _ | a⟩) (_ | ⟨j, _ | b⟩) <;> simp_all⟩
  loopless := ⟨by
    rintro (_ | ⟨i, _ | a⟩) <;> simp⟩
private instance treeDecidableRel (k l : ℕ) : DecidableRel (tree k l).Adj := by
  rintro (_ | ⟨i, _ | a⟩) (_ | ⟨j, _ | b⟩) <;> dsimp [tree] <;> infer_instance
private lemma card_vert (k l : ℕ) : Fintype.card (Option (Fin k × Option (Fin l))) = 1 + k * (l + 1) := by
  simp [Fintype.card_option, Fintype.card_prod]; omega
private lemma neighbor_sum_root {R : Type*} [AddCommMonoid R] (k l : ℕ) (f : (Option (Fin k × Option (Fin l))) → R) :
    ∑ x ∈ (tree k l).neighborFinset none, f x = ∑ i, f (some (i, none)) := by
  classical
  have hn : (tree k l).neighborFinset none = univ.filter ((tree k l).Adj none) := by
    ext; simp
  rw [hn, Finset.sum_filter]
  simp [tree, Fintype.sum_option, Fintype.sum_prod_type]
private lemma neighbor_sum_hub {R : Type*} [AddCommMonoid R] (k l : ℕ) (i : Fin k)
    (f : (Option (Fin k × Option (Fin l))) → R) :
    ∑ x ∈ (tree k l).neighborFinset (some (i, none)), f x =
      f none + ∑ j, f (some (i, some j)) := by
  classical
  have hn : (tree k l).neighborFinset (some (i, none)) = univ.filter ((tree k l).Adj (some (i, none))) := by
    ext; simp
  rw [hn, Finset.sum_filter]
  simp [tree, Fintype.sum_option, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp
private lemma neighbor_sum_leaf {R : Type*} [AddCommMonoid R] (k l : ℕ) (i : Fin k) (j : Fin l)
    (f : (Option (Fin k × Option (Fin l))) → R) :
    ∑ x ∈ (tree k l).neighborFinset (some (i, some j)), f x = f (some (i, none)) := by
  classical
  have hn : (tree k l).neighborFinset (some (i, some j)) = univ.filter ((tree k l).Adj (some (i, some j))) := by
    ext; simp
  rw [hn, Finset.sum_filter]
  simp [tree, Fintype.sum_option, Fintype.sum_prod_type]
private lemma degree_root (k l : ℕ) : (tree k l).degree none = k := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones,
    neighbor_sum_root]
  simp
private lemma degree_hub (k l : ℕ) (i : Fin k) : (tree k l).degree (some (i, none)) = l + 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones,
    neighbor_sum_hub]
  simp; omega
private lemma degree_leaf (k l : ℕ) (i : Fin k) (j : Fin l) :
    (tree k l).degree (some (i, some j)) = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones,
    neighbor_sum_leaf]
private lemma tree_connected (k l : ℕ) : (tree k l).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none, ?_⟩
  rintro (_ | ⟨i, _ | j⟩)
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by trivial)
  · exact (SimpleGraph.Adj.reachable (show (tree k l).Adj none (some (i, none)) by trivial)).trans
      (SimpleGraph.Adj.reachable (show (tree k l).Adj (some (i, none)) (some (i, some j)) by rfl))
private lemma tree_isTree (k l : ℕ) : (tree k l).IsTree := by
  classical
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨tree_connected k l, ?_⟩
  have h := (tree k l).sum_degrees_eq_twice_card_edges
  have hd : ∑ x : (Option (Fin k × Option (Fin l))), (tree k l).degree x = k + k * (l + 1) + k * l := by
    rw [Fintype.sum_option]
    simp [Fintype.sum_prod_type, Fintype.sum_option, degree_root, degree_hub, degree_leaf]
    ring
  rw [hd] at h
  have hr : k + k * (l + 1) + k * l = 2 * (k * (l + 1)) := by ring
  rw [hr] at h
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    Nat.card_eq_fintype_card, card_vert]
  omega
open scoped Classical in
private lemma star_leaf_degree (m : ℕ) (v : Fin m) :
    (completeBipartiteGraph (Fin 1) (Fin m)).degree (Sum.inr v) = 1 := by
  classical
  have h : (completeBipartiteGraph (Fin 1) (Fin m)).degree (Sum.inr v) =
      ∑ x : Fin 1 ⊕ Fin m, if (completeBipartiteGraph (Fin 1) (Fin m)).Adj (Sum.inr v) x
        then (1 : ℕ) else 0 := by
    simpa only [Nat.cast_id] using (SimpleGraph.degree_eq_sum_if_adj (R := ℕ)
      (G := completeBipartiteGraph (Fin 1) (Fin m)) (Sum.inr v))
  rw [h, Fintype.sum_sum_type]
  simp [completeBipartiteGraph]
private lemma tree_not_star (k l : ℕ) (hk : 2 ≤ k) (hl : 1 ≤ l) (m : ℕ) :
    IsEmpty (tree k l ≃g completeBipartiteGraph (Fin 1) (Fin m)) := by
  classical
  refine ⟨fun e => ?_⟩
  let i : Fin k := ⟨0, by omega⟩
  have high (v : (Option (Fin k × Option (Fin l)))) (hv : 2 ≤ (tree k l).degree v) :
      e v = Sum.inl 0 := by
    cases he : e v with
    | inl x => have hx : x = 0 := Subsingleton.elim _ _; simp [hx]
    | inr x =>
        have hd := e.degree_eq v
        rw [he, star_leaf_degree] at hd
        omega
  have he := e.injective ((high none (by rw [degree_root]; exact hk)).trans
    (high (some (i, none)) (by rw [degree_hub]; omega)).symm)
  cases he
private def leafCount (s : ℕ) := s * (s + 1)
private def hubCount (s : ℕ) := leafCount s + 1
private abbrev order (s : ℕ) := 1 + hubCount s * (leafCount s + 1)
private lemma order_strictMono : StrictMono order := by
  intro s t hst
  have hc : s * (s + 1) + 1 < t * (t + 1) + 1 := by nlinarith
  dsimp [order, hubCount, leafCount]
  exact Nat.add_lt_add_left (Nat.mul_self_lt_mul_self hc) 1
end

section
private def cell {k l : ℕ} (x y z : ℝ) : (Option (Fin k × Option (Fin l))) → ℝ
  | none => x
  | some (_, none) => y
  | some (_, some _) => z
private lemma lap_cell (k l : ℕ) (x y z : ℝ) :
    (tree k l).lapMatrix ℝ *ᵥ cell x y z =
      cell ((k : ℝ) * (x - y)) (((l : ℝ) + 1) * y - x - l * z) (z - y) := by
  funext v
  rcases v with (_ | ⟨i, _ | j⟩)
  · rw [SimpleGraph.lapMatrix_mulVec_apply, degree_root, neighbor_sum_root]
    simp [cell]; ring
  · rw [SimpleGraph.lapMatrix_mulVec_apply, degree_hub, neighbor_sum_hub]
    simp [cell]; ring
  · rw [SimpleGraph.lapMatrix_mulVec_apply, degree_leaf, neighbor_sum_leaf]
    simp [cell]
private def eigA (s : ℕ) : ℝ := (s : ℝ)^2 + 1
private def eigB (s : ℕ) : ℝ := ((s : ℝ) + 1)^2 + 1
private def w0 (s : ℕ) : (Option (Fin (hubCount s) × Option (Fin (leafCount s)))) → ℝ := cell 1 1 1
private def wa (s : ℕ) : (Option (Fin (hubCount s) × Option (Fin (leafCount s)))) → ℝ :=
  cell (-(hubCount s : ℝ) * s) (-(s : ℝ)^2) 1
private def wb (s : ℕ) : (Option (Fin (hubCount s) × Option (Fin (leafCount s)))) → ℝ :=
  cell ((hubCount s : ℝ) * ((s : ℝ) + 1)) (-((s : ℝ) + 1)^2) 1
private lemma w0_eigen (s : ℕ) :
    (tree (hubCount s) (leafCount s)).lapMatrix ℝ *ᵥ w0 s = (0 : ℝ) • w0 s := by
  have hc : (cell 1 1 1 : (Option (Fin (hubCount s) × Option (Fin (leafCount s)))) → ℝ) = (fun _ => 1) := by
    funext v; rcases v with (_ | ⟨i, _ | j⟩) <;> rfl
  simpa [w0, hc] using (tree (hubCount s) (leafCount s)).lapMatrix_mulVec_const_eq_zero (R := ℝ)
private lemma wa_eigen (s : ℕ) :
    (tree (hubCount s) (leafCount s)).lapMatrix ℝ *ᵥ wa s = eigA s • wa s := by
  rw [wa, lap_cell]
  change _ = fun v => eigA s * wa s v
  funext v
  rcases v with (_ | ⟨i, _ | j⟩) <;>
    simp [wa, cell, eigA, hubCount, leafCount] <;> ring
private lemma wb_eigen (s : ℕ) :
    (tree (hubCount s) (leafCount s)).lapMatrix ℝ *ᵥ wb s = eigB s • wb s := by
  rw [wb, lap_cell]
  change _ = fun v => eigB s * wb s v
  funext v
  rcases v with (_ | ⟨i, _ | j⟩) <;>
    simp [wb, cell, eigB, hubCount, leafCount] <;> ring
private lemma eigA_pos (s : ℕ) : 0 < eigA s := by
  dsimp [eigA]; positivity
private lemma eigB_pos (s : ℕ) : 0 < eigB s := by
  dsimp [eigB]; positivity
private lemma eig_gap_pos (s : ℕ) : 0 < eigB s - eigA s := by
  dsimp [eigA, eigB]
  have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  nlinarith
private lemma order_eq_ab (s : ℕ) : (order s : ℝ) = eigA s * eigB s := by
  simp [order, hubCount, leafCount, eigA, eigB]; ring

private def c0 (s : ℕ) : ℝ := 1 / (eigA s * eigB s)
private def ca (s : ℕ) : ℝ := -1 / (eigA s * (eigB s - eigA s))
private def cb (s : ℕ) : ℝ := 1 / (eigB s * (eigB s - eigA s))
private lemma root_decomposition (s : ℕ) :
    Pi.single (none : (Option (Fin (hubCount s) × Option (Fin (leafCount s))))) (1 : ℝ) =
      c0 s • w0 s + ca s • wa s + cb s • wb s := by
  have ha := (eigA_pos s).ne'
  have hb := (eigB_pos s).ne'
  have hd := (eig_gap_pos s).ne'
  funext v
  rcases v with (_ | ⟨i, _ | j⟩) <;>
    simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      c0, ca, cb, w0, wa, wb, cell, Option.some_ne_none, if_false, if_true] <;>
    field_simp <;> simp [eigA, eigB, hubCount, leafCount] <;> ring
end

section
private def vertEquiv (k l : ℕ) : (Option (Fin k × Option (Fin l))) ≃ Fin (1 + k * (l + 1)) :=
  (Equiv.optionCongr ((Equiv.prodCongr (Equiv.refl (Fin k))
    (finSuccEquiv l).symm).trans finProdFinEquiv)).trans
      ((finSuccEquiv (k * (l + 1))).symm.trans (finCongr (Nat.add_comm _ _)))
open scoped Classical in
private def treeFin (s : ℕ) : SimpleGraph (Fin (order s)) :=
  (tree (hubCount s) (leafCount s)).map (vertEquiv (hubCount s) (leafCount s))
open scoped Classical in
private lemma treeFin_isTree (s : ℕ) : (treeFin s).IsTree :=
  (SimpleGraph.Iso.map (vertEquiv (hubCount s) (leafCount s)) _).isTree_iff.mp
    (tree_isTree _ _)
open scoped Classical in
private lemma treeFin_not_star (s : ℕ) (hs : 1 ≤ s) (m : ℕ) :
    IsEmpty (treeFin s ≃g completeBipartiteGraph (Fin 1) (Fin m)) := by
  refine ⟨fun e => ?_⟩
  have hk : 2 ≤ hubCount s := by dsimp [hubCount, leafCount]; nlinarith
  have hl : 1 ≤ leafCount s := by dsimp [leafCount]; nlinarith
  have h := tree_not_star (hubCount s) (leafCount s) hk hl m
  exact h.false (e.comp (SimpleGraph.Iso.map (vertEquiv (hubCount s) (leafCount s)) _))

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
open scoped Classical in
private lemma iso_lap_entry {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) (x y : V) :
    H.lapMatrix ℝ (e x) (e y) = G.lapMatrix ℝ x y := by
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
    Matrix.diagonal_apply, e.degree_eq, e.injective.eq_iff, e.map_adj_iff]
open scoped Classical in
private lemma iso_lap_eigenvector {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H)
    (v : V → ℝ) (theta : ℝ) (hv : G.lapMatrix ℝ *ᵥ v = theta • v) :
    H.lapMatrix ℝ *ᵥ (v ∘ e.symm) = theta • (v ∘ e.symm) := by
  funext x
  obtain ⟨x, rfl⟩ := e.surjective x
  change (∑ y, H.lapMatrix ℝ (e x) y * v (e.symm y)) = theta * v (e.symm (e x))
  rw [← e.toEquiv.sum_comp (fun y => H.lapMatrix ℝ (e x) y * v (e.symm y))]
  change (∑ y : V, H.lapMatrix ℝ (e x) (e y) * v (e.symm (e y))) = theta * v (e.symm (e x))
  simp only [e.symm_apply_apply, iso_lap_entry e]
  exact congrFun hv x
end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
private def specProj {A : Matrix V V ℝ} (hA : A.IsHermitian) (theta : ℝ) : Matrix V V ℝ := by
  classical
  exact ∑ i with hA.eigenvalues i = theta,
    vecMulVec ⇑(hA.eigenvectorBasis i) ⇑(hA.eigenvectorBasis i)
private lemma specProj_mulVec {A : Matrix V V ℝ} (hA : A.IsHermitian) (theta : ℝ) (w : V → ℝ) :
    specProj hA theta *ᵥ w = ∑ i with hA.eigenvalues i = theta,
      (⇑(hA.eigenvectorBasis i) ⬝ᵥ w) • ⇑(hA.eigenvectorBasis i) := by
  classical
  simp [specProj, sum_mulVec, vecMulVec_mulVec]
private lemma eig_dot_zero {A : Matrix V V ℝ} (hA : A.IsHermitian) (w : V → ℝ) (mu : ℝ)
    (hw : A *ᵥ w = mu • w) (i : V) (hi : hA.eigenvalues i ≠ mu) :
    ⇑(hA.eigenvectorBasis i) ⬝ᵥ w = 0 := by
  have hv : hA.eigenvectorBasis i ∈ Module.End.eigenspace A.toEuclideanLin (hA.eigenvalues i) := by
    rw [Module.End.mem_eigenspace_iff]
    apply WithLp.ofLp_injective 2
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul]
      using hA.mulVec_eigenvectorBasis i
  have hw' : WithLp.toLp 2 w ∈ Module.End.eigenspace A.toEuclideanLin mu := by
    rw [Module.End.mem_eigenspace_iff]
    apply WithLp.ofLp_injective 2
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using hw
  have ho := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).orthogonalFamily_eigenspaces hi
    ⟨hA.eigenvectorBasis i, hv⟩ ⟨WithLp.toLp 2 w, hw'⟩
  change inner ℝ (hA.eigenvectorBasis i) (WithLp.toLp 2 w) = 0 at ho
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, star_trivial, dotProduct_comm] using ho
private lemma basis_expansion {A : Matrix V V ℝ} (hA : A.IsHermitian) (w : V → ℝ) :
    ∑ i, (⇑(hA.eigenvectorBasis i) ⬝ᵥ w) • ⇑(hA.eigenvectorBasis i) = w := by
  have h := congrArg WithLp.ofLp (hA.eigenvectorBasis.sum_repr' (WithLp.toLp 2 w))
  simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct,
    WithLp.ofLp_toLp, star_trivial, dotProduct_comm] using h
private lemma specProj_eigenvector {A : Matrix V V ℝ} (hA : A.IsHermitian) (w : V → ℝ) (mu theta : ℝ)
    (hw : A *ᵥ w = mu • w) :
    specProj hA theta *ᵥ w = if theta = mu then w else 0 := by
  classical
  rw [specProj_mulVec]
  by_cases ht : theta = mu
  · subst theta
    rw [if_pos rfl]
    conv_rhs => rw [← basis_expansion hA w]
    exact sum_subset (filter_subset _ _) (by
      intro i hi hnot
      have he : hA.eigenvalues i ≠ mu := by
        intro he; exact hnot (mem_filter.mpr ⟨hi, he⟩)
      rw [eig_dot_zero hA w mu hw i he, zero_smul])
  · rw [if_neg ht]
    apply sum_eq_zero
    intro i hi
    have he : hA.eigenvalues i ≠ mu := by
      rw [(mem_filter.mp hi).2]
      exact ht
    rw [eig_dot_zero hA w mu hw i he, zero_smul]
private lemma eigenvalue_of_nonzero {A : Matrix V V ℝ} (hA : A.IsHermitian) (w : V → ℝ) (mu : ℝ)
    (hw : A *ᵥ w = mu • w) (hn : w ≠ 0) : mu ∈ univ.image hA.eigenvalues := by
  classical
  have he : Module.End.HasEigenvalue A.toLin' mu :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by simpa only [Matrix.toLin'_apply] using hw), hn⟩
  have hs : mu ∈ spectrum ℝ A := by simpa only [Matrix.spectrum_toLin'] using he.mem_spectrum
  rw [hA.spectrum_real_eq_range_eigenvalues] at hs
  simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hs
end

section
open scoped Classical

private def v0 (s : ℕ) : Fin (order s) → ℝ := w0 s ∘ (vertEquiv (hubCount s) (leafCount s)).symm
private def va (s : ℕ) : Fin (order s) → ℝ := wa s ∘ (vertEquiv (hubCount s) (leafCount s)).symm
private def vb (s : ℕ) : Fin (order s) → ℝ := wb s ∘ (vertEquiv (hubCount s) (leafCount s)).symm
private lemma v0_eigen (s : ℕ) : (treeFin s).lapMatrix ℝ *ᵥ v0 s = (0 : ℝ) • v0 s :=
  iso_lap_eigenvector (H := treeFin s) (SimpleGraph.Iso.map (vertEquiv (hubCount s) (leafCount s)) _) _ _ (w0_eigen s)
private lemma va_eigen (s : ℕ) : (treeFin s).lapMatrix ℝ *ᵥ va s = eigA s • va s :=
  iso_lap_eigenvector (H := treeFin s) (SimpleGraph.Iso.map (vertEquiv (hubCount s) (leafCount s)) _) _ _ (wa_eigen s)
private lemma vb_eigen (s : ℕ) : (treeFin s).lapMatrix ℝ *ᵥ vb s = eigB s • vb s :=
  iso_lap_eigenvector (H := treeFin s) (SimpleGraph.Iso.map (vertEquiv (hubCount s) (leafCount s)) _) _ _ (wb_eigen s)
private lemma fin_root_decomposition (s : ℕ) :
    Pi.single (((vertEquiv (hubCount s) (leafCount s)) none)) (1 : ℝ) = c0 s • v0 s + ca s • va s + cb s • vb s := by
  change Pi.single (((vertEquiv (hubCount s) (leafCount s)) none)) (1 : ℝ) = fun x =>
    c0 s * v0 s x + ca s * va s x + cb s * vb s x
  funext x
  obtain ⟨x, rfl⟩ := (vertEquiv (hubCount s) (leafCount s)).surjective x
  have h := congrFun (root_decomposition s) x
  change (Pi.single ((vertEquiv _ _) none) (1 : ℝ) : Fin (order s) → ℝ) ((vertEquiv _ _) x) =
    c0 s * w0 s ((vertEquiv _ _).symm ((vertEquiv _ _) x)) +
    ca s * wa s ((vertEquiv _ _).symm ((vertEquiv _ _) x)) +
    cb s * wb s ((vertEquiv _ _).symm ((vertEquiv _ _) x))
  rw [Pi.single_apply]
  simpa only [Equiv.symm_apply_apply, (vertEquiv _ _).injective.eq_iff,
    Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
private lemma lapIdempotent_specProj {n : ℕ} (G : SimpleGraph (Fin n)) (theta : ℝ) :
    lapIdempotent G theta = specProj (G.isHermitian_lapMatrix ℝ) theta := rfl
private lemma root_projection (s : ℕ) (theta : ℝ) :
    lapIdempotent (treeFin s) theta *ᵥ Pi.single (((vertEquiv (hubCount s) (leafCount s)) none)) 1 =
      (if theta = 0 then c0 s • v0 s else 0) +
      (if theta = eigA s then ca s • va s else 0) +
      (if theta = eigB s then cb s • vb s else 0) := by
  rw [lapIdempotent_specProj, fin_root_decomposition, mulVec_add, mulVec_add,
    mulVec_smul, mulVec_smul, mulVec_smul,
    specProj_eigenvector _ _ _ _ (v0_eigen s),
    specProj_eigenvector _ _ _ _ (va_eigen s),
    specProj_eigenvector _ _ _ _ (vb_eigen s)]
  by_cases h0 : theta = 0 <;> by_cases ha : theta = eigA s <;>
    by_cases hb : theta = eigB s <;> simp [h0, ha, hb]

private def entryA (s : ℕ) := (eigA s - 1) / (eigA s * (eigB s - eigA s))
private def entryB (s : ℕ) := (eigB s - 1) / (eigB s * (eigB s - eigA s))
private lemma entryA_nonneg (s : ℕ) : 0 ≤ entryA s := by
  dsimp [entryA]
  exact div_nonneg (by dsimp [eigA]; nlinarith [sq_nonneg (s : ℝ)])
    (mul_nonneg (eigA_pos s).le (eig_gap_pos s).le)
private lemma entryB_nonneg (s : ℕ) : 0 ≤ entryB s := by
  dsimp [entryB]
  exact div_nonneg (by dsimp [eigB]; nlinarith [sq_nonneg ((s : ℝ) + 1)])
    (mul_nonneg (eigB_pos s).le (eig_gap_pos s).le)
private lemma hub_projection (s : ℕ) (i : Fin (hubCount s)) (theta : ℝ) :
    lapIdempotent (treeFin s) theta (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) (((vertEquiv (hubCount s) (leafCount s)) none)) =
      (if theta = 0 then c0 s else 0) +
      (if theta = eigA s then entryA s else 0) +
      (if theta = eigB s then -entryB s else 0) := by
  have h := congrFun (root_projection s theta) (((vertEquiv (hubCount s) (leafCount s)) (some (i, none))))
  have hh : (lapIdempotent (treeFin s) theta *ᵥ Pi.single (((vertEquiv (hubCount s) (leafCount s)) none)) 1) (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) =
      lapIdempotent (treeFin s) theta (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) (((vertEquiv (hubCount s) (leafCount s)) none)) := by simp
  rw [hh] at h
  rw [h]
  have hv0 : v0 s (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) = 1 := by
    change w0 s ((vertEquiv _ _).symm ((vertEquiv _ _) (some (i, none)))) = _
    rw [Equiv.symm_apply_apply]; rfl
  have hva : va s (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) = -(s : ℝ)^2 := by
    change wa s ((vertEquiv _ _).symm ((vertEquiv _ _) (some (i, none)))) = _
    rw [Equiv.symm_apply_apply]; rfl
  have hvb : vb s (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) = -((s : ℝ) + 1)^2 := by
    change wb s ((vertEquiv _ _).symm ((vertEquiv _ _) (some (i, none)))) = _
    rw [Equiv.symm_apply_apply]; rfl
  simp only [Pi.add_apply, ite_apply]
  change ((if theta = 0 then c0 s * v0 s (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) else 0) +
    (if theta = eigA s then ca s * va s (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) else 0) +
    (if theta = eigB s then cb s * vb s (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) else 0)) = _
  rw [hv0, hva, hvb, mul_one]
  have hca : ca s * (-(s : ℝ)^2) = entryA s := by
    unfold ca entryA
    rw [show eigA s - 1 = (s : ℝ)^2 by simp [eigA]]
    ring
  have hcb : cb s * (-((s : ℝ) + 1)^2) = -entryB s := by
    unfold cb entryB
    rw [show eigB s - 1 = ((s : ℝ) + 1)^2 by simp [eigB]]
    ring
  rw [hca, hcb]
private lemma root_supported_eigenvalues (s : ℕ) (hs : 1 ≤ s) :
    ({0, eigA s, eigB s} : Finset ℝ) ⊆ univ.image ((treeFin s).isHermitian_lapMatrix ℝ).eigenvalues := by
  have hn0 : v0 s ≠ 0 := by
    intro h
    have := congrFun h (((vertEquiv (hubCount s) (leafCount s)) none))
    change w0 s ((vertEquiv _ _).symm ((vertEquiv _ _) none)) = 0 at this
    rw [Equiv.symm_apply_apply] at this
    norm_num [w0, cell] at this
  have hna : va s ≠ 0 := by
    intro h
    have := congrFun h (((vertEquiv (hubCount s) (leafCount s)) none))
    have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    have hkR : (0 : ℝ) < hubCount s := by dsimp [hubCount]; positivity
    change wa s ((vertEquiv _ _).symm ((vertEquiv _ _) none)) = 0 at this
    rw [Equiv.symm_apply_apply] at this
    change -(hubCount s : ℝ) * (s : ℝ) = 0 at this
    nlinarith [mul_pos hkR hsR]
  have hnb : vb s ≠ 0 := by
    intro h
    have := congrFun h (((vertEquiv (hubCount s) (leafCount s)) none))
    have hkR : (0 : ℝ) < hubCount s := by dsimp [hubCount]; positivity
    change wb s ((vertEquiv _ _).symm ((vertEquiv _ _) none)) = 0 at this
    rw [Equiv.symm_apply_apply] at this
    change (hubCount s : ℝ) * ((s : ℝ) + 1) = 0 at this
    have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    nlinarith [mul_pos hkR (show 0 < (s : ℝ) + 1 by positivity)]
  intro theta ht
  simp only [mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact eigenvalue_of_nonzero _ _ _ (v0_eigen s) hn0
  · exact eigenvalue_of_nonzero _ _ _ (va_eigen s) hna
  · exact eigenvalue_of_nonzero _ _ _ (vb_eigen s) hnb
private lemma tree_bound_coeff (s : ℕ) (hs : 1 ≤ s) (i : Fin (hubCount s)) :
    boundingEntry (treeFin s) (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) (((vertEquiv (hubCount s) (leafCount s)) none)) = c0 s + entryA s + entryB s := by
  have ha0 : eigA s ≠ 0 := (eigA_pos s).ne'
  have hb0 : eigB s ≠ 0 := (eigB_pos s).ne'
  have hab : eigA s ≠ eigB s := by have := eig_gap_pos s; linarith
  unfold boundingEntry
  rw [← sum_subset (root_supported_eigenvalues s hs) (by
    intro theta ht hn
    have hn0 : theta ≠ 0 := by intro h; exact hn (by simp [h])
    have hna : theta ≠ eigA s := by intro h; exact hn (by simp [h])
    have hnb : theta ≠ eigB s := by intro h; exact hn (by simp [h])
    rw [hub_projection, if_neg hn0, if_neg hna, if_neg hnb]
    simp)]
  have hc0 : 0 ≤ c0 s := div_nonneg zero_le_one (mul_nonneg (eigA_pos s).le (eigB_pos s).le)
  simp [Finset.sum_insert, hub_projection, ha0, ha0.symm, hb0, hb0.symm, hab, hab.symm,
    abs_of_nonneg (entryA_nonneg s), abs_of_nonneg (entryB_nonneg s),
    abs_of_nonneg hc0]
  ring
private lemma tree_bound (s : ℕ) (hs : 1 ≤ s) (i : Fin (hubCount s)) :
    boundingEntry (treeFin s) (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) (((vertEquiv (hubCount s) (leafCount s)) none)) =
      1 / (order s : ℝ) + entryA s + entryB s := by
  rw [tree_bound_coeff s hs i, order_eq_ab]
  rfl
end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
private lemma complexify_eigenvector (A : Matrix V V ℝ) (w : V → ℝ) (theta : ℝ)
    (hw : A *ᵥ w = theta • w) :
    A.map (algebraMap ℝ ℂ) *ᵥ (fun v => (algebraMap ℝ ℂ) ∘ v) w = (theta : ℂ) • (fun v => (algebraMap ℝ ℂ) ∘ v) w := by
  funext x
  change (A.map (algebraMap ℝ ℂ) *ᵥ ((algebraMap ℝ ℂ) ∘ w)) x = _
  rw [← (algebraMap ℝ ℂ).map_mulVec]
  rw [hw]
  simp [Pi.smul_apply, smul_eq_mul]
private lemma real_eigenvector_exp (A : Matrix V V ℝ) (w : V → ℝ) (theta tau : ℝ)
    (hw : A *ᵥ w = theta • w) :
    NormedSpace.exp (((tau : ℂ) * Complex.I) • A.map (algebraMap ℝ ℂ)) *ᵥ (fun v => (algebraMap ℝ ℂ) ∘ v) w =
      Complex.exp ((tau : ℂ) * Complex.I * theta) • (fun v => (algebraMap ℝ ℂ) ∘ v) w := by
  apply D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity.exp_mulVec_of_eigenvector
  rw [smul_mulVec, complexify_eigenvector A w theta hw, smul_smul]
omit [Fintype V] [DecidableEq V] in
private lemma complexify_add (v w : V → ℝ) : (fun v => (algebraMap ℝ ℂ) ∘ v) (v + w) = (fun v => (algebraMap ℝ ℂ) ∘ v) v + (fun v => (algebraMap ℝ ℂ) ∘ v) w := by
  funext x; simp [Function.comp_def]
omit [Fintype V] [DecidableEq V] in
private lemma complexify_smul (c : ℝ) (v : V → ℝ) :
    (fun v => (algebraMap ℝ ℂ) ∘ v) (c • v) = (c : ℂ) • (fun v => (algebraMap ℝ ℂ) ∘ v) v := by
  funext x; simp [Pi.smul_apply, smul_eq_mul]
omit [Fintype V] in
private lemma complexify_single (r : V) :
    (fun v => (algebraMap ℝ ℂ) ∘ v) (Pi.single r (1 : ℝ)) = Pi.single r (1 : ℂ) := by
  funext x
  by_cases hx : x = r <;> simp [hx]
private lemma even_phase (q : ℕ) (hq : Even q) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) = 1 := by
  rw [mul_comm _ (q : ℂ), Complex.exp_nat_mul, Complex.exp_pi_mul_I, hq.neg_one_pow]
private lemma odd_phase (q : ℕ) (hq : Odd q) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (q : ℂ)) = -1 := by
  rw [mul_comm _ (q : ℂ), Complex.exp_nat_mul, Complex.exp_pi_mul_I, hq.neg_one_pow]
end

section
open scoped Classical Matrix.Norms.L2Operator
private lemma root_evolution (s : ℕ) (tau : ℝ) :
    lapPropagator (treeFin s) tau *ᵥ Pi.single (((vertEquiv (hubCount s) (leafCount s)) none)) (1 : ℂ) =
      (c0 s : ℂ) • (fun v => (algebraMap ℝ ℂ) ∘ v) (v0 s) +
      (Complex.exp ((tau : ℂ) * Complex.I * eigA s) * ca s) • (fun v => (algebraMap ℝ ℂ) ∘ v) (va s) +
      (Complex.exp ((tau : ℂ) * Complex.I * eigB s) * cb s) • (fun v => (algebraMap ℝ ℂ) ∘ v) (vb s) := by
  rw [← complexify_single, fin_root_decomposition,
    complexify_add, complexify_add, complexify_smul, complexify_smul, complexify_smul]
  rw [lapPropagator_eq_source]
  rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul,
    real_eigenvector_exp _ _ _ _ (v0_eigen s),
    real_eigenvector_exp _ _ _ _ (va_eigen s),
    real_eigenvector_exp _ _ _ _ (vb_eigen s)]
  simp [smul_smul, mul_comm]
private lemma phases (s : ℕ) (hs : Odd s) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * eigA s) = 1 ∧
    Complex.exp ((Real.pi : ℂ) * Complex.I * eigB s) = -1 := by
  have ha : Even (s ^ 2 + 1) := (hs.pow).add_one
  have hb : Odd ((s + 1) ^ 2 + 1) := (hs.add_one.pow_of_ne_zero (by norm_num : 2 ≠ 0)).add_one
  have hca : (eigA s : ℂ) = ((s ^ 2 + 1 : ℕ) : ℂ) := by simp [eigA]
  have hcb : (eigB s : ℂ) = (((s + 1) ^ 2 + 1 : ℕ) : ℂ) := by simp [eigB]
  rw [hca, hcb]
  exact ⟨even_phase _ ha, odd_phase _ hb⟩
private lemma tree_peak (s : ℕ) (hs : Odd s) (hpos : 1 ≤ s) (i : Fin (hubCount s)) :
    PeakTransfer (treeFin s) (((vertEquiv (hubCount s) (leafCount s)) none)) (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) := by
  have hne : ((vertEquiv (hubCount s) (leafCount s)) none) ≠ ((vertEquiv (hubCount s) (leafCount s)) (some (i, none))) := by
    exact (vertEquiv _ _).injective.ne (by simp)
  refine ⟨hne, Real.pi, ?_⟩
  rw [tree_bound s hpos i, order_eq_ab]
  change ‖lapPropagator (treeFin s) Real.pi (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) (((vertEquiv (hubCount s) (leafCount s)) none))‖ = c0 s + entryA s + entryB s
  have he := congrFun (root_evolution s Real.pi) (((vertEquiv (hubCount s) (leafCount s)) (some (i, none))))
  have hentry : (lapPropagator (treeFin s) Real.pi *ᵥ Pi.single (((vertEquiv (hubCount s) (leafCount s)) none)) 1) (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) =
      lapPropagator (treeFin s) Real.pi (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) (((vertEquiv (hubCount s) (leafCount s)) none)) := by simp
  rw [hentry, (phases s hs).1, (phases s hs).2] at he
  have hv0 : v0 s (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) = 1 := by
    change w0 s ((vertEquiv _ _).symm ((vertEquiv _ _) (some (i, none)))) = _
    rw [Equiv.symm_apply_apply]; rfl
  have hva : va s (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) = -(s : ℝ)^2 := by
    change wa s ((vertEquiv _ _).symm ((vertEquiv _ _) (some (i, none)))) = _
    rw [Equiv.symm_apply_apply]; rfl
  have hvb : vb s (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) = -((s : ℝ) + 1)^2 := by
    change wb s ((vertEquiv _ _).symm ((vertEquiv _ _) (some (i, none)))) = _
    rw [Equiv.symm_apply_apply]; rfl
  have hval : lapPropagator (treeFin s) Real.pi (((vertEquiv (hubCount s) (leafCount s)) (some (i, none)))) (((vertEquiv (hubCount s) (leafCount s)) none)) =
      ((c0 s + entryA s + entryB s : ℝ) : ℂ) := by
    rw [he]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, Complex.coe_algebraMap,
      hv0, hva, hvb, one_mul, neg_one_mul]
    norm_cast
    push_cast
    unfold ca cb entryA entryB
    rw [show eigA s - 1 = (s : ℝ)^2 by simp [eigA],
      show eigB s - 1 = ((s : ℝ) + 1)^2 by simp [eigB]]
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (add_nonneg (add_nonneg
    (div_nonneg zero_le_one (mul_nonneg (eigA_pos s).le (eigB_pos s).le))
    (entryA_nonneg s)) (entryB_nonneg s))
private lemma order_ge (s : ℕ) : s ≤ order s := order_strictMono.id_le s

theorem result : claim := by
  intro N
  let s := 2 * N + 1
  have hs : Odd s := odd_two_mul_add_one N
  have hpos : 1 ≤ s := by dsimp [s]; omega
  have hN : N ≤ order s := (show N ≤ s by dsimp [s]; omega).trans (order_ge s)
  refine ⟨order s, hN, treeFin s, treeFin_isTree s, treeFin_not_star s hpos, ?_⟩
  let i : Fin (hubCount s) := ⟨0, by dsimp [hubCount]; omega⟩
  exact ⟨((vertEquiv (hubCount s) (leafCount s)) none), ((vertEquiv (hubCount s) (leafCount s)) (some (i, none))), tree_peak s hs hpos i⟩
end

end D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
