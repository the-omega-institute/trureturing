/- GID: D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Root-to-leaf spectral transfer, envelope monotonicity, and sharp tree constant. -/

/-
admission_basis: escape-witness
Escape witnesses surviving the bypass test:
1. spectral_envelope_and_antitonicity:
   (a) Derivative-free endpoint chord polynomial identity
       v*a*(v - a)*(1 + d)^3 + a*(a - 1)*(v + d)^3 - v*(v - 1)*(a + d)^3
         = (v - 1)*(a - 1)*(v - a)*(v*a + d^3) >= 0,
       dominating 4*(a + d)^(3/2)/(sqrt a * d^2) on [1, upperFeasibleA d].
   (b) Positive-term square decomposition
       (d^2 + 2*d + 5)^3 = (d^2 - 2*d + 5)*(d^4 + 8*d^3 + 38*d^2 + 40*d + 25) + 64*d^3
       with d₂*(d₂^2 - 2*d₂ + 5) - d₁*(d₁^2 - 2*d₁ + 5)
         = (d₂ - d₁)*((d₁ - 1)^2 + (d₂ - 1)^2 + d₁*d₂ + 3) > 0,
       proving 1 < envelopeH d₁ and strict antitonicity of envelopeG, envelopeH on (0, ∞).
2. sharp_global_spectral_transfer_bound:
   Combines root-to-leaf spectral decomposition on SimpleGraph (Fin (treeOrder k l)), slack
   identity 4*(upperFeasibleA (specD k l) - specA k l) = (k - l - 1)^2, sqrt 5 <= specD k l,
   spectral_envelope_and_antitonicity, envelopeH (sqrt 5) = C_*, and
   C_*^2 - envelopeG (sqrt 5)^2 = 8*(3 - sqrt 5)/25 > 0 to prove
   leafBoundingEntry^2 <= optimalTransferConst * n^(-3/2) and equality <-> k = 2 /\ l = 1.
Direct frozen dependencies:
  D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees (lapIdempotent, boundingEntry, lapPropagator,
  eig_dot_zero; sha256:eaa12760074ad3f2e25fbb0d69c7cc50dd9a77cb4cda1a9fa1cf193e798d8975)
  D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity.exp_mulVec_of_eigenvector
  (sha256:4c9f2eff40b9ab9a5dd6bf3511ef67bd738e5144793aa9213135c3c33bf35942)
  D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.hamiltonianPropagator
  (sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb)
  D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.hamiltonianPropagator_neg
  (sha256:5965bdf5e9583b3548e15db5890602825b2142c2be7b5125a36b6586891c2045)
Utility: none; symbolic spectral identities and universal bounds over unbounded k >= 2, l >= 1.
proof_shape: rawNeighbor_sums: bind-only;
  consumer: twoLevelTree_leaf_dynamics_and_invariance, vTheta_eigen.
proof_shape: spec_params: bind-only; consumer: fin_root_decomposition, leaf_projection,
  sharp_global_spectral_transfer_bound, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: vTheta_eigen: bind-only;
  consumer: leaf_projection, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: fin_root_decomposition: bind-only;
  consumer: leaf_projection, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: specProj_eigenvector: bind-only; consumer: leaf_projection.
proof_shape: leaf_projection: bind-only; consumer: twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: real_eigenvector_exp: bind-only; consumer: twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: twoLevelTree_leaf_dynamics_and_invariance: bind-only;
  consumer: sharp_global_spectral_transfer_bound,
  D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.
proof_shape: sq_rpow_three_halves: bind-only; consumer: sharp_global_spectral_transfer_bound,
  spectral_envelope_and_antitonicity, upperFeasible_eval.
proof_shape: envelope_pos_aux: bind-only; consumer: sharp_global_spectral_transfer_bound,
  spectral_envelope_and_antitonicity, upperFeasible_eval.
proof_shape: upperFeasible_eval: bind-only;
  consumer: sharp_global_spectral_transfer_bound, spectral_envelope_and_antitonicity.
proof_shape: spectral_envelope_and_antitonicity: content;
  consumer: sharp_global_spectral_transfer_bound,
  D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.
proof_shape: sharp_global_spectral_transfer_bound: content;
  consumer: D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSharpTransferDecay.
proof_shape: treeOrder: not-applicable; consumer: fin_root_decomposition, hubVertex, leafVertex,
  leaf_projection, rootVertex, sharp_global_spectral_transfer_bound, spec_params, twoLevelTree,
  twoLevelTree_leaf_dynamics_and_invariance, vTheta, vTheta_eigen, vertEquiv.
proof_shape: rawTree: not-applicable; consumer: rawNeighbor_sums, rawTreeDecidableRel,
  twoLevelTree, twoLevelTree_leaf_dynamics_and_invariance, vTheta_eigen, vertIso.
proof_shape: rawTreeDecidableRel: not-applicable; consumer: rawNeighbor_sums,
  twoLevelTreeDecidableRel, twoLevelTree_leaf_dynamics_and_invariance, vTheta_eigen.
proof_shape: vertEquiv: not-applicable; consumer: fin_root_decomposition, hubVertex, leafVertex,
  leaf_projection, rootVertex, twoLevelTree, twoLevelTreeDecidableRel,
  twoLevelTree_leaf_dynamics_and_invariance, vTheta, vertIso.
proof_shape: twoLevelTree: not-applicable; consumer: leafBoundingEntry, leafTransferProb,
  leaf_projection, twoLevelTreeDecidableRel, twoLevelTree_leaf_dynamics_and_invariance,
  vTheta_eigen, vertIso.
proof_shape: twoLevelTreeDecidableRel: not-applicable; consumer: leafBoundingEntry,
  leafTransferProb, leaf_projection, twoLevelTree_leaf_dynamics_and_invariance, vTheta_eigen.
proof_shape: vertIso: not-applicable;
  consumer: twoLevelTree_leaf_dynamics_and_invariance, vTheta_eigen.
proof_shape: rootVertex: not-applicable; consumer: fin_root_decomposition, leafBoundingEntry,
  leafTransferProb, leaf_projection, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: hubVertex: not-applicable; consumer: twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: leafVertex: not-applicable; consumer: leafBoundingEntry, leafTransferProb,
  leaf_projection, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: leafTransferProb: not-applicable;
  consumer: sharp_global_spectral_transfer_bound, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: leafBoundingEntry: not-applicable;
  consumer: sharp_global_spectral_transfer_bound, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: specS: not-applicable;
  consumer: sharp_global_spectral_transfer_bound, specA, specB, spec_params, vTheta_eigen.
proof_shape: specD: not-applicable; consumer: cA, cB, fin_root_decomposition, leaf_projection,
  sharp_global_spectral_transfer_bound, specA, specB, spec_params,
  twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: specA: not-applicable; consumer: c0, cA, fin_root_decomposition, leaf_projection,
  sharp_global_spectral_transfer_bound, spec_params, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: specB: not-applicable; consumer: c0, cB, fin_root_decomposition, leaf_projection,
  spec_params, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: optimalTransferConst: not-applicable; consumer: sharp_global_spectral_transfer_bound.
proof_shape: upperFeasibleA: not-applicable; consumer: sharp_global_spectral_transfer_bound,
  spec_params, spectral_envelope_and_antitonicity, upperFeasible_eval.
proof_shape: envelopeG: not-applicable;
  consumer: envelope_pos_aux, sharp_global_spectral_transfer_bound,
  spectral_envelope_and_antitonicity.
proof_shape: envelopeH: not-applicable; consumer: envelope_pos_aux,
  sharp_global_spectral_transfer_bound, spectral_envelope_and_antitonicity, upperFeasible_eval.
proof_shape: wTheta: not-applicable; consumer: fin_root_decomposition, leaf_projection,
  twoLevelTree_leaf_dynamics_and_invariance, vTheta, vTheta_eigen.
proof_shape: c0: not-applicable;
  consumer: fin_root_decomposition, leaf_projection, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: cA: not-applicable;
  consumer: fin_root_decomposition, leaf_projection, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: cB: not-applicable;
  consumer: fin_root_decomposition, leaf_projection, twoLevelTree_leaf_dynamics_and_invariance.
proof_shape: vTheta: not-applicable; consumer: fin_root_decomposition, leaf_projection,
  twoLevelTree_leaf_dynamics_and_invariance, vTheta_eigen.
Escape registration:
  Reg/D5/S3/Quantum/Dynamics/LaplacianTwoLevelTreeSpectralBound.lean (DTR-Declared).
-/

import D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees

/-! # Root-to-Leaf Laplacian Spectral Bound on Homogeneous Two-Level Trees -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Matrix Finset D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
noncomputable section
namespace D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound

/-- Vertex count `n = 1 + k (l + 1)` of the homogeneous two-level tree `T(k, l)`. -/
def treeOrder (k l : ℕ) : ℕ := 1 + k * (l + 1)
private def rawTree (k l : ℕ) : SimpleGraph (Option (Fin k × Option (Fin l))) where
  Adj x y := match x, y with
    | none, some (_, none) => True
    | some (_, none), none => True
    | some (i, none), some (j, some _) => i = j
    | some (i, some _), some (j, none) => i = j
    | _, _ => False
  symm := ⟨by rintro (_ | ⟨i, _ | a⟩) (_ | ⟨j, _ | b⟩) <;> simp_all⟩
  loopless := ⟨by rintro (_ | ⟨i, _ | a⟩) <;> simp⟩
private instance rawTreeDecidableRel (k l : ℕ) : DecidableRel (rawTree k l).Adj := by
  rintro (_ | ⟨i, _ | a⟩) (_ | ⟨j, _ | b⟩) <;> dsimp [rawTree] <;> infer_instance
private def vertEquiv (k l : ℕ) : Option (Fin k × Option (Fin l)) ≃ Fin (treeOrder k l) :=
  (Equiv.optionCongr ((Equiv.prodCongr (Equiv.refl (Fin k))
    (finSuccEquiv l).symm).trans finProdFinEquiv)).trans
      ((finSuccEquiv (k * (l + 1))).symm.trans (finCongr (Nat.add_comm _ _)))
/-- The homogeneous two-level tree `T(k, l)` on `Fin (treeOrder k l)`. -/
def twoLevelTree (k l : ℕ) : SimpleGraph (Fin (treeOrder k l)) where
  Adj u v := (rawTree k l).Adj ((vertEquiv k l).symm u) ((vertEquiv k l).symm v)
  symm := ⟨fun _ _ h => (rawTree k l).symm.symm _ _ h⟩
  loopless := ⟨fun u => (rawTree k l).loopless.irrefl ((vertEquiv k l).symm u)⟩
/-- Canonical decidable adjacency on `twoLevelTree k l`. -/
instance twoLevelTreeDecidableRel (k l : ℕ) : DecidableRel (twoLevelTree k l).Adj :=
  fun u v => rawTreeDecidableRel k l ((vertEquiv k l).symm u) ((vertEquiv k l).symm v)
private def vertIso (k l : ℕ) : rawTree k l ≃g twoLevelTree k l where
  toEquiv := vertEquiv k l
  map_rel_iff' := by
    intro a b; change (rawTree k l).Adj ((vertEquiv k l).symm (vertEquiv k l a))
      ((vertEquiv k l).symm (vertEquiv k l b)) ↔ (rawTree k l).Adj a b; simp
/-- The root vertex `r` of `twoLevelTree k l`. -/
def rootVertex (k l : ℕ) : Fin (treeOrder k l) := vertEquiv k l none
/-- The `i`-th hub vertex `h_i` of `twoLevelTree k l`. -/
def hubVertex (k l : ℕ) (i : Fin k) : Fin (treeOrder k l) := vertEquiv k l (some (i, none))
/-- The `(i, j)`-th leaf vertex `x_{i, j}` of `twoLevelTree k l`. -/
def leafVertex (k l : ℕ) (i : Fin k) (j : Fin l) : Fin (treeOrder k l) :=
  vertEquiv k l (some (i, some j))
/-- Continuous-time Laplacian root-to-leaf transfer probability `P_{k, l}(t) = |U(t)_{x, r}|^2`. -/
noncomputable def leafTransferProb (k l : ℕ) (i : Fin k) (j : Fin l) (t : ℝ) : ℝ :=
  ‖lapPropagator (twoLevelTree k l) t (leafVertex k l i j) (rootVertex k l)‖ ^ 2
/-- The distinct-eigenvalue spectral bounding-matrix entry `B_{k, l} = B(L)_{x, r}`. -/
noncomputable def leafBoundingEntry (k l : ℕ) (i : Fin k) (j : Fin l) : ℝ :=
  boundingEntry (twoLevelTree k l) (leafVertex k l i j) (rootVertex k l)
/-- Trace parameter `S = k + l + 2` of the cell-constant Laplacian quadratic. -/
noncomputable def specS (k l : ℕ) : ℝ := (k : ℝ) + (l : ℝ) + 2
/-- Discriminant parameter `d = sqrt((k - l)^2 + 4 l)` over `ℝ`. -/
noncomputable def specD (k l : ℕ) : ℝ := Real.sqrt (((k : ℝ) - (l : ℝ)) ^ 2 + 4 * (l : ℝ))
/-- Lower positive root-supported Laplacian eigenvalue `a = (S - d) / 2`. -/
noncomputable def specA (k l : ℕ) : ℝ := (specS k l - specD k l) / 2
/-- Upper positive root-supported Laplacian eigenvalue `b = (S + d) / 2`. -/
noncomputable def specB (k l : ℕ) : ℝ := (specS k l + specD k l) / 2
/-- Optimal global scaled transfer constant `C_* = 2 + 6 sqrt(5) / 5`. -/
noncomputable def optimalTransferConst : ℝ := 2 + 6 * Real.sqrt 5 / 5
/-- Upper feasible endpoint `A(d) = (d^2 - 2 d + 5) / 4` for `a` at fixed `d`. -/
noncomputable def upperFeasibleA (d : ℝ) : ℝ := (d ^ 2 - 2 * d + 5) / 4
/-- Lower-endpoint spectral envelope `G(d) = 4 (d + 1)^(3/2) / d^2`. -/
noncomputable def envelopeG (d : ℝ) : ℝ := 4 * ((d + 1) ^ ((3 : ℝ) / 2)) / (d ^ 2)
/-- Upper-endpoint spectral envelope `H(d) = (d^2 + 2 d + 5)^(3/2) / (d^2 sqrt(d^2 - 2 d + 5))`. -/
noncomputable def envelopeH (d : ℝ) : ℝ :=
  ((d ^ 2 + 2 * d + 5) ^ ((3 : ℝ) / 2)) / (d ^ 2 * Real.sqrt (d ^ 2 - 2 * d + 5))

private lemma rawNeighbor_sums {R : Type*} [AddCommMonoid R] (k l : ℕ)
    (f : Option (Fin k × Option (Fin l)) → R) :
    (∑ x ∈ (rawTree k l).neighborFinset none, f x = ∑ i, f (some (i, none))) ∧
      (∀ i : Fin k, ∑ x ∈ (rawTree k l).neighborFinset (some (i, none)), f x =
        f none + ∑ j, f (some (i, some j))) ∧
      (∀ (i : Fin k) (j : Fin l),
        ∑ x ∈ (rawTree k l).neighborFinset (some (i, some j)), f x = f (some (i, none))) := by
  classical
  have hf : ∀ v, (rawTree k l).neighborFinset v = univ.filter ((rawTree k l).Adj v) :=
    fun _ => by ext; simp
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩ <;> rw [hf, sum_filter] <;>
    simp [rawTree, Fintype.sum_option, Fintype.sum_prod_type]

private lemma spec_params {k l : ℕ} (hk : 2 ≤ k) (hl : 1 ≤ l) :
    (specD k l) ^ 2 = ((k : ℝ) - (l : ℝ)) ^ 2 + 4 * (l : ℝ) ∧ Real.sqrt 5 ≤ specD k l ∧
      0 < specD k l ∧ specB k l - specA k l = specD k l ∧
      specA k l * specB k l = (treeOrder k l : ℝ) ∧
      (specA k l) ^ 2 - specS k l * specA k l + (treeOrder k l : ℝ) = 0 ∧
      (specB k l) ^ 2 - specS k l * specB k l + (treeOrder k l : ℝ) = 0 ∧
      1 < specA k l ∧ 0 < specA k l ∧ 0 < specB k l ∧ specA k l < specB k l ∧
      specA k l ≤ upperFeasibleA (specD k l) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlR : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hdisc : (5 : ℝ) ≤ ((k : ℝ) - (l : ℝ)) ^ 2 + 4 * (l : ℝ) := by
    by_cases hl1 : l = 1
    · subst hl1; norm_num; nlinarith
    · have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (show 2 ≤ l by omega)
      nlinarith [sq_nonneg ((k : ℝ) - (l : ℝ))]
  have hdsq : (specD k l) ^ 2 = ((k : ℝ) - (l : ℝ)) ^ 2 + 4 * (l : ℝ) := by
    unfold specD; exact Real.sq_sqrt (by linarith)
  have hd_ge : Real.sqrt 5 ≤ specD k l := by unfold specD; exact Real.sqrt_le_sqrt hdisc
  have hd_pos : 0 < specD k l := lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num)) hd_ge
  have hadd : specA k l + specB k l = specS k l := by unfold specA specB; ring
  have hsub : specB k l - specA k l = specD k l := by unfold specA specB; ring
  have hmul : specA k l * specB k l = (treeOrder k l : ℝ) := by
    have h4 : 4 * (specA k l * specB k l) = (specS k l) ^ 2 - (specD k l) ^ 2 := by
      unfold specA specB; ring
    rw [hdsq] at h4; unfold specS treeOrder at *; push_cast; linarith
  have hqa : (specA k l) ^ 2 - specS k l * specA k l + (treeOrder k l : ℝ) = 0 := by
    rw [← hadd, ← hmul]; ring
  have hqb : (specB k l) ^ 2 - specS k l * specB k l + (treeOrder k l : ℝ) = 0 := by
    rw [← hadd, ← hmul]; ring
  have ha_gt : 1 < specA k l := by
    have : ((k : ℝ) + (l : ℝ)) ^ 2 - (specD k l) ^ 2 = 4 * (l : ℝ) * ((k : ℝ) - 1) := by
      rw [hdsq]; ring
    have : specD k l < (k : ℝ) + (l : ℝ) := by nlinarith [hd_pos]
    unfold specA specS; linarith
  have ha_pos : 0 < specA k l := lt_trans zero_lt_one ha_gt
  have hab_lt : specA k l < specB k l := by linarith
  have ha_le : specA k l ≤ upperFeasibleA (specD k l) := by
    have : 4 * (upperFeasibleA (specD k l) - specA k l) = ((k : ℝ) - (l : ℝ) - 1) ^ 2 := by
      unfold upperFeasibleA specA specS; linarith [hdsq]
    nlinarith [sq_nonneg ((k : ℝ) - (l : ℝ) - 1)]
  exact ⟨hdsq, hd_ge, hd_pos, hsub, hmul, hqa, hqb, ha_gt, ha_pos, lt_trans ha_pos hab_lt,
    hab_lt, ha_le⟩

private def wTheta (k l : ℕ) (θ : ℝ) : Option (Fin k × Option (Fin l)) → ℝ
  | none => (k : ℝ) * (θ - (l : ℝ) - 1)
  | some (_, none) => 1 - θ
  | some (_, some _) => 1
private def vTheta (k l : ℕ) (θ : ℝ) : Fin (treeOrder k l) → ℝ :=
  wTheta k l θ ∘ (vertEquiv k l).symm
private def c0 (k l : ℕ) : ℝ := 1 / (specA k l * specB k l)
private def cA (k l : ℕ) : ℝ := -1 / (specA k l * specD k l)
private def cB (k l : ℕ) : ℝ := 1 / (specB k l * specD k l)

private lemma vTheta_eigen (k l : ℕ) (θ : ℝ)
    (hθ : θ ^ 2 - specS k l * θ + (treeOrder k l : ℝ) = 0) :
    (twoLevelTree k l).lapMatrix ℝ *ᵥ vTheta k l θ = θ • vTheta k l θ := by
  let e := vertIso k l
  have hentry : ∀ a b, (twoLevelTree k l).lapMatrix ℝ (e a) (e b) = (rawTree k l).lapMatrix ℝ a b :=
    fun a b => by
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        Matrix.diagonal_apply, e.degree_eq, e.injective.eq_iff, e.map_adj_iff]
  have hns := rawNeighbor_sums k l (wTheta k l θ)
  have hns1 := rawNeighbor_sums k l (fun _ => (1 : ℕ))
  have hraw : (rawTree k l).lapMatrix ℝ *ᵥ wTheta k l θ = θ • wTheta k l θ := by
    funext v; unfold specS treeOrder at hθ; push_cast at hθ
    rcases v with (_ | ⟨i, _ | j⟩)
    · have hd : (rawTree k l).degree none = k := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_sum_ones, hns1.1]; simp
      rw [SimpleGraph.lapMatrix_mulVec_apply, hd, hns.1]; simp [wTheta]
      linear_combination -(k : ℝ) * hθ
    · have hd : (rawTree k l).degree (some (i, none)) = l + 1 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_sum_ones, hns1.2.1 i]; simp; omega
      rw [SimpleGraph.lapMatrix_mulVec_apply, hd, hns.2.1 i]; simp [wTheta]
      linear_combination hθ
    · have hd : (rawTree k l).degree (some (i, some j)) = 1 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_sum_ones, hns1.2.2 i j]
      rw [SimpleGraph.lapMatrix_mulVec_apply, hd, hns.2.2 i j]; simp [wTheta]
  funext x; obtain ⟨x, rfl⟩ := (vertEquiv k l).surjective x
  simp only [mulVec, dotProduct, vTheta, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [← (vertEquiv k l).sum_comp (fun y =>
    (twoLevelTree k l).lapMatrix ℝ (vertEquiv k l x) y * wTheta k l θ ((vertEquiv k l).symm y))]
  have he : ∀ a b, (twoLevelTree k l).lapMatrix ℝ (vertEquiv k l a) (vertEquiv k l b) =
      (rawTree k l).lapMatrix ℝ a b := hentry
  simp only [Equiv.symm_apply_apply, he]; exact congrFun hraw x

private lemma fin_root_decomposition {k l : ℕ} (hk : 2 ≤ k) (hl : 1 ≤ l) :
    Pi.single (rootVertex k l) (1 : ℝ) =
      c0 k l • (1 : Fin (treeOrder k l) → ℝ) + cA k l • vTheta k l (specA k l) +
        cB k l • vTheta k l (specB k l) := by
  obtain ⟨_, _, hd_pos, hsub, hmul, _, _, _, ha_pos, hb_pos, _, _⟩ := spec_params hk hl
  have ha : specA k l ≠ 0 := ha_pos.ne'; have hb : specB k l ≠ 0 := hb_pos.ne'
  have hba : specB k l - specA k l ≠ 0 := by rw [hsub]; exact hd_pos.ne'
  have hab : specA k l * specB k l = 1 + (k : ℝ) * ((l : ℝ) + 1) := by simpa [treeOrder] using hmul
  funext x; obtain ⟨w, rfl⟩ := (vertEquiv k l).surjective x
  change (Pi.single (vertEquiv k l none) (1 : ℝ) : Fin (treeOrder k l) → ℝ) (vertEquiv k l w) =
    c0 k l * 1 + cA k l * wTheta k l (specA k l) ((vertEquiv k l).symm (vertEquiv k l w)) +
      cB k l * wTheta k l (specB k l) ((vertEquiv k l).symm (vertEquiv k l w))
  rw [Equiv.symm_apply_apply]; rcases w with (_ | ⟨i, _ | j⟩)
  · simp only [Pi.single_apply, ite_true, c0, cA, cB, wTheta, ← hsub]
    field_simp; linear_combination (specB k l - specA k l) * hab
  all_goals
    simp only [Pi.single_apply, (vertEquiv k l).injective.eq_iff, reduceCtorEq, ite_false,
      c0, cA, cB, wTheta, ← hsub]; field_simp; ring
private lemma specProj_eigenvector {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℝ) (μ θ : ℝ) (hw : G.lapMatrix ℝ *ᵥ w = μ • w) :
    lapIdempotent G θ *ᵥ w = if θ = μ then w else 0 := by
  classical
  let hL := G.isHermitian_lapMatrix ℝ
  have hbasis : ∑ i, (⇑(hL.eigenvectorBasis i) ⬝ᵥ w) • ⇑(hL.eigenvectorBasis i) = w := by
    have h := congrArg WithLp.ofLp (hL.eigenvectorBasis.sum_repr' (WithLp.toLp 2 w))
    simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct,
      WithLp.ofLp_toLp, star_trivial, dotProduct_comm] using h
  have hmul : lapIdempotent G θ *ᵥ w =
      ∑ i with hL.eigenvalues i = θ,
        (⇑(hL.eigenvectorBasis i) ⬝ᵥ w) • ⇑(hL.eigenvectorBasis i) := by
    simp [lapIdempotent, sum_mulVec, vecMulVec_mulVec]
  rw [hmul]; split_ifs with ht
  · subst ht; conv_rhs => rw [← hbasis]
    exact sum_subset (filter_subset _ _) (fun i hi hnot => by
      rw [eig_dot_zero hL w θ hw i (fun he => hnot (mem_filter.mpr ⟨hi, he⟩)), zero_smul])
  · refine sum_eq_zero fun i hi => ?_
    rw [eig_dot_zero hL w μ hw i (by rw [(mem_filter.mp hi).2]; exact ht), zero_smul]
private lemma leaf_projection {k l : ℕ} (hk : 2 ≤ k) (hl : 1 ≤ l)
    (i : Fin k) (j : Fin l) (θ : ℝ) :
    lapIdempotent (twoLevelTree k l) θ (leafVertex k l i j) (rootVertex k l) =
      (if θ = 0 then c0 k l else 0) + (if θ = specA k l then cA k l else 0) +
        (if θ = specB k l then cB k l else 0) ∧
    ({0, specA k l, specB k l} : Finset ℝ) ⊆
      univ.image ((twoLevelTree k l).isHermitian_lapMatrix ℝ).eigenvalues := by
  classical
  obtain ⟨_, _, _, _, _, hqa, hqb, _, _, _, _, _⟩ := spec_params hk hl
  have hv0 : (twoLevelTree k l).lapMatrix ℝ *ᵥ (1 : Fin (treeOrder k l) → ℝ) =
      (0 : ℝ) • (1 : Fin (treeOrder k l) → ℝ) := by
    rw [zero_smul]; exact (twoLevelTree k l).lapMatrix_mulVec_one_eq_zero ℝ
  have hproj : lapIdempotent (twoLevelTree k l) θ *ᵥ Pi.single (rootVertex k l) 1 =
      (if θ = 0 then c0 k l • (1 : Fin (treeOrder k l) → ℝ) else 0) +
      (if θ = specA k l then cA k l • vTheta k l (specA k l) else 0) +
      (if θ = specB k l then cB k l • vTheta k l (specB k l) else 0) := by
    rw [fin_root_decomposition hk hl, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul,
      mulVec_smul, specProj_eigenvector _ _ _ _ hv0,
      specProj_eigenvector _ _ _ _ (vTheta_eigen k l _ hqa),
      specProj_eigenvector _ _ _ _ (vTheta_eigen k l _ hqb)]
    by_cases h0 : θ = 0 <;> by_cases ha : θ = specA k l <;>
      by_cases hb : θ = specB k l <;> simp [h0, ha, hb]
  have hv : ∀ μ, vTheta k l μ (leafVertex k l i j) = 1 := fun μ => by
    change wTheta k l μ ((vertEquiv k l).symm (vertEquiv k l (some (i, some j)))) = 1
    rw [Equiv.symm_apply_apply]; rfl
  refine ⟨?_, ?_⟩
  · have h := congrFun hproj (leafVertex k l i j)
    have hh : (lapIdempotent (twoLevelTree k l) θ *ᵥ Pi.single (rootVertex k l) 1)
        (leafVertex k l i j) =
        lapIdempotent (twoLevelTree k l) θ (leafVertex k l i j) (rootVertex k l) := by simp
    rw [hh] at h; rw [h]; simp [Pi.add_apply, ite_apply, hv]
  · let hL := (twoLevelTree k l).isHermitian_lapMatrix ℝ
    have heig : ∀ (w : Fin (treeOrder k l) → ℝ) (μ : ℝ),
        (twoLevelTree k l).lapMatrix ℝ *ᵥ w = μ • w → w ≠ 0 → μ ∈ univ.image hL.eigenvalues := by
      intro w μ hw hn
      have he : Module.End.HasEigenvalue ((twoLevelTree k l).lapMatrix ℝ).toLin' μ :=
        Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.mpr (by simpa only [Matrix.toLin'_apply] using hw), hn⟩
      have hs : μ ∈ spectrum ℝ ((twoLevelTree k l).lapMatrix ℝ) := by
        simpa only [Matrix.spectrum_toLin'] using he.mem_spectrum
      rw [hL.spectrum_real_eq_range_eigenvalues] at hs
      simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hs
    intro μ hμ; simp only [mem_insert, mem_singleton] at hμ; rcases hμ with rfl | rfl | rfl
    · exact heig _ _ hv0 (fun h => by have := congrFun h (leafVertex k l i j); norm_num at this)
    · exact heig _ _ (vTheta_eigen k l _ hqa) (fun h => by
        have := congrFun h (leafVertex k l i j); rw [hv] at this; norm_num at this)
    · exact heig _ _ (vTheta_eigen k l _ hqb) (fun h => by
        have := congrFun h (leafVertex k l i j); rw [hv] at this; norm_num at this)
private lemma real_eigenvector_exp {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (w : V → ℝ) (θ t : ℝ) (hw : A *ᵥ w = θ • w) :
    NormedSpace.exp (((t : ℂ) * Complex.I) • A.map (algebraMap ℝ ℂ)) *ᵥ ((algebraMap ℝ ℂ) ∘ w) =
      Complex.exp (Complex.I * (θ : ℂ) * (t : ℂ)) • ((algebraMap ℝ ℂ) ∘ w) := by
  open scoped Matrix.Norms.L2Operator in
  have hmap : A.map (algebraMap ℝ ℂ) *ᵥ ((algebraMap ℝ ℂ) ∘ w) =
      (θ : ℂ) • ((algebraMap ℝ ℂ) ∘ w) := by
    funext x; rw [← (algebraMap ℝ ℂ).map_mulVec, hw]; simp [Pi.smul_apply, smul_eq_mul]
  rw [show Complex.I * (θ : ℂ) * (t : ℂ) = (t : ℂ) * Complex.I * (θ : ℂ) by ring]
  apply D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity.exp_mulVec_of_eigenvector
  rw [smul_mulVec, hmap, smul_smul]
/-- Actual-tree structure, leaf-transitivity, exact propagator, and spectral bounding entry. -/
theorem twoLevelTree_leaf_dynamics_and_invariance (k l : ℕ) (hk : 2 ≤ k) (hl : 1 ≤ l)
    (i i' : Fin k) (j j' : Fin l) (t : ℝ) :
    (twoLevelTree k l).IsTree ∧
      (∃ φ : twoLevelTree k l ≃g twoLevelTree k l,
        φ (rootVertex k l) = rootVertex k l ∧
          φ (leafVertex k l i j) = leafVertex k l i' j') ∧
      leafTransferProb k l i j t = leafTransferProb k l i' j' t ∧
      leafBoundingEntry k l i j = leafBoundingEntry k l i' j' ∧
      lapPropagator (twoLevelTree k l) t (leafVertex k l i j) (rootVertex k l) =
        (1 : ℂ) / (treeOrder k l : ℂ) -
          Complex.exp (Complex.I * (specA k l : ℂ) * (t : ℂ)) /
            ((specA k l : ℂ) * (specD k l : ℂ)) +
          Complex.exp (Complex.I * (specB k l : ℂ) * (t : ℂ)) /
            ((specB k l : ℂ) * (specD k l : ℂ)) ∧
      leafBoundingEntry k l i j = 2 / (specA k l * specD k l) ∧
      leafTransferProb k l i j t ≤ (leafBoundingEntry k l i j) ^ 2 := by
  classical
  obtain ⟨_, _, hd, hsub, hmul, hqa, hqb, _, ha, hb, hab_lt, _⟩ := spec_params hk hl
  have htree : (twoLevelTree k l).IsTree := by
    have hrh : ∀ a : Fin k, (twoLevelTree k l).Adj (rootVertex k l) (hubVertex k l a) := fun a => by
      change (rawTree k l).Adj ((vertEquiv k l).symm (vertEquiv k l none))
        ((vertEquiv k l).symm (vertEquiv k l (some (a, none)))); simp [rawTree]
    have hhl : ∀ (a : Fin k) (b : Fin l),
        (twoLevelTree k l).Adj (hubVertex k l a) (leafVertex k l a b) := fun a b => by
      change (rawTree k l).Adj ((vertEquiv k l).symm (vertEquiv k l (some (a, none))))
        ((vertEquiv k l).symm (vertEquiv k l (some (a, some b)))); simp [rawTree]
    have hconn : (twoLevelTree k l).Connected :=
      (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨rootVertex k l, fun v => by
        obtain ⟨w, rfl⟩ := (vertEquiv k l).surjective v
        rcases w with (_ | ⟨a, _ | b⟩)
        · exact SimpleGraph.Reachable.refl _
        · exact (hrh a).reachable
        · exact (hrh a).reachable.trans (hhl a b).reachable⟩
    have hns1 := rawNeighbor_sums k l (fun _ => (1 : ℕ))
    have hr : (rawTree k l).IsTree := by
      rw [SimpleGraph.isTree_iff_connected_and_card]
      refine ⟨(vertIso k l).connected_iff.mpr hconn, ?_⟩
      have hdr : (rawTree k l).degree none = k := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_sum_ones, hns1.1]; simp
      have hdh : ∀ a : Fin k, (rawTree k l).degree (some (a, none)) = l + 1 := fun a => by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_sum_ones, hns1.2.1 a]; simp; omega
      have hdl : ∀ (a : Fin k) (b : Fin l), (rawTree k l).degree (some (a, some b)) = 1 :=
        fun a b => by
          rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_sum_ones, hns1.2.2 a b]
      have hsum := (rawTree k l).sum_degrees_eq_twice_card_edges
      have hdsum : ∑ x : Option (Fin k × Option (Fin l)), (rawTree k l).degree x =
          2 * (k * (l + 1)) := by
        rw [Fintype.sum_option]
        simp [Fintype.sum_prod_type, Fintype.sum_option, hdr, hdh, hdl]; ring
      have hc : Fintype.card (Option (Fin k × Option (Fin l))) = 1 + k * (l + 1) := by
        simp [Fintype.card_option, Fintype.card_prod]; omega
      rw [hdsum] at hsum
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card, hc]
      omega
    exact (vertIso k l).isTree_iff.mp hr
  have haut : ∃ φ : twoLevelTree k l ≃g twoLevelTree k l,
      φ (rootVertex k l) = rootVertex k l ∧
        φ (leafVertex k l i j) = leafVertex k l i' j' := by
    let f : Option (Fin k × Option (Fin l)) → Option (Fin k × Option (Fin l))
      | none => none
      | some (a, none) => some (Equiv.swap i i' a, none)
      | some (a, some b) => some (Equiv.swap i i' a, some (Equiv.swap j j' b))
    let e : Option (Fin k × Option (Fin l)) ≃ Option (Fin k × Option (Fin l)) :=
      { toFun := f, invFun := f,
        left_inv := by rintro (_ | ⟨a, _ | b⟩) <;> simp [f],
        right_inv := by rintro (_ | ⟨a, _ | b⟩) <;> simp [f] }
    let rawAut : rawTree k l ≃g rawTree k l :=
      { toEquiv := e, map_rel_iff' := by
          rintro (_ | ⟨a, _ | b⟩) (_ | ⟨a', _ | b'⟩) <;> dsimp [e, f, rawTree] <;>
            simp only [(Equiv.swap i i').injective.eq_iff] }
    refine ⟨(vertIso k l).symm.trans (rawAut.trans (vertIso k l)), ?_, ?_⟩
    · dsimp [vertIso, rootVertex, rawAut, e, f]; simp
    · dsimp [vertIso, leafVertex, rawAut, e, f]; simp
  have hbnd : ∀ (a : Fin k) (b : Fin l),
      leafBoundingEntry k l a b = 2 / (specA k l * specD k l) := fun a b => by
    have ha0 : specA k l ≠ 0 := ha.ne'; have hb0 : specB k l ≠ 0 := hb.ne'
    have hab : specA k l ≠ specB k l := hab_lt.ne
    unfold leafBoundingEntry boundingEntry
    rw [← sum_subset (leaf_projection hk hl a b 0).2 (fun θ _ hn => by
      rw [(leaf_projection hk hl a b θ).1]
      simp only [show θ ≠ 0 from fun h => hn (by simp [h]),
        show θ ≠ specA k l from fun h => hn (by simp [h]),
        show θ ≠ specB k l from fun h => hn (by simp [h]), ite_false, add_zero, abs_zero])]
    have h0_not : (0 : ℝ) ∉ ({specA k l, specB k l} : Finset ℝ) := by
      simp only [mem_insert, mem_singleton, not_or]; exact ⟨ha0.symm, hb0.symm⟩
    have ha_not : specA k l ∉ ({specB k l} : Finset ℝ) := by simp only [mem_singleton]; exact hab
    rw [sum_insert h0_not, sum_insert ha_not, sum_singleton]
    simp only [(leaf_projection hk hl a b _).1, ha0, ha0.symm, hb0, hb0.symm, hab, hab.symm,
      ite_true, ite_false, add_zero, zero_add]
    have hc0 : |c0 k l| = 1 / (specA k l * specB k l) :=
      abs_of_nonneg (div_nonneg zero_le_one (mul_nonneg ha.le hb.le))
    have hcA : |cA k l| = 1 / (specA k l * specD k l) := by
      unfold cA
      rw [neg_div, abs_neg, abs_of_nonneg (div_nonneg zero_le_one (mul_nonneg ha.le hd.le))]
    have hcB : |cB k l| = 1 / (specB k l * specD k l) :=
      abs_of_nonneg (div_nonneg zero_le_one (mul_nonneg hb.le hd.le))
    have hba : specB k l - specA k l ≠ 0 := by rw [hsub]; exact hd.ne'
    rw [hc0, hcA, hcB, ← hsub]; field_simp; ring
  have hprop : ∀ (a : Fin k) (b : Fin l),
      lapPropagator (twoLevelTree k l) t (leafVertex k l a b) (rootVertex k l) =
        (1 : ℂ) / (treeOrder k l : ℂ) -
          Complex.exp (Complex.I * (specA k l : ℂ) * (t : ℂ)) /
            ((specA k l : ℂ) * (specD k l : ℂ)) +
          Complex.exp (Complex.I * (specB k l : ℂ) * (t : ℂ)) /
            ((specB k l : ℂ) * (specD k l : ℂ)) := fun a b => by
    open scoped Matrix.Norms.L2Operator in
    have hv0 : (twoLevelTree k l).lapMatrix ℝ *ᵥ (1 : Fin (treeOrder k l) → ℝ) =
        (0 : ℝ) • (1 : Fin (treeOrder k l) → ℝ) := by
      rw [zero_smul]; exact (twoLevelTree k l).lapMatrix_mulVec_one_eq_zero ℝ
    have hsingle : ((algebraMap ℝ ℂ) ∘ Pi.single (rootVertex k l) (1 : ℝ)) =
        Pi.single (rootVertex k l) (1 : ℂ) := by
      funext x; by_cases hx : x = rootVertex k l <;> simp [hx]
    have hlin : ((algebraMap ℝ ℂ) ∘ (c0 k l • (1 : Fin (treeOrder k l) → ℝ) +
        cA k l • vTheta k l (specA k l) + cB k l • vTheta k l (specB k l))) =
        (c0 k l : ℂ) • ((algebraMap ℝ ℂ) ∘ (1 : Fin (treeOrder k l) → ℝ)) +
          (cA k l : ℂ) • ((algebraMap ℝ ℂ) ∘ vTheta k l (specA k l)) +
          (cB k l : ℂ) • ((algebraMap ℝ ℂ) ∘ vTheta k l (specB k l)) := by
      funext x; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hexp : lapPropagator (twoLevelTree k l) t =
        NormedSpace.exp (((t : ℂ) * Complex.I) •
          ((twoLevelTree k l).lapMatrix ℝ).map (algebraMap ℝ ℂ)) :=
      D5.S3.Quantum.Dynamics.RationalWeightPathTransfer.hamiltonianPropagator_neg _ _
    have hevol : lapPropagator (twoLevelTree k l) t *ᵥ Pi.single (rootVertex k l) (1 : ℂ) =
        (c0 k l : ℂ) • ((algebraMap ℝ ℂ) ∘ (1 : Fin (treeOrder k l) → ℝ)) +
          (Complex.exp (Complex.I * (specA k l : ℂ) * (t : ℂ)) * (cA k l : ℂ)) •
            ((algebraMap ℝ ℂ) ∘ vTheta k l (specA k l)) +
          (Complex.exp (Complex.I * (specB k l : ℂ) * (t : ℂ)) * (cB k l : ℂ)) •
            ((algebraMap ℝ ℂ) ∘ vTheta k l (specB k l)) := by
      rw [← hsingle, fin_root_decomposition hk hl, hlin, hexp, mulVec_add, mulVec_add,
        mulVec_smul, mulVec_smul, mulVec_smul, real_eigenvector_exp _ _ _ _ hv0,
        real_eigenvector_exp _ _ _ _ (vTheta_eigen k l _ hqa),
        real_eigenvector_exp _ _ _ _ (vTheta_eigen k l _ hqb)]
      simp [smul_smul, mul_comm]
    have he := congrFun hevol (leafVertex k l a b)
    have hentry : (lapPropagator (twoLevelTree k l) t *ᵥ Pi.single (rootVertex k l) (1 : ℂ))
        (leafVertex k l a b) =
        lapPropagator (twoLevelTree k l) t (leafVertex k l a b) (rootVertex k l) := by simp
    have hv : ∀ μ : ℝ, vTheta k l μ (leafVertex k l a b) = 1 := fun μ => by
      change wTheta k l μ ((vertEquiv k l).symm (vertEquiv k l (some (a, some b)))) = 1
      rw [Equiv.symm_apply_apply]; rfl
    have habC : (specA k l : ℂ) * (specB k l : ℂ) = (treeOrder k l : ℂ) := by exact_mod_cast hmul
    rw [hentry] at he; rw [he]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      Complex.coe_algebraMap, Pi.one_apply, hv, Complex.ofReal_one, mul_one]
    unfold c0 cA cB; push_cast; rw [habC]; ring
  have hle : leafTransferProb k l i j t ≤ (leafBoundingEntry k l i j) ^ 2 := by
    unfold leafTransferProb; rw [hprop i j, hbnd i j]
    have hn_exp : ∀ {μ : ℝ}, 0 < μ →
        ‖Complex.exp (Complex.I * (μ : ℂ) * (t : ℂ)) / ((μ : ℂ) * (specD k l : ℂ))‖ =
          1 / (μ * specD k l) := fun {μ} hμ => by
      rw [norm_div, show Complex.I * (μ : ℂ) * (t : ℂ) = ((μ * t : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I, show (μ : ℂ) * (specD k l : ℂ) =
          ((μ * specD k l : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    have htri : ‖(1 : ℂ) / (treeOrder k l : ℂ) -
        Complex.exp (Complex.I * (specA k l : ℂ) * (t : ℂ)) /
          ((specA k l : ℂ) * (specD k l : ℂ)) +
        Complex.exp (Complex.I * (specB k l : ℂ) * (t : ℂ)) /
          ((specB k l : ℂ) * (specD k l : ℂ))‖ ≤ 2 / (specA k l * specD k l) := by
      refine (norm_add_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans_eq ?_)
      have hba : specB k l - specA k l ≠ 0 := by rw [hsub]; exact hd.ne'
      rw [norm_div, norm_one, Complex.norm_natCast, hn_exp ha, hn_exp hb, ← hmul, ← hsub]
      field_simp; ring
    exact pow_le_pow_left₀ (norm_nonneg _) htri 2
  refine ⟨htree, haut, ?_, by rw [hbnd i j, hbnd i' j'], hprop i j, hbnd i j, hle⟩
  unfold leafTransferProb; rw [hprop i j, hprop i' j']
private lemma sq_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((3 : ℝ) / 2)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast (x ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hx,
    show ((3 : ℝ) / 2) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
private lemma envelope_pos_aux {d : ℝ} (hd : 0 < d) :
    0 < d ^ 2 - 2 * d + 5 ∧ 0 < d ^ 2 + 2 * d + 5 ∧ 0 < envelopeG d ∧ 0 < envelopeH d := by
  have hqm : 0 < d ^ 2 - 2 * d + 5 := by nlinarith [sq_nonneg (d - 1)]
  have hqp : 0 < d ^ 2 + 2 * d + 5 := by nlinarith [sq_nonneg (d + 1)]
  have hG : 0 < envelopeG d := by
    unfold envelopeG
    have : 0 < (d + 1) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _; positivity
  have hH : 0 < envelopeH d := by
    unfold envelopeH
    have : 0 < (d ^ 2 + 2 * d + 5) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hqp _
    have : 0 < Real.sqrt (d ^ 2 - 2 * d + 5) := Real.sqrt_pos.mpr hqm; positivity
  exact ⟨hqm, hqp, hG, hH⟩
private lemma upperFeasible_eval {d : ℝ} (hd : 0 < d) :
    4 * ((upperFeasibleA d + d) ^ ((3 : ℝ) / 2)) /
      (Real.sqrt (upperFeasibleA d) * d ^ 2) = envelopeH d := by
  obtain ⟨hqm, hqp, _, hHp⟩ := envelope_pos_aux hd
  have hv_pos : 0 < upperFeasibleA d := by unfold upperFeasibleA; linarith
  have hL_nonneg : 0 ≤ 4 * ((upperFeasibleA d + d) ^ ((3 : ℝ) / 2)) /
      (Real.sqrt (upperFeasibleA d) * d ^ 2) := by
    have : 0 ≤ (upperFeasibleA d + d) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    positivity
  refine (sq_eq_sq₀ hL_nonneg hHp.le).mp ?_
  unfold envelopeH
  rw [div_pow, mul_pow, mul_pow, sq_rpow_three_halves (by positivity), Real.sq_sqrt hv_pos.le,
    div_pow, mul_pow, sq_rpow_three_halves hqp.le, Real.sq_sqrt hqm.le]
  have hv4 : d ^ 2 - 2 * d + 5 = 4 * upperFeasibleA d := by unfold upperFeasibleA; ring
  have hvd4 : d ^ 2 + 2 * d + 5 = 4 * (upperFeasibleA d + d) := by unfold upperFeasibleA; ring
  have hd4 : (d ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (pow_ne_zero 2 hd.ne')
  rw [hv4, hvd4, div_eq_div_iff (mul_ne_zero hv_pos.ne' hd4)
    (mul_ne_zero hd4 (mul_ne_zero (by norm_num) hv_pos.ne'))]; ring
/-- Rational square decompositions, strict lower bound `1 < H(d)`, strict antitonicity of `G` and
`H` on `(0, ∞)`, and derivative-free endpoint domination on `[1, A(d)]`. -/
theorem spectral_envelope_and_antitonicity (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : d₁ < d₂) :
    envelopeG d₁ ^ 2 = 16 * (1 / d₁ + 3 / d₁ ^ 2 + 3 / d₁ ^ 3 + 1 / d₁ ^ 4) ∧
      envelopeH d₁ ^ 2 =
        1 + 8 / d₁ + 38 / d₁ ^ 2 + 40 / d₁ ^ 3 + 25 / d₁ ^ 4 +
          64 / (d₁ * (d₁ ^ 2 - 2 * d₁ + 5)) ∧
      1 < envelopeH d₁ ∧ envelopeG d₂ < envelopeG d₁ ∧ envelopeH d₂ < envelopeH d₁ ∧
      (∀ a : ℝ, 1 ≤ a → a ≤ upperFeasibleA d₁ →
        4 * ((a + d₁) ^ ((3 : ℝ) / 2)) / (Real.sqrt a * d₁ ^ 2) ≤
          max (envelopeG d₁) (envelopeH d₁)) := by
  have hd₂_pos : 0 < d₂ := lt_trans hd₁ hd₂
  obtain ⟨hqm1, _, hG1p, hH1p⟩ := envelope_pos_aux hd₁
  obtain ⟨_, _, hG2p, hH2p⟩ := envelope_pos_aux hd₂_pos
  have hGsq : ∀ {d : ℝ}, 0 < d →
      envelopeG d ^ 2 = 16 * (1 / d + 3 / d ^ 2 + 3 / d ^ 3 + 1 / d ^ 4) := fun {d} hd => by
    unfold envelopeG; rw [div_pow, mul_pow, sq_rpow_three_halves (by linarith)]
    have : d ≠ 0 := hd.ne'; field_simp; ring
  have hHsq : ∀ {d : ℝ}, 0 < d → envelopeH d ^ 2 =
      1 + 8 / d + 38 / d ^ 2 + 40 / d ^ 3 + 25 / d ^ 4 + 64 / (d * (d ^ 2 - 2 * d + 5)) :=
    fun {d} hd => by
      obtain ⟨hqm, hqp, _, _⟩ := envelope_pos_aux hd
      unfold envelopeH; rw [div_pow, mul_pow, sq_rpow_three_halves hqp.le, Real.sq_sqrt hqm.le]
      have hd0 : d ≠ 0 := hd.ne'; have hd4 : (d ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (pow_ne_zero 2 hd0)
      have hpoly : 1 + 8 / d + 38 / d ^ 2 + 40 / d ^ 3 + 25 / d ^ 4 =
          (d ^ 4 + 8 * d ^ 3 + 38 * d ^ 2 + 40 * d + 25) / (d ^ 2) ^ 2 := by field_simp
      rw [hpoly, div_add_div _ _ hd4 (mul_ne_zero hd0 hqm.ne'),
        div_eq_div_iff (mul_ne_zero hd4 hqm.ne') (mul_ne_zero hd4 (mul_ne_zero hd0 hqm.ne'))]
      ring
  have hG1 := hGsq hd₁; have hG2 := hGsq hd₂_pos; have hH1 := hHsq hd₁; have hH2 := hHsq hd₂_pos
  have hHgt1 : 1 < envelopeH d₁ := by
    have : 0 < 8 / d₁ + 38 / d₁ ^ 2 + 40 / d₁ ^ 3 + 25 / d₁ ^ 4 +
        64 / (d₁ * (d₁ ^ 2 - 2 * d₁ + 5)) := by positivity
    exact (sq_lt_sq₀ zero_le_one hH1p.le).mp (by rw [hH1]; linarith)
  have hp2 : d₁ ^ 2 < d₂ ^ 2 := pow_lt_pow_left₀ hd₂ hd₁.le (by norm_num)
  have hp3 : d₁ ^ 3 < d₂ ^ 3 := pow_lt_pow_left₀ hd₂ hd₁.le (by norm_num)
  have hp4 : d₁ ^ 4 < d₂ ^ 4 := pow_lt_pow_left₀ hd₂ hd₁.le (by norm_num)
  have hG_anti : envelopeG d₂ < envelopeG d₁ := by
    refine (sq_lt_sq₀ hG2p.le hG1p.le).mp ?_
    rw [hG1, hG2]
    linarith [one_div_lt_one_div_of_lt hd₁ hd₂,
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 3) (pow_pos hd₁ 2) hp2,
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 3) (pow_pos hd₁ 3) hp3,
      one_div_lt_one_div_of_lt (pow_pos hd₁ 4) hp4]
  have hH_anti : envelopeH d₂ < envelopeH d₁ := by
    have hK_diff : d₂ * (d₂ ^ 2 - 2 * d₂ + 5) - d₁ * (d₁ ^ 2 - 2 * d₁ + 5) =
        (d₂ - d₁) * ((d₁ - 1) ^ 2 + (d₂ - 1) ^ 2 + d₁ * d₂ + 3) := by ring
    have hK_lt : d₁ * (d₁ ^ 2 - 2 * d₁ + 5) < d₂ * (d₂ ^ 2 - 2 * d₂ + 5) := by
      have : 0 < (d₁ - 1) ^ 2 + (d₂ - 1) ^ 2 + d₁ * d₂ + 3 := by
        nlinarith [sq_nonneg (d₁ - 1), sq_nonneg (d₂ - 1), mul_pos hd₁ hd₂_pos]
      nlinarith [sub_pos.mpr hd₂]
    refine (sq_lt_sq₀ hH2p.le hH1p.le).mp ?_
    rw [hH1, hH2]
    linarith [div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 8) hd₁ hd₂,
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 38) (pow_pos hd₁ 2) hp2,
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 40) (pow_pos hd₁ 3) hp3,
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 25) (pow_pos hd₁ 4) hp4,
      div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 64) (mul_pos hd₁ hqm1) hK_lt]
  refine ⟨hG1, hH1, hHgt1, hG_anti, hH_anti, fun a ha1 ha2 => ?_⟩
  let v := upperFeasibleA d₁
  have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hv_pos : 0 < v := by dsimp [v]; unfold upperFeasibleA; linarith
  have hF_nonneg : 0 ≤ 4 * ((a + d₁) ^ ((3 : ℝ) / 2)) / (Real.sqrt a * d₁ ^ 2) := by
    have : 0 ≤ (a + d₁) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _; positivity
  have hF_sq : (4 * ((a + d₁) ^ ((3 : ℝ) / 2)) / (Real.sqrt a * d₁ ^ 2)) ^ 2 =
      16 * ((a + d₁) ^ 3 / a) / d₁ ^ 4 := by
    rw [div_pow, mul_pow, mul_pow, sq_rpow_three_halves (by linarith), Real.sq_sqrt ha_pos.le]
    have : a ≠ 0 := ha_pos.ne'; have : d₁ ≠ 0 := hd₁.ne'; field_simp; ring
  have hG_sq : envelopeG d₁ ^ 2 = 16 * ((1 + d₁) ^ 3 / 1) / d₁ ^ 4 := by
    unfold envelopeG; rw [div_pow, mul_pow, sq_rpow_three_halves (by linarith)]; ring
  have hH_sq : envelopeH d₁ ^ 2 = 16 * ((v + d₁) ^ 3 / v) / d₁ ^ 4 := by
    rw [← upperFeasible_eval hd₁]; change (_ / (Real.sqrt v * d₁ ^ 2)) ^ 2 = _
    rw [div_pow, mul_pow, mul_pow, sq_rpow_three_halves (by positivity), Real.sq_sqrt hv_pos.le]
    have : v ≠ 0 := hv_pos.ne'; have : d₁ ≠ 0 := hd₁.ne'; field_simp; ring
  have hchord : (a + d₁) ^ 3 / a ≤ max ((1 + d₁) ^ 3 / 1) ((v + d₁) ^ 3 / v) := by
    by_cases hv1 : v = 1
    · rw [le_antisymm (hv1 ▸ ha2) ha1]; exact le_max_left _ _
    · have hv_gt : 1 < v := lt_of_le_of_ne (ha1.trans ha2) (Ne.symm hv1)
      have hpoly : v * a * (v - a) * (1 + d₁) ^ 3 + a * (a - 1) * (v + d₁) ^ 3 -
          v * (v - 1) * (a + d₁) ^ 3 =
          (v - 1) * (a - 1) * (v - a) * (v * a + d₁ ^ 3) := by ring
      have hnonneg : 0 ≤ (v - 1) * (a - 1) * (v - a) * (v * a + d₁ ^ 3) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr ha1))
          (sub_nonneg.mpr ha2)) (by positivity)
      let M := max ((1 + d₁) ^ 3 / 1) ((v + d₁) ^ 3 / v)
      have hM1 : (1 + d₁) ^ 3 ≤ M := by
        have hm : (1 + d₁) ^ 3 / 1 ≤ M := le_max_left _ _; rwa [div_one] at hm
      have hMv : (v + d₁) ^ 3 ≤ v * M := by
        have hm : (v + d₁) ^ 3 / v ≤ M := le_max_right _ _
        rwa [div_le_iff₀ hv_pos, mul_comm] at hm
      have hstep2 : v * a * (v - a) * (1 + d₁) ^ 3 ≤ v * a * (v - a) * M :=
        mul_le_mul_of_nonneg_left hM1 (mul_nonneg (mul_nonneg hv_pos.le ha_pos.le)
          (sub_nonneg.mpr ha2))
      have hstep3 : a * (a - 1) * (v + d₁) ^ 3 ≤ a * (a - 1) * (v * M) :=
        mul_le_mul_of_nonneg_left hMv (mul_nonneg ha_pos.le (sub_nonneg.mpr ha1))
      have haM : (a + d₁) ^ 3 ≤ a * M :=
        le_of_mul_le_mul_left
          (by linarith : v * (v - 1) * (a + d₁) ^ 3 ≤ v * (v - 1) * (a * M))
          (mul_pos hv_pos (by linarith))
      rw [div_le_iff₀ ha_pos]; linarith
  rcases le_max_iff.mp hchord with hL | hR
  · refine le_max_of_le_left ((sq_le_sq₀ hF_nonneg hG1p.le).mp ?_)
    rw [hF_sq, hG_sq]; gcongr
  · refine le_max_of_le_right ((sq_le_sq₀ hF_nonneg hH1p.le).mp ?_)
    rw [hF_sq, hH_sq]; gcongr

/-- Optimal global spectral transfer bound on `T(k, l)` and `(k, l) = (2, 1)` equality. -/
theorem sharp_global_spectral_transfer_bound (k l : ℕ) (hk : 2 ≤ k) (hl : 1 ≤ l)
    (i : Fin k) (j : Fin l) (t : ℝ) :
    Real.sqrt 5 ≤ specD k l ∧ 1 < specA k l ∧ specA k l ≤ upperFeasibleA (specD k l) ∧
      (treeOrder k l : ℝ) = specA k l * (specA k l + specD k l) ∧
      ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 ≤
        max (envelopeG (specD k l)) (envelopeH (specD k l)) ∧
      leafTransferProb k l i j t ≤ (leafBoundingEntry k l i j) ^ 2 ∧
      (leafBoundingEntry k l i j) ^ 2 ≤
        optimalTransferConst * ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2)) ∧
      (((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 =
        optimalTransferConst ↔ k = 2 ∧ l = 1) := by
  obtain ⟨hdsq, hd_ge, hd_pos, hsub, hmul, _, _, ha_gt, ha_pos, _, _, ha_le⟩ := spec_params hk hl
  have hn_eq : (treeOrder k l : ℝ) = specA k l * (specA k l + specD k l) := by
    rw [← hmul, ← hsub]; ring
  have hn_pos : 0 < (treeOrder k l : ℝ) := by rw [hn_eq]; positivity
  have hdyn := twoLevelTree_leaf_dynamics_and_invariance k l hk hl i i j j t
  have henv := spectral_envelope_and_antitonicity (specD k l) (specD k l + 1) hd_pos (by linarith)
  have hFeq : ∀ {k' l' : ℕ} (hk' : 2 ≤ k') (hl' : 1 ≤ l') (i' : Fin k') (j' : Fin l'),
      ((treeOrder k' l' : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k' l' i' j') ^ 2 =
        4 * ((specA k' l' + specD k' l') ^ ((3 : ℝ) / 2)) /
          (Real.sqrt (specA k' l') * (specD k' l') ^ 2) := fun {k' l'} hk' hl' i' j' => by
    obtain ⟨_, _, hd', hsub', hmul', _, _, _, ha', _, _, _⟩ := spec_params hk' hl'
    have hn' : (treeOrder k' l' : ℝ) = specA k' l' * (specA k' l' + specD k' l') := by
      rw [← hmul', ← hsub']; ring
    have hnp' : 0 < (treeOrder k' l' : ℝ) := by rw [hn']; positivity
    rw [(twoLevelTree_leaf_dynamics_and_invariance k' l' hk' hl' i' i' j' j' 0).2.2.2.2.2.1]
    have hLn : 0 ≤ ((treeOrder k' l' : ℝ) ^ ((3 : ℝ) / 2)) *
        (2 / (specA k' l' * specD k' l')) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hnp'.le _) (sq_nonneg _)
    have hRn : 0 ≤ 4 * ((specA k' l' + specD k' l') ^ ((3 : ℝ) / 2)) /
        (Real.sqrt (specA k' l') * (specD k' l') ^ 2) := by
      have : 0 ≤ (specA k' l' + specD k' l') ^ ((3 : ℝ) / 2) :=
        Real.rpow_nonneg (by positivity) _; positivity
    refine (sq_eq_sq₀ hLn hRn).mp ?_
    rw [mul_pow, sq_rpow_three_halves hnp'.le, div_pow, div_pow, mul_pow, mul_pow,
      div_pow, mul_pow, mul_pow, sq_rpow_three_halves (by positivity), Real.sq_sqrt ha'.le, hn']
    have : specA k' l' ≠ 0 := ha'.ne'; have : specD k' l' ≠ 0 := hd'.ne'; field_simp; ring
  have hscaled_le : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 ≤
      max (envelopeG (specD k l)) (envelopeH (specD k l)) := by
    rw [hFeq hk hl i j]; exact henv.2.2.2.2.2 (specA k l) ha_gt.le ha_le
  have hq_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hq_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  obtain ⟨hqm, hqp, hGq_pos, hHq_pos⟩ := envelope_pos_aux hq_pos
  have hC_pos : 0 < optimalTransferConst := by unfold optimalTransferConst; positivity
  have hHq : envelopeH (Real.sqrt 5) = optimalTransferConst := by
    refine (sq_eq_sq₀ hHq_pos.le hC_pos.le).mp ?_
    unfold envelopeH optimalTransferConst
    rw [div_pow, mul_pow, sq_rpow_three_halves hqp.le, Real.sq_sqrt hqm.le, hq_sq,
      div_eq_iff (by nlinarith : (5 : ℝ) ^ 2 * (5 - 2 * Real.sqrt 5 + 5) ≠ 0)]
    linear_combination 80 * Real.sqrt 5 * hq_sq
  have hGq : envelopeG (Real.sqrt 5) < optimalTransferConst := by
    refine (sq_lt_sq₀ hGq_pos.le hC_pos.le).mp ?_
    have hdiff : optimalTransferConst ^ 2 - envelopeG (Real.sqrt 5) ^ 2 =
        8 * (3 - Real.sqrt 5) / 25 := by
      unfold envelopeG optimalTransferConst
      rw [hq_sq, div_pow, mul_pow, sq_rpow_three_halves (by positivity)]
      linear_combination (-16 * Real.sqrt 5 - 12) / 25 * hq_sq
    have hq_lt3 : Real.sqrt 5 < 3 :=
      (sq_lt_sq₀ hq_pos.le (by norm_num)).mp (by rw [hq_sq]; norm_num)
    linarith
  have hmax_le : max (envelopeG (specD k l)) (envelopeH (specD k l)) ≤ optimalTransferConst := by
    rcases lt_or_eq_of_le hd_ge with hlt | heq
    · have hanti := spectral_envelope_and_antitonicity (Real.sqrt 5) (specD k l) hq_pos hlt
      exact max_le (le_of_lt (lt_trans hanti.2.2.2.1 hGq)) (le_of_lt (hHq ▸ hanti.2.2.2.2.1))
    · rw [← heq, hHq, max_eq_right hGq.le]
  have hscaled_C : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) * (leafBoundingEntry k l i j) ^ 2 ≤
      optimalTransferConst := hscaled_le.trans hmax_le
  have hbound_C : (leafBoundingEntry k l i j) ^ 2 ≤
      optimalTransferConst * ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2)) := by
    have hmul_le := mul_le_mul_of_nonneg_right hscaled_C
      (Real.rpow_nonneg hn_pos.le (-(3 : ℝ) / 2))
    have hrpow : ((treeOrder k l : ℝ) ^ ((3 : ℝ) / 2)) *
        ((treeOrder k l : ℝ) ^ (-(3 : ℝ) / 2)) = 1 := by
      rw [← Real.rpow_add hn_pos]; norm_num
    rwa [mul_right_comm, hrpow, one_mul] at hmul_le
  refine ⟨hd_ge, ha_gt, ha_le, hn_eq, hscaled_le, hdyn.2.2.2.2.2.2, hbound_C, ?_⟩
  constructor
  · intro heq
    have hd_eq : specD k l = Real.sqrt 5 := by
      by_contra hne
      have hlt : Real.sqrt 5 < specD k l := lt_of_le_of_ne hd_ge (Ne.symm hne)
      have hanti := spectral_envelope_and_antitonicity (Real.sqrt 5) (specD k l) hq_pos hlt
      have : max (envelopeG (specD k l)) (envelopeH (specD k l)) < optimalTransferConst :=
        max_lt (lt_trans hanti.2.2.2.1 hGq) (hHq ▸ hanti.2.2.2.2.1)
      linarith
    have hdisc5 : ((k : ℝ) - (l : ℝ)) ^ 2 + 4 * (l : ℝ) = 5 := by rw [← hdsq, hd_eq, hq_sq]
    have hl1 : l = 1 := by
      by_contra hnl
      have hl2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (show 2 ≤ l by omega)
      linarith [sq_nonneg ((k : ℝ) - (l : ℝ))]
    subst hl1
    have hk2 : k = 2 := by
      have hkR2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hksq : ((k : ℝ) - 1) ^ 2 = 1 ^ 2 := by push_cast at hdisc5; linarith
      have hk1 : (k : ℝ) - 1 = 1 := (sq_eq_sq₀ (by linarith) zero_le_one).mp hksq
      exact_mod_cast (show (k : ℝ) = 2 by linarith)
    exact ⟨hk2, rfl⟩
  · rintro ⟨rfl, rfl⟩
    have hd21 : specD 2 1 = Real.sqrt 5 := by unfold specD; congr 1; norm_num
    have ha21 : specA 2 1 = upperFeasibleA (Real.sqrt 5) := by
      unfold specA specS upperFeasibleA; rw [hd21, hq_sq]; ring
    rw [hFeq hk hl i j, hd21, ha21, upperFeasible_eval hq_pos, hHq]

end D5.S3.Quantum.Dynamics.LaplacianTwoLevelTreeSpectralBound
