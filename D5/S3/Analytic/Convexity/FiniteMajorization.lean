/- GID: D5/S3/Analytic/Convexity/FiniteMajorization
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/FiniteMajorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: FiniteMajorization for compact scalar martingale transport. -/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/econlib-strassen/LICENSE.txt.
Authors: Daniel Lyng
Ported from danlyng/Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f.
Modified for the host probability-measure API, native conditional expectation,
existing library suppliers, and a construction-oriented module organization.
-/
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Hom
import Mathlib.Data.Real.StarOrdered


open Set Filter Topology

section
open Set

lemma convexOn_hinge_right (a : ℝ) :
    ConvexOn ℝ Set.univ (fun z : ℝ => max (z - a) 0) := by
  have hid : ConvexOn ℝ (Set.univ : Set ℝ) id := convexOn_id convex_univ
  convert (hid.add_const (-a)).sup (convexOn_const 0 convex_univ) using 1 <;>
    ext z <;> simp [sub_eq_add_neg]

end

section
open Finset Set BigOperators

/-- For any subset `S ⊆ Fin n` of size `k` and threshold `t`, the `S`-sum of `v` is bounded above
by `k · t` plus the total positive-part sum `∑ max (v - t) 0`. -/
private lemma subset_sum_le_scale_plus_hinge {n : ℕ} (v : Fin n → ℝ) {k : ℕ}
    (S : Finset (Fin n)) (hS : S.card = k) (t : ℝ) :
    ∑ i ∈ S, v i ≤ (k : ℝ) * t + ∑ i, max (v i - t) 0 := by
  have h_sub : ∑ i ∈ S, (v i - t) = ∑ i ∈ S, v i - (k : ℝ) * t := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hS, nsmul_eq_mul]
  have h_le_max : ∑ i ∈ S, (v i - t) ≤ ∑ i ∈ S, max (v i - t) 0 :=
    Finset.sum_le_sum (fun i _ => le_max_left _ _)
  have h_le_univ : ∑ i ∈ S, max (v i - t) 0 ≤ ∑ i, max (v i - t) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg S.subset_univ
      (fun i _ _ => le_max_right _ _)
  linarith

/-- Given a monotone vector `d` and vectors `x, y` with equal total sums but `∑ d · x < ∑ d · y`,
there is a prefix index `k` (with `k + 1 < n`) whose `x`-prefix sum strictly exceeds the `y`-prefix
sum. -/
private lemma abel_pull_partial_sum {n : ℕ} (d x y : Fin n → ℝ)
    (hd_mono : Monotone d)
    (hsum : ∑ i, x i = ∑ i, y i)
    (hfact : ∑ i, d i * x i < ∑ i, d i * y i) :
    ∃ k : Fin n, k.val + 1 < n ∧
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k.val), y i) <
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k.val), x i) := by
  classical
  by_contra hno
  push Not at hno
  set D : ℕ → ℝ := fun i => if h : i < n then d ⟨i, h⟩ else 0 with hD_def
  set X : ℕ → ℝ := fun i => if h : i < n then x ⟨i, h⟩ else 0 with hX_def
  set Y : ℕ → ℝ := fun i => if h : i < n then y ⟨i, h⟩ else 0 with hY_def
  have eqD : ∀ i : Fin n, d i = D i.val := fun i => by simp [hD_def, i.isLt]
  have eqX : ∀ i : Fin n, x i = X i.val := fun i => by simp [hX_def, i.isLt]
  have eqY : ∀ i : Fin n, y i = Y i.val := fun i => by simp [hY_def, i.isLt]
  have hsum_X : (∑ i, x i) = ∑ i ∈ Finset.range n, X i := by
    calc (∑ i, x i) = ∑ i : Fin n, X i.val :=
          Finset.sum_congr rfl fun i _ => eqX i
      _ = ∑ i ∈ Finset.range n, X i := Fin.sum_univ_eq_sum_range X n
  have hsum_Y : (∑ i, y i) = ∑ i ∈ Finset.range n, Y i := by
    calc (∑ i, y i) = ∑ i : Fin n, Y i.val :=
          Finset.sum_congr rfl fun i _ => eqY i
      _ = ∑ i ∈ Finset.range n, Y i := Fin.sum_univ_eq_sum_range Y n
  have hsum_dX : (∑ i, d i * x i) = ∑ i ∈ Finset.range n, D i * X i := by
    calc (∑ i, d i * x i) = ∑ i : Fin n, D i.val * X i.val := by
          refine Finset.sum_congr rfl fun i _ => ?_; rw [eqD i, eqX i]
      _ = ∑ i ∈ Finset.range n, D i * X i :=
          Fin.sum_univ_eq_sum_range (fun i => D i * X i) n
  have hsum_dY : (∑ i, d i * y i) = ∑ i ∈ Finset.range n, D i * Y i := by
    calc (∑ i, d i * y i) = ∑ i : Fin n, D i.val * Y i.val := by
          refine Finset.sum_congr rfl fun i _ => ?_; rw [eqD i, eqY i]
      _ = ∑ i ∈ Finset.range n, D i * Y i :=
          Fin.sum_univ_eq_sum_range (fun i => D i * Y i) n
  have hfilter_range : ∀ k : ℕ, k < n →
      ∀ (v : Fin n → ℝ) (V : ℕ → ℝ), (∀ i : Fin n, v i = V i.val) →
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k), v i) =
          ∑ i ∈ Finset.range (k + 1), V i := by
    intro k hk v V hv
    rw [Finset.sum_filter]
    rw [show (∑ i : Fin n, if i.val ≤ k then v i else 0) =
        ∑ i : Fin n, if i.val ≤ k then V i.val else 0 from Finset.sum_congr rfl
          (fun i _ => by
            split_ifs with h
            · exact hv i
            · rfl)]
    rw [show (∑ i : Fin n, if i.val ≤ k then V i.val else 0) =
        ∑ i ∈ Finset.range n, if i ≤ k then V i else 0 from
          Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≤ k then V j else 0) n]
    have hsubset : Finset.range (k + 1) ⊆ Finset.range n := by
      intro i hi
      rw [Finset.mem_range] at hi ⊢; omega
    rw [← Finset.sum_subset hsubset (fun i hi hi' => by
      rw [Finset.mem_range] at hi'
      have : ¬ (i ≤ k) := by omega
      rw [if_neg this])]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [if_pos (by omega)]
  have hD_mono : ∀ i, i + 1 < n → D i ≤ D (i + 1) := fun i hi => by
    have h1 : i < n := by omega
    have h2 : i + 1 < n := hi
    have : d ⟨i, h1⟩ ≤ d ⟨i + 1, h2⟩ := hd_mono (by change i ≤ i + 1; omega)
    simp only [hD_def, dif_pos h1, dif_pos h2]
    exact this
  have hsum_XY : (∑ i ∈ Finset.range n, X i) = ∑ i ∈ Finset.range n, Y i := by
    rw [← hsum_X, ← hsum_Y]; exact hsum
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · subst hn0
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hfact
    exact absurd hfact (lt_irrefl 0)
  have hrange_eq_ico : Finset.range n = Finset.Ico 0 n := by
    rw [Finset.range_eq_Ico]
  have habel : ∀ (V : ℕ → ℝ),
      (∑ i ∈ Finset.range n, D i * V i) =
        D (n - 1) * (∑ i ∈ Finset.range n, V i) -
        ∑ i ∈ Finset.Ico 0 (n - 1), (D (i + 1) - D i) * ∑ j ∈ Finset.range (i + 1), V j := by
    intro V
    have hby_parts := Finset.sum_Ico_by_parts (R := ℝ) (M := ℝ) D V hn_pos
    simp only [smul_eq_mul, Finset.sum_range_zero, mul_zero, sub_zero] at hby_parts
    rw [show (Finset.range n : Finset ℕ) = Finset.Ico 0 n from hrange_eq_ico] at *
    exact hby_parts
  have habelX := habel X
  have habelY := habel Y
  have hdiff :
      (∑ i ∈ Finset.range n, D i * X i) - (∑ i ∈ Finset.range n, D i * Y i) =
      - ∑ i ∈ Finset.Ico 0 (n - 1),
          (D (i + 1) - D i) * (∑ j ∈ Finset.range (i + 1), X j -
            ∑ j ∈ Finset.range (i + 1), Y j) := by
    rw [habelX, habelY, hsum_XY]
    set A : ℝ := D (n - 1) * ∑ i ∈ Finset.range n, Y i
    set SX : ℝ := ∑ i ∈ Finset.Ico 0 (n - 1),
        (D (i + 1) - D i) * ∑ j ∈ Finset.range (i + 1), X j
    set SY : ℝ := ∑ i ∈ Finset.Ico 0 (n - 1),
        (D (i + 1) - D i) * ∑ j ∈ Finset.range (i + 1), Y j
    have h_SX_SY :
        (∑ i ∈ Finset.Ico 0 (n - 1),
          (D (i + 1) - D i) * (∑ j ∈ Finset.range (i + 1), X j -
            ∑ j ∈ Finset.range (i + 1), Y j)) = SX - SY := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    linarith [h_SX_SY]
  have hterm_nonpos : ∀ i ∈ Finset.Ico 0 (n - 1),
      (D (i + 1) - D i) * (∑ j ∈ Finset.range (i + 1), X j -
        ∑ j ∈ Finset.range (i + 1), Y j) ≤ 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi_lt : i + 1 < n := by omega
    have hi_fin : i < n := by omega
    have hfactor_nonneg : 0 ≤ D (i + 1) - D i := by
      have := hD_mono i hi_lt; linarith
    have hpartial_le :
        (∑ j ∈ Finset.range (i + 1), X j) ≤ ∑ j ∈ Finset.range (i + 1), Y j := by
      have h1 := hno ⟨i, hi_fin⟩ hi_lt
      have hlhs := hfilter_range i hi_fin x X eqX
      have hrhs := hfilter_range i hi_fin y Y eqY
      linarith
    have : (∑ j ∈ Finset.range (i + 1), X j) - (∑ j ∈ Finset.range (i + 1), Y j) ≤ 0 := by
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hfactor_nonneg this
  have hsum_nonpos :
      (∑ i ∈ Finset.Ico 0 (n - 1),
          (D (i + 1) - D i) * (∑ j ∈ Finset.range (i + 1), X j -
            ∑ j ∈ Finset.range (i + 1), Y j)) ≤ 0 :=
    Finset.sum_nonpos hterm_nonpos
  have hcontra : (∑ i ∈ Finset.range n, D i * Y i) ≤ ∑ i ∈ Finset.range n, D i * X i := by
    linarith
  have hfact_nat :
      (∑ i ∈ Finset.range n, D i * X i) < ∑ i ∈ Finset.range n, D i * Y i := by
    rw [← hsum_dX, ← hsum_dY]; exact hfact
  linarith

/-- **Hardy–Littlewood–Pólya majorization theorem.** If `x, y : Fin n → ℝ` have equal sum and
`∑ φ(x) ≤ ∑ φ(y)` for every convex `φ : ℝ → ℝ`, then there exists a doubly stochastic matrix `D`
with `D *ᵥ y = x`. -/
theorem exists_doublyStochastic_mulVec_of_convex_dominates
    {n : ℕ} (x y : Fin n → ℝ)
    (hxy : ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → ∑ i, φ (x i) ≤ ∑ j, φ (y j))
    (hsum : ∑ i, x i = ∑ j, y j) :
    ∃ D : Matrix (Fin n) (Fin n) ℝ,
      D ∈ doublyStochastic ℝ (Fin n) ∧ D.mulVec y = x := by
  classical
  let L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun D => D.mulVec y
      map_add' := fun A B => by ext i; simp [Matrix.add_mulVec]
      map_smul' := fun r A => by ext i; simp [Matrix.smul_mulVec] }
  set target : Set (Fin n → ℝ) := L '' (doublyStochastic ℝ (Fin n) : Set _) with htarget_def
  have hds_hull : (doublyStochastic ℝ (Fin n) : Set _) =
      convexHull ℝ {M | ∃ σ : Equiv.Perm (Fin n), Equiv.Perm.permMatrix ℝ σ = M} :=
    doublyStochastic_eq_convexHull_permMatrix
  have htarget_hull : target = convexHull ℝ (Set.range (fun σ : Equiv.Perm (Fin n) => y ∘ σ)) := by
    simp only [target, hds_hull]
    rw [L.image_convexHull]
    congr 1
    ext v
    constructor
    · rintro ⟨M, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, (Matrix.permMatrix_mulVec σ).symm⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨Equiv.Perm.permMatrix ℝ σ, ⟨σ, rfl⟩, Matrix.permMatrix_mulVec σ⟩
  have htarget_closed : IsClosed target := by
    rw [htarget_hull]; exact Set.Finite.isClosed_convexHull ℝ (Set.finite_range _)
  have htarget_convex : Convex ℝ target := by
    rw [htarget_hull]; exact convex_convexHull ℝ _
  have h_perm_mem : ∀ σ : Equiv.Perm (Fin n), y ∘ σ ∈ target := fun σ =>
    ⟨Equiv.Perm.permMatrix ℝ σ, permMatrix_mem_doublyStochastic, Matrix.permMatrix_mulVec σ⟩
  by_contra hnot
  push Not at hnot
  have hx_notin : x ∉ target := by
    rintro ⟨D, hD, hDy⟩
    exact hnot D hD hDy
  obtain ⟨f, u, hfx, hfb⟩ :=
    geometric_hahn_banach_point_closed htarget_convex htarget_closed hx_notin
  let c : Fin n → ℝ := fun i => f (Pi.single i 1)
  have hsingle_smul : ∀ (i : Fin n) (r : ℝ),
      Pi.single i r = r • (Pi.single i 1 : Fin n → ℝ) := by
    intro i r
    ext j
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases h : j = i
    · subst h; simp [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, mul_zero]
  have hf_rep : ∀ v : Fin n → ℝ, f v = ∑ i, c i * v i := by
    intro v
    have hv : v = ∑ i, Pi.single i (v i) := (Finset.univ_sum_single v).symm
    calc f v
        = f (∑ i, Pi.single i (v i)) := by rw [← hv]
      _ = ∑ i, f (Pi.single i (v i)) := map_sum f _ _
      _ = ∑ i, v i * f (Pi.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hsingle_smul i (v i), f.map_smul, smul_eq_mul]
      _ = ∑ i, c i * v i := by
          refine Finset.sum_congr rfl fun i _ => ?_; simp [c, mul_comm]
  have h_sep : ∀ σ : Equiv.Perm (Fin n), (∑ i, c i * x i) < ∑ i, c i * (y ∘ σ) i := by
    intro σ
    have h1 : f x < f (y ∘ σ) := lt_trans hfx (hfb _ (h_perm_mem σ))
    rwa [hf_rep, hf_rep] at h1
  let σ_c : Equiv.Perm (Fin n) := Tuple.sort c
  let σ_y : Equiv.Perm (Fin n) := Tuple.sort y
  let τ_y : Equiv.Perm (Fin n) := σ_y * Fin.revPerm * σ_c⁻¹
  have hc_mono : Monotone (c ∘ σ_c) := Tuple.monotone_sort c
  have hy_mono : Monotone (y ∘ σ_y) := Tuple.monotone_sort y
  have hrev_anti : Antitone (Fin.revPerm : Fin n → Fin n) :=
    fun i j hij => (Fin.rev_le_rev.mpr hij)
  -- For any `v` sorted by `σ_v`, the rearrangement `v ∘ τ_v` (with `τ_v = σ_v ∘ rev ∘ σ_c⁻¹`)
  -- antivaries with `c` and pulls back along `σ_c` to `(v ∘ σ_v) ∘ rev`.
  have antivary_rearrange : ∀ (v : Fin n → ℝ) (σ_v : Equiv.Perm (Fin n)),
      Monotone (v ∘ σ_v) →
      Antivary c (v ∘ (σ_v * Fin.revPerm * σ_c⁻¹ : Equiv.Perm (Fin n))) ∧
      ((v ∘ (σ_v * Fin.revPerm * σ_c⁻¹ : Equiv.Perm (Fin n))) ∘ σ_c =
        (v ∘ σ_v) ∘ (Fin.revPerm : Fin n → Fin n)) := by
    intro v σ_v hv_mono
    set τ_v : Equiv.Perm (Fin n) := σ_v * Fin.revPerm * σ_c⁻¹ with hτ_v
    have h_pullback : (v ∘ τ_v) ∘ σ_c = (v ∘ σ_v) ∘ (Fin.revPerm : Fin n → Fin n) := by
      funext i
      change v ((σ_v * Fin.revPerm * σ_c⁻¹ : Equiv.Perm (Fin n)) (σ_c i)) =
        v (σ_v (Fin.revPerm i))
      simp [Equiv.Perm.mul_apply]
    refine ⟨?_, h_pullback⟩
    have hτc_anti : Antitone ((v ∘ τ_v) ∘ σ_c) :=
      h_pullback ▸ hv_mono.comp_antitone hrev_anti
    have hAnti_lifted :
        Antivary (((v ∘ τ_v) ∘ σ_c) ∘ (σ_c⁻¹ : Equiv.Perm (Fin n)))
                 ((c ∘ σ_c) ∘ (σ_c⁻¹ : Equiv.Perm (Fin n))) :=
      (hτc_anti.antivary hc_mono).comp_right _
    have h1 : ((v ∘ τ_v) ∘ σ_c) ∘ (σ_c⁻¹ : Equiv.Perm (Fin n)) = v ∘ τ_v := by
      funext i; simp [Function.comp_apply]
    have h2 : (c ∘ σ_c) ∘ (σ_c⁻¹ : Equiv.Perm (Fin n)) = c := by
      funext i; simp [Function.comp_apply]
    rw [h1, h2] at hAnti_lifted
    exact hAnti_lifted.symm
  obtain ⟨h_cy_antivary, hyτcy_simp⟩ := antivary_rearrange y σ_y hy_mono
  have h_sep_τy := h_sep τ_y
  let σ_x : Equiv.Perm (Fin n) := Tuple.sort x
  let τ_x : Equiv.Perm (Fin n) := σ_x * Fin.revPerm * σ_c⁻¹
  have hx_mono : Monotone (x ∘ σ_x) := Tuple.monotone_sort x
  obtain ⟨h_cx_antivary, hxτcx_simp⟩ := antivary_rearrange x σ_x hx_mono
  have h_cx_min : (∑ i, c i * (x ∘ τ_x) i) ≤ ∑ i, c i * x i := by
    have hstep := h_cx_antivary.sum_mul_le_sum_mul_comp_perm (σ := τ_x⁻¹)
    have hptwise : ∀ i, (x ∘ τ_x) (τ_x⁻¹ i) = x i := fun i => by
      change x (τ_x (τ_x⁻¹ i)) = x i
      rw [show τ_x (τ_x⁻¹ i) = i from by simp]
    calc (∑ i, c i * (x ∘ τ_x) i)
        ≤ ∑ i, c i * (x ∘ τ_x) (τ_x⁻¹ i) := hstep
      _ = ∑ i, c i * x i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hptwise i]
  have h_sorted_strict : (∑ i, c i * (x ∘ τ_x) i) < ∑ i, c i * (y ∘ τ_y) i := by
    calc (∑ i, c i * (x ∘ τ_x) i) ≤ ∑ i, c i * x i := h_cx_min
      _ < ∑ i, c i * (y ∘ τ_y) i := h_sep_τy
  have hreindex : ∀ (c' v' : Fin n → ℝ) (σ : Equiv.Perm (Fin n)),
      ∑ i, c' i * v' i = ∑ j, c' (σ j) * v' (σ j) := fun c' v' σ =>
    (Equiv.sum_comp σ (fun j => c' j * v' j)).symm
  have hsum_x_reindex :
      (∑ i, c i * (x ∘ τ_x) i) = ∑ j, (c ∘ σ_c) j * ((x ∘ τ_x) ∘ σ_c) j :=
    hreindex c (x ∘ τ_x) σ_c
  have hsum_y_reindex :
      (∑ i, c i * (y ∘ τ_y) i) = ∑ j, (c ∘ σ_c) j * ((y ∘ τ_y) ∘ σ_c) j :=
    hreindex c (y ∘ τ_y) σ_c
  rw [hxτcx_simp] at hsum_x_reindex
  rw [hyτcy_simp] at hsum_y_reindex
  set d : Fin n → ℝ := c ∘ σ_c with hd_def
  set x' : Fin n → ℝ := fun j => (x ∘ σ_x) (Fin.revPerm j) with hx'_def
  set y' : Fin n → ℝ := fun j => (y ∘ σ_y) (Fin.revPerm j) with hy'_def
  have hd_mono : Monotone d := hc_mono
  have hsum_x' : ∑ j, x' j = ∑ i, x i := by
    calc ∑ j, x' j = ∑ j, (x ∘ σ_x) (Fin.revPerm j) := rfl
      _ = ∑ j, (x ∘ σ_x) j := Equiv.sum_comp Fin.revPerm (x ∘ σ_x)
      _ = ∑ i, x i := Equiv.sum_comp σ_x x
  have hsum_y' : ∑ j, y' j = ∑ i, y i := by
    calc ∑ j, y' j = ∑ j, (y ∘ σ_y) (Fin.revPerm j) := rfl
      _ = ∑ j, (y ∘ σ_y) j := Equiv.sum_comp Fin.revPerm (y ∘ σ_y)
      _ = ∑ i, y i := Equiv.sum_comp σ_y y
  have hfact : (∑ j, d j * x' j) < ∑ j, d j * y' j := by
    rwa [hsum_x_reindex, hsum_y_reindex] at h_sorted_strict
  have h_sum_x'_eq : (∑ i, x' i) = ∑ i, y' i := by
    rw [hsum_x', hsum_y', hsum]
  have h_abel_pull :
      ∃ k : Fin n, k.val + 1 < n ∧
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k.val), y' i) <
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k.val), x' i) :=
    abel_pull_partial_sum d x' y' hd_mono h_sum_x'_eq hfact
  obtain ⟨k, hk_lt, hPk⟩ := h_abel_pull
  let k' : ℕ := k.val + 1
  have hk'_le : k' ≤ n := by omega
  let S_x' : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val ≤ k.val)
  have hS_x'_card : S_x'.card = k' := by
    change (Finset.univ.filter (fun i : Fin n => i.val ≤ k.val)).card = k.val + 1
    have heq : (Finset.univ.filter (fun i : Fin n => i.val ≤ k.val)) = Finset.Iic k := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
      exact Iff.rfl
    rw [heq, Fin.card_Iic]
  let S_x : Finset (Fin n) := S_x'.image (fun i => σ_x (Fin.revPerm i))
  have hS_x_card : S_x.card = k' := by
    change (S_x'.image (fun i => σ_x (Fin.revPerm i))).card = k'
    calc (S_x'.image (fun i => σ_x (Fin.revPerm i))).card = S_x'.card :=
        Finset.card_image_of_injective _
          (fun a b hab => Fin.revPerm.injective (σ_x.injective hab))
      _ = k' := hS_x'_card
  have hS_x_sum : (∑ i ∈ S_x, x i) = ∑ i ∈ S_x', x' i := by
    change ∑ i ∈ S_x'.image (fun i => σ_x (Fin.revPerm i)), x i = ∑ i ∈ S_x', x' i
    rw [Finset.sum_image]
    · rfl
    · intros a _ b _ hab
      exact Fin.revPerm.injective (σ_x.injective hab)
  let S_y : Finset (Fin n) := S_x'.image (fun i => σ_y (Fin.revPerm i))
  have hS_y_card : S_y.card = k' := by
    change (S_x'.image (fun i => σ_y (Fin.revPerm i))).card = k'
    calc (S_x'.image (fun i => σ_y (Fin.revPerm i))).card = S_x'.card :=
        Finset.card_image_of_injective _
          (fun a b hab => Fin.revPerm.injective (σ_y.injective hab))
      _ = k' := hS_x'_card
  have hS_y_sum : (∑ i ∈ S_y, y i) = ∑ i ∈ S_x', y' i := by
    change ∑ i ∈ S_x'.image (fun i => σ_y (Fin.revPerm i)), y i = ∑ i ∈ S_x', y' i
    rw [Finset.sum_image]
    · rfl
    · intros a _ b _ hab
      exact Fin.revPerm.injective (σ_y.injective hab)
  have hm_lt : n - 1 - k.val < n := by omega
  let q : Fin n := ⟨n - 1 - k.val, hm_lt⟩
  let s : ℝ := y (σ_y q)
  have hq_val : q.val = n - 1 - k.val := rfl
  have hS_y_mem : ∀ i : Fin n, i ∈ S_y ↔ q.val ≤ (σ_y.symm i).val := by
    intro i
    change i ∈ S_x'.image (fun j => σ_y (Fin.revPerm j)) ↔ q.val ≤ (σ_y.symm i).val
    rw [Finset.mem_image]
    constructor
    · rintro ⟨j, hj_in, hj_eq⟩
      simp only [S_x', Finset.mem_filter, Finset.mem_univ, true_and] at hj_in
      have hinv : σ_y.symm i = Fin.revPerm j := by
        rw [← hj_eq]
        exact Equiv.symm_apply_apply σ_y (Fin.revPerm j)
      rw [hinv]
      change n - 1 - k.val ≤ (Fin.revPerm j).val
      have hrev_val : (Fin.revPerm j).val = n - (j.val + 1) := Fin.val_rev j
      omega
    · intro h
      refine ⟨Fin.revPerm (σ_y.symm i), ?_, ?_⟩
      · show Fin.revPerm (σ_y.symm i) ∈ S_x'
        simp only [S_x', Finset.mem_filter, Finset.mem_univ, true_and]
        have hrev : (Fin.revPerm (σ_y.symm i)).val = n - ((σ_y.symm i).val + 1) :=
          Fin.val_rev (σ_y.symm i)
        omega
      · show σ_y (Fin.revPerm (Fin.revPerm (σ_y.symm i))) = i
        rw [show Fin.revPerm (Fin.revPerm (σ_y.symm i)) = σ_y.symm i from by
          ext; simp [Fin.revPerm_apply, Fin.rev_rev]]
        exact Equiv.apply_symm_apply σ_y i
  have hS_y_lo : ∀ i ∈ S_y, s ≤ y i := by
    intro i hi
    have hi' : q.val ≤ (σ_y.symm i).val := (hS_y_mem i).mp hi
    have hle : q ≤ σ_y.symm i := hi'
    have : y (σ_y q) ≤ y (σ_y (σ_y.symm i)) := hy_mono hle
    rwa [Equiv.apply_symm_apply] at this
  have hS_y_hi : ∀ i, i ∉ S_y → y i ≤ s := by
    intro i hi
    have hi' : ¬ q.val ≤ (σ_y.symm i).val := fun h => hi ((hS_y_mem i).mpr h)
    have hle : σ_y.symm i ≤ q := by
      change (σ_y.symm i).val ≤ q.val
      omega
    have : y (σ_y (σ_y.symm i)) ≤ y (σ_y q) := hy_mono hle
    rwa [Equiv.apply_symm_apply] at this
  have hx_bound : (∑ i ∈ S_x, x i) ≤ (k' : ℝ) * s + ∑ i, max (x i - s) 0 :=
    subset_sum_le_scale_plus_hinge x S_x hS_x_card s
  have hhyp : (∑ i, max (x i - s) 0) ≤ ∑ j, max (y j - s) 0 :=
    hxy _ (convexOn_hinge_right s)
  have h_out_zero : ∀ i ∉ S_y, max (y i - s) 0 = 0 := fun i hi =>
    max_eq_right (sub_nonpos.mpr (hS_y_hi i hi))
  have h_in_eq : ∀ i ∈ S_y, max (y i - s) 0 = y i - s := fun i hi =>
    max_eq_left (sub_nonneg.mpr (hS_y_lo i hi))
  have h_sum_split : (∑ j, max (y j - s) 0) = ∑ i ∈ S_y, (y i - s) := by
    rw [← Finset.sum_compl_add_sum S_y (fun i => max (y i - s) 0)]
    have h_compl_zero : (∑ i ∈ S_yᶜ, max (y i - s) 0) = 0 :=
      Finset.sum_eq_zero (fun i hi => h_out_zero i (Finset.mem_compl.mp hi))
    rw [h_compl_zero, zero_add]
    exact Finset.sum_congr rfl (fun i hi => h_in_eq i hi)
  have h_y_S_eq : (∑ i ∈ S_y, y i) = (k' : ℝ) * s + ∑ j, max (y j - s) 0 := by
    rw [h_sum_split, Finset.sum_sub_distrib, Finset.sum_const, hS_y_card, nsmul_eq_mul]
    ring
  have hSx_le_Sy : (∑ i ∈ S_x, x i) ≤ ∑ i ∈ S_y, y i := by linarith
  rw [hS_x_sum.symm, hS_y_sum.symm] at hPk
  linarith

/-- Converse to the **Hardy–Littlewood–Pólya theorem**: If `x, y : Fin n → ℝ` are both monotone
non-decreasing with equal sum and the partial sums of `y` are everywhere dominated by those of `x`
(`y` is lower in the majorization order), then `∑ φ(x) ≤ ∑ φ(y)` for every convex `φ : ℝ → ℝ`. -/
theorem sum_convex_le_of_partial_sum_ge
    {n : ℕ} (x y : Fin n → ℝ) (hx : Monotone x) (hy : Monotone y)
    (hsum : ∑ i, x i = ∑ i, y i)
    (hpart : ∀ K : Fin n,
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), y i) ≤
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ K.val), x i))
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    ∑ i, φ (x i) ≤ ∑ i, φ (y i) := by
  classical
  -- Handle n = 0 trivially.
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · subst hn0; simp
  -- The right-derivative slope c k = derivWithin φ (Set.Ioi (x k)) (x k).
  set c : Fin n → ℝ := fun k => derivWithin φ (Set.Ioi (x k)) (x k) with hc_def
  -- c is monotone since φ is convex on ℝ and x is monotone.
  have hc_mono : Monotone c := by
    intro i j hij
    have hmono := hφ.monotoneOn_rightDeriv
      (a := x i) (b := x j)
      (by rw [interior_univ]; exact Set.mem_univ _)
      (by rw [interior_univ]; exact Set.mem_univ _)
      (hx hij)
    exact hmono
  -- Tangent-line inequality: φ(x k) - φ(y k) ≤ c k * (x k - y k).
  have htangent : ∀ k : Fin n, φ (x k) - φ (y k) ≤ c k * (x k - y k) := by
    intro k
    rcases lt_trichotomy (x k) (y k) with hlt | heq | hgt
    · -- Case x k < y k: use rightDeriv_le_slope.
      have h_slope :
          derivWithin φ (Set.Ioi (x k)) (x k) ≤ slope φ (x k) (y k) :=
        hφ.rightDeriv_le_slope_of_mem_interior
          (by rw [interior_univ]; exact Set.mem_univ _)
          (Set.mem_univ _) hlt
      have hpos : 0 < y k - x k := by linarith
      have hslope_eq : slope φ (x k) (y k) = (φ (y k) - φ (x k)) / (y k - x k) :=
        slope_def_field φ (x k) (y k)
      rw [hslope_eq] at h_slope
      have h_mul :
          c k * (y k - x k) ≤ (φ (y k) - φ (x k)) / (y k - x k) * (y k - x k) := by
        exact mul_le_mul_of_nonneg_right h_slope (le_of_lt hpos)
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h_mul
      nlinarith [h_mul]
    · -- Case x k = y k: both sides are 0.
      rw [heq]; ring_nf; linarith
    · -- Case x k > y k: use slope_le_leftDeriv and leftDeriv_le_rightDeriv.
      have h_slope :
          slope φ (y k) (x k) ≤ derivWithin φ (Set.Iio (x k)) (x k) :=
        hφ.slope_le_leftDeriv_of_mem_interior
          (Set.mem_univ _)
          (by rw [interior_univ]; exact Set.mem_univ _) hgt
      have h_left_right :
          derivWithin φ (Set.Iio (x k)) (x k) ≤ derivWithin φ (Set.Ioi (x k)) (x k) :=
        hφ.leftDeriv_le_rightDeriv_of_mem_interior
          (by rw [interior_univ]; exact Set.mem_univ _)
      have h_combined : slope φ (y k) (x k) ≤ c k := le_trans h_slope h_left_right
      have hpos : 0 < x k - y k := by linarith
      have hslope_eq : slope φ (y k) (x k) = (φ (x k) - φ (y k)) / (x k - y k) :=
        slope_def_field φ (y k) (x k)
      rw [hslope_eq] at h_combined
      have h_mul :
          (φ (x k) - φ (y k)) / (x k - y k) * (x k - y k) ≤ c k * (x k - y k) :=
        mul_le_mul_of_nonneg_right h_combined (le_of_lt hpos)
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h_mul
      exact h_mul
  -- Sum the tangent-line inequality: ∑ [φ(x k) - φ(y k)] ≤ ∑ c k * (x k - y k).
  have h_sum_tangent :
      (∑ k, (φ (x k) - φ (y k))) ≤ ∑ k, c k * (x k - y k) :=
    Finset.sum_le_sum (fun k _ => htangent k)
  -- Now perform Abel summation on ∑ c k * (x k - y k) to show it is ≤ 0.
  -- Transport c, x, y to ℕ-indexed functions.
  set C : ℕ → ℝ := fun i => if h : i < n then c ⟨i, h⟩ else 0 with hC_def
  set X : ℕ → ℝ := fun i => if h : i < n then x ⟨i, h⟩ else 0 with hX_def
  set Y : ℕ → ℝ := fun i => if h : i < n then y ⟨i, h⟩ else 0 with hY_def
  have eqC : ∀ i : Fin n, c i = C i.val := fun i => by simp [hC_def, i.isLt]
  have eqX : ∀ i : Fin n, x i = X i.val := fun i => by simp [hX_def, i.isLt]
  have eqY : ∀ i : Fin n, y i = Y i.val := fun i => by simp [hY_def, i.isLt]
  -- Prefix-sum filter-to-range translation (copied from abel_pull_partial_sum).
  have hfilter_range : ∀ k : ℕ, k < n →
      ∀ (v : Fin n → ℝ) (V : ℕ → ℝ), (∀ i : Fin n, v i = V i.val) →
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ k), v i) =
          ∑ i ∈ Finset.range (k + 1), V i := by
    intro k hk v V hv
    rw [Finset.sum_filter]
    rw [show (∑ i : Fin n, if i.val ≤ k then v i else 0) =
        ∑ i : Fin n, if i.val ≤ k then V i.val else 0 from Finset.sum_congr rfl
          (fun i _ => by
            split_ifs with h
            · exact hv i
            · rfl)]
    rw [show (∑ i : Fin n, if i.val ≤ k then V i.val else 0) =
        ∑ i ∈ Finset.range n, if i ≤ k then V i else 0 from
          Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≤ k then V j else 0) n]
    have hsubset : Finset.range (k + 1) ⊆ Finset.range n := by
      intro i hi
      rw [Finset.mem_range] at hi ⊢; omega
    rw [← Finset.sum_subset hsubset (fun i hi hi' => by
      rw [Finset.mem_range] at hi'
      have : ¬ (i ≤ k) := by omega
      rw [if_neg this])]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [if_pos (by omega)]
  -- Rewrite ∑ c k * (x k - y k) in terms of range sums.
  have hsum_CXY :
      (∑ k, c k * (x k - y k)) =
        (∑ i ∈ Finset.range n, C i * X i) - ∑ i ∈ Finset.range n, C i * Y i := by
    have h1 : (∑ k, c k * x k) = ∑ i ∈ Finset.range n, C i * X i := by
      calc (∑ k, c k * x k) = ∑ k : Fin n, C k.val * X k.val := by
            refine Finset.sum_congr rfl fun k _ => ?_; rw [eqC k, eqX k]
        _ = ∑ i ∈ Finset.range n, C i * X i :=
            Fin.sum_univ_eq_sum_range (fun i => C i * X i) n
    have h2 : (∑ k, c k * y k) = ∑ i ∈ Finset.range n, C i * Y i := by
      calc (∑ k, c k * y k) = ∑ k : Fin n, C k.val * Y k.val := by
            refine Finset.sum_congr rfl fun k _ => ?_; rw [eqC k, eqY k]
        _ = ∑ i ∈ Finset.range n, C i * Y i :=
            Fin.sum_univ_eq_sum_range (fun i => C i * Y i) n
    calc (∑ k, c k * (x k - y k))
        = ∑ k, (c k * x k - c k * y k) := by
          refine Finset.sum_congr rfl fun k _ => ?_; ring
      _ = (∑ k, c k * x k) - ∑ k, c k * y k := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ i ∈ Finset.range n, C i * X i) - ∑ i ∈ Finset.range n, C i * Y i := by
          rw [h1, h2]
  -- C is monotone in the relevant range.
  have hC_mono : ∀ i, i + 1 < n → C i ≤ C (i + 1) := fun i hi => by
    have h1 : i < n := by omega
    have h2 : i + 1 < n := hi
    have : c ⟨i, h1⟩ ≤ c ⟨i + 1, h2⟩ := hc_mono (by change i ≤ i + 1; omega)
    simp only [hC_def, dif_pos h1, dif_pos h2]
    exact this
  -- Equal sums in ℕ form.
  have hsum_XY : (∑ i ∈ Finset.range n, X i) = ∑ i ∈ Finset.range n, Y i := by
    have hX_sum : (∑ i, x i) = ∑ i ∈ Finset.range n, X i := by
      calc (∑ i, x i) = ∑ i : Fin n, X i.val :=
            Finset.sum_congr rfl fun i _ => eqX i
        _ = ∑ i ∈ Finset.range n, X i := Fin.sum_univ_eq_sum_range X n
    have hY_sum : (∑ i, y i) = ∑ i ∈ Finset.range n, Y i := by
      calc (∑ i, y i) = ∑ i : Fin n, Y i.val :=
            Finset.sum_congr rfl fun i _ => eqY i
        _ = ∑ i ∈ Finset.range n, Y i := Fin.sum_univ_eq_sum_range Y n
    rw [← hX_sum, ← hY_sum]; exact hsum
  have hrange_eq_ico : Finset.range n = Finset.Ico 0 n := by
    rw [Finset.range_eq_Ico]
  -- Abel summation.
  have habel : ∀ (V : ℕ → ℝ),
      (∑ i ∈ Finset.range n, C i * V i) =
        C (n - 1) * (∑ i ∈ Finset.range n, V i) -
        ∑ i ∈ Finset.Ico 0 (n - 1), (C (i + 1) - C i) * ∑ j ∈ Finset.range (i + 1), V j := by
    intro V
    have hby_parts := Finset.sum_Ico_by_parts (R := ℝ) (M := ℝ) C V hn_pos
    simp only [smul_eq_mul, Finset.sum_range_zero, mul_zero, sub_zero] at hby_parts
    rw [show (Finset.range n : Finset ℕ) = Finset.Ico 0 n from hrange_eq_ico] at *
    exact hby_parts
  have habelX := habel X
  have habelY := habel Y
  -- Prefix-sum inequality for X vs Y.
  have hpartial_ge : ∀ m, m < n →
      (∑ j ∈ Finset.range (m + 1), Y j) ≤ ∑ j ∈ Finset.range (m + 1), X j := by
    intro m hm
    have h1 := hpart ⟨m, hm⟩
    have hlhs := hfilter_range m hm y Y eqY
    have hrhs := hfilter_range m hm x X eqX
    rw [hlhs, hrhs] at h1
    exact h1
  -- Compute: ∑ C * X - ∑ C * Y = - ∑ (C(i+1) - C i) * (∑X - ∑Y).
  have hdiff :
      (∑ i ∈ Finset.range n, C i * X i) - (∑ i ∈ Finset.range n, C i * Y i) =
      - ∑ i ∈ Finset.Ico 0 (n - 1),
          (C (i + 1) - C i) * (∑ j ∈ Finset.range (i + 1), X j -
            ∑ j ∈ Finset.range (i + 1), Y j) := by
    rw [habelX, habelY, hsum_XY]
    set SX : ℝ := ∑ i ∈ Finset.Ico 0 (n - 1),
        (C (i + 1) - C i) * ∑ j ∈ Finset.range (i + 1), X j
    set SY : ℝ := ∑ i ∈ Finset.Ico 0 (n - 1),
        (C (i + 1) - C i) * ∑ j ∈ Finset.range (i + 1), Y j
    have h_SX_SY :
        (∑ i ∈ Finset.Ico 0 (n - 1),
          (C (i + 1) - C i) * (∑ j ∈ Finset.range (i + 1), X j -
            ∑ j ∈ Finset.range (i + 1), Y j)) = SX - SY := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    linarith [h_SX_SY]
  -- Each Abel term is ≥ 0: (C(i+1) - C i) * (∑X - ∑Y) ≥ 0.
  have hterm_nonneg : ∀ i ∈ Finset.Ico 0 (n - 1),
      0 ≤ (C (i + 1) - C i) * (∑ j ∈ Finset.range (i + 1), X j -
        ∑ j ∈ Finset.range (i + 1), Y j) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi_lt : i + 1 < n := by omega
    have hi_fin : i < n := by omega
    have hfactor_nonneg : 0 ≤ C (i + 1) - C i := by
      have := hC_mono i hi_lt; linarith
    have hpartial :
        (∑ j ∈ Finset.range (i + 1), Y j) ≤ ∑ j ∈ Finset.range (i + 1), X j :=
      hpartial_ge i hi_fin
    have hdiff_nn :
        0 ≤ (∑ j ∈ Finset.range (i + 1), X j) - (∑ j ∈ Finset.range (i + 1), Y j) := by
      linarith
    exact mul_nonneg hfactor_nonneg hdiff_nn
  have hsum_nonneg :
      0 ≤ ∑ i ∈ Finset.Ico 0 (n - 1),
          (C (i + 1) - C i) * (∑ j ∈ Finset.range (i + 1), X j -
            ∑ j ∈ Finset.range (i + 1), Y j) :=
    Finset.sum_nonneg hterm_nonneg
  -- So ∑ C * X - ∑ C * Y ≤ 0, i.e., ∑ c k * (x k - y k) ≤ 0.
  have hCXY_nonpos :
      (∑ i ∈ Finset.range n, C i * X i) - ∑ i ∈ Finset.range n, C i * Y i ≤ 0 := by
    rw [hdiff]; linarith
  have htangent_sum_nonpos : (∑ k, c k * (x k - y k)) ≤ 0 := by
    rw [hsum_CXY]; exact hCXY_nonpos
  -- Putting it all together: ∑ [φ(x k) - φ(y k)] ≤ ∑ c k * (x k - y k) ≤ 0.
  have h_final : (∑ k, (φ (x k) - φ (y k))) ≤ 0 :=
    le_trans h_sum_tangent htangent_sum_nonpos
  rw [Finset.sum_sub_distrib] at h_final
  linarith
end
