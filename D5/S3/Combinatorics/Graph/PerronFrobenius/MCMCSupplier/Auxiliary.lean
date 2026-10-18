/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected MCMC finite Perron proof supporting actual weighted graphs. -/
/- Transplanted from or4nge19/MCMC@b901242fd04b6eff425a177e5c9bc6c56257bc62.
Copyright and attribution notices below retained; full license: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LICENSE.
Changes: module imports relocated; comment formatting, placement and blank lines adapted for the canonical weighted-graph consumer.
Matteo Cipollina. Changes: unused declarations and branches removed; retained live proof steps preserved; unused local proof terms removed. -/
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.Spectrum
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Int.Star
open Filter Set Finset Matrix Topology Convex
theorem eventually_to_open {α : Type*} [TopologicalSpace α] {p : α → Prop} {a : α}
    (h : ∀ᶠ x in 𝓝 a, p x) :
    ∃ (U : Set α), IsOpen U ∧ a ∈ U ∧ ∀ x ∈ U, p x := by
  rcases mem_nhds_iff.mp h with ⟨U, hU_open, haU, hU⟩
  simp_all only
  apply Exists.intro
  · apply And.intro
    on_goal 2 => apply And.intro
    on_goal 2 => {exact hU
    }
    · simp_all only
    · intro x a_1
      apply hU_open
      simp_all only
theorem continuousOn_finset_inf' {α β : Type*} [TopologicalSpace α] [LinearOrder β]
    [TopologicalSpace β] [OrderTopology β] {ι : Type*} [Fintype ι]
    {s : Finset ι} {U : Set α} (hs : s.Nonempty) {f : ι → α → β}
    (hf : ∀ i ∈ s, ContinuousOn (f i) U) :
    ContinuousOn (fun x => s.inf' hs (fun i => f i x)) U :=
  ContinuousOn.finset_inf'_apply hs hf
theorem finset_inf'_mono_subset {α β : Type*} [LinearOrder β] {s t : Finset α} (h : s ⊆ t)
    {f : α → β} {hs : s.Nonempty} {ht : t.Nonempty} :
    t.inf' ht f ≤ s.inf' hs f := by
  exact inf'_mono f h hs
theorem mulVec_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx : ∀ i, 0 ≤ x i) : ∀ i, 0 ≤ (A *ᵥ x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)
theorem exists_pos_of_sum_one_of_nonneg {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
    (hsum : ∑ i, x i = 1) (hnonneg : ∀ i, 0 ≤ x i) : ∃ j, 0 < x j := by
  by_contra h
  push_neg at h
  have h_all_zero : ∀ i, x i = 0 := by
    intro i
    exact le_antisymm (h i) (hnonneg i)
  have h_sum_zero : ∑ i, x i = 0 := by
    simp only [h_all_zero, Finset.sum_const_zero]
  have : 1 = 0 := by linarith
  exact absurd this (by norm_num)
lemma Finset.inf'_eq_ciInf {α β} [ConditionallyCompleteLinearOrder β] {s : Finset α}
    (h : s.Nonempty) (f : α → β) :
    s.inf' h f = ⨅ i : s, f i := by
  have : Nonempty s := Finset.Nonempty.to_subtype h
  rw [Finset.inf'_eq_csInf_image]
  congr
  ext x
  simp [Set.mem_image, Set.mem_range]
variable {n : Type*}
lemma exists_pos_of_ne_zero [Fintype n] [DecidableEq n] {v : n → ℝ} (h_nonneg : ∀ i, 0 ≤ v i) (h_ne_zero : v ≠ 0) :
    ∃ i, 0 < v i := by
  by_contra h_all_nonpos
  apply h_ne_zero
  ext i
  exact le_antisymm (by simp_all) (h_nonneg i)
lemma exists_pos_maximal_of_nonneg_ne_zero [Fintype n] [Nonempty n] [DecidableEq n] {v : n → ℝ}
    (h_nonneg : ∀ i, 0 ≤ v i) (h_ne_zero : v ≠ 0) :
    ∃ i, 0 < v i ∧ ∀ j, v j ≤ v i := by
  obtain ⟨i, -, hi_max⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
  obtain ⟨j, hj_pos⟩ := exists_pos_of_ne_zero h_nonneg h_ne_zero
  refine ⟨i, ?_, ?_⟩
  · refine lt_of_lt_of_le hj_pos ?_
    rw [← hi_max]
    exact Finset.le_sup' v (Finset.mem_univ j)
  · intro j
    rw [← hi_max]
    exact Finset.le_sup' v (Finset.mem_univ j)
lemma Set.toFinset_nonempty_iff {α : Type*} [Fintype α] [DecidableEq α] (s : Set α) [Finite s] [Fintype s] :
    s.toFinset.Nonempty ↔ s.Nonempty := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Set.mem_toFinset.mp hx⟩
  · intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, Set.mem_toFinset.mpr hx⟩
lemma div_le_iff {a b c : ℝ} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  rw [@le_iff_le_iff_lt_iff_lt]
  exact lt_div_iff₀ hb
lemma Finset.inf'_pos {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {f : α → ℝ} (h_pos : ∀ a ∈ s, 0 < f a) :
    0 < s.inf' hs f := by
  obtain ⟨b, hb_mem, h_fb_is_inf⟩ := s.exists_mem_eq_inf' hs f
  have h_fb_pos : 0 < f b := h_pos b hb_mem
  rw [h_fb_is_inf]
  exact h_fb_pos
lemma ones_norm_mem_simplex [Fintype n] [Nonempty n] :
  (fun _ => (Fintype.card n : ℝ)⁻¹) ∈ stdSimplex ℝ n := by
  dsimp [stdSimplex]; constructor
  · intro i; apply inv_nonneg.2; norm_cast; exact Nat.cast_nonneg _
  · simp [Finset.sum_const, Finset.card_univ];
lemma ne_zero_of_mem_stdSimplex
    {n : Type*} [Fintype n] [Nonempty n] {x : n → ℝ}
    (hx : x ∈ stdSimplex ℝ n) :
    x ≠ 0 := by
  intro h_zero
  have h_sum_zero : (∑ i, x i) = 0 := by
    subst h_zero
    simp_all only [Pi.zero_apply, Finset.sum_const_zero]
  have h_sum_one : (∑ i, x i) = 1 := hx.2
  linarith
namespace Matrix
lemma diagonal_mulVec_ones [DecidableEq n][Fintype n] (d : n → ℝ) :
    diagonal d *ᵥ (fun _ => 1) = d := by
  ext i; simp [mulVec_diagonal]
lemma diagonal_inv_mulVec_self [DecidableEq n][Fintype n] {d : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    diagonal (d⁻¹) *ᵥ d = fun _ => 1 := by
  ext i
  simp [mulVec_diagonal]
  simp_all only [ne_eq, isUnit_iff_ne_zero, not_false_eq_true, IsUnit.inv_mul_cancel]
lemma diagonal_mulVec_diagonal_inv_mulVec [DecidableEq n] [Fintype n]
    {d x : n → ℝ} (hd : ∀ i, d i ≠ 0) :
    diagonal d *ᵥ (diagonal (d⁻¹) *ᵥ x) = x := by
  ext i
  simp [mulVec_diagonal, hd i]
lemma diagonal_mulVec_mono [DecidableEq n] [Fintype n] {d x y : n → ℝ}
    (hd_nonneg : ∀ i, 0 ≤ d i) (hxy : x ≤ y) :
    diagonal d *ᵥ x ≤ diagonal d *ᵥ y := by
  intro i
  rw [mulVec_diagonal, mulVec_diagonal]
  exact mul_le_mul_of_nonneg_left (hxy i) (hd_nonneg i)
end Matrix
variable {α ι : Type*} {f : ι → α} {s : Set ι}
open Set
