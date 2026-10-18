/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/CollatzWielandt
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/CollatzWielandt
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected MCMC finite Perron proof supporting actual weighted graphs. -/
/- Transplanted from or4nge19/MCMC@b901242fd04b6eff425a177e5c9bc6c56257bc62.
Copyright and attribution notices below retained; full license: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean.
Changes: module imports relocated; comment formatting, placement and blank lines adapted for the canonical weighted-graph consumer.
Matteo Cipollina. Changes: unused declarations and branches removed; retained live proof steps preserved; unused local proof terms removed. -/
/- Copyright (c) 2025 Matteo Cipollina. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE. Authors: Matteo Cipollina -/
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.Auxiliary
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Semicontinuity.Basic
namespace Matrix
section PerronFrobenius
variable {n : Type*} [Fintype n] [Nonempty n] {A : Matrix n n ℝ}
open LinearMap Set Filter Topology Finset Quiver Matrix IsCompact
open scoped Convex Pointwise
noncomputable def collatzWielandtFn (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  let supp := {i | 0 < x i}.toFinset
  if h : supp.Nonempty then
    supp.inf' h fun i => (A *ᵥ x) i / x i
  else 0
namespace CollatzWielandt
private lemma pos_support_toFinset_nonempty_of_mem_stdSimplex {x : n → ℝ}
    (hx : x ∈ stdSimplex ℝ n) :
    ({i | 0 < x i}.toFinset).Nonempty := by
  obtain ⟨i, hi_pos⟩ := exists_pos_of_sum_one_of_nonneg hx.2 hx.1
  exact ⟨i, by simpa using hi_pos⟩
omit [Nonempty n] in
lemma collatzWielandtFn_eq_inf' (A : Matrix n n ℝ) {x : n → ℝ}
    (hx : ({i | 0 < x i}.toFinset).Nonempty) :
    collatzWielandtFn A x =
      ({i | 0 < x i}.toFinset).inf' hx (fun i => (A *ᵥ x) i / x i) := by
  dsimp [collatzWielandtFn]
  rw [dif_pos hx]
omit [Nonempty n] in
private def posSupportNeighborhood (x : n → ℝ) : Set (n → ℝ) :=
  {y | ∀ i ∈ {i | 0 < x i}.toFinset, 0 < y i}
omit [Nonempty n] in
private lemma self_mem_posSupportNeighborhood (x : n → ℝ) :
    x ∈ posSupportNeighborhood x := by
  intro i hi
  simpa [Set.mem_toFinset] using hi
omit [Nonempty n] in
private lemma isOpen_posSupportNeighborhood (x : n → ℝ) :
    IsOpen (posSupportNeighborhood x) := by
  have h_eq : posSupportNeighborhood x = ⋂ i ∈ {i | 0 < x i}.toFinset, {y | 0 < y i} := by
    ext y
    simp [posSupportNeighborhood]
  rw [h_eq]
  apply isOpen_biInter_finset
  intro i _
  exact isOpen_lt continuous_const (continuous_apply i)
omit [Nonempty n] in
private lemma continuousOn_fixedSupportRatios (A : Matrix n n ℝ) {x : n → ℝ}
    (hx : ({i | 0 < x i}.toFinset).Nonempty) :
    ContinuousOn (fun y => {i | 0 < x i}.toFinset.inf' hx fun i => (A *ᵥ y) i / y i)
      (posSupportNeighborhood x) := by
  apply continuousOn_finset_inf' hx
  intro i hi
  apply ContinuousOn.div
  · exact continuous_apply i |>.comp_continuousOn
      ((Matrix.mulVecLin A).toContinuousLinearMap.continuous.continuousOn)
  · exact (continuous_apply i).continuousOn
  · intro y hy
    exact (hy i hi).ne'
private lemma collatzWielandtFn_le_fixedSupportRatios (A : Matrix n n ℝ)
    {x y : n → ℝ} (hx : ({i | 0 < x i}.toFinset).Nonempty)
    (hy : y ∈ posSupportNeighborhood x ∩ stdSimplex ℝ n) :
    collatzWielandtFn A y ≤
      {i | 0 < x i}.toFinset.inf' hx (fun i => (A *ᵥ y) i / y i) := by
  have hy_supp : {i | 0 < y i}.toFinset.Nonempty :=
    pos_support_toFinset_nonempty_of_mem_stdSimplex hy.2
  rw [collatzWielandtFn_eq_inf' A hy_supp]
  apply finset_inf'_mono_subset
  intro i hi
  have : 0 < y i := hy.1 i hi
  simpa [Set.mem_toFinset] using this
theorem upperSemicontinuousOn
    (A : Matrix n n ℝ) : UpperSemicontinuousOn (collatzWielandtFn A) (stdSimplex ℝ n) := by
  intro x₀ hx₀ c hc
  have supp_x₀ : {i | 0 < x₀ i}.toFinset.Nonempty :=
    pos_support_toFinset_nonempty_of_mem_stdSimplex hx₀
  have fn_eq :
      collatzWielandtFn A x₀ =
        {i | 0 < x₀ i}.toFinset.inf' supp_x₀ (fun i => (A *ᵥ x₀) i / x₀ i) :=
    collatzWielandtFn_eq_inf' A supp_x₀
  let f := fun y => {i | 0 < x₀ i}.toFinset.inf' supp_x₀ fun i => (A *ᵥ y) i / y i
  rw [fn_eq] at hc
  have cont_at : ContinuousAt f x₀ :=
    (continuousOn_fixedSupportRatios A supp_x₀).continuousAt
      ((isOpen_posSupportNeighborhood x₀).mem_nhds (self_mem_posSupportNeighborhood x₀))
  have lt_eventually : ∀ᶠ y in 𝓝 x₀, f y < c :=
    Filter.Tendsto.eventually_lt_const hc cont_at
  rcases eventually_to_open lt_eventually with ⟨V, V_open, x₀_in_V, hV⟩
  let W := V ∩ posSupportNeighborhood x₀ ∩ stdSimplex ℝ n
  have VU_open : IsOpen (V ∩ posSupportNeighborhood x₀) :=
    IsOpen.inter V_open (isOpen_posSupportNeighborhood x₀)
  have VU_mem : x₀ ∈ V ∩ posSupportNeighborhood x₀ :=
    ⟨x₀_in_V, self_mem_posSupportNeighborhood x₀⟩
  have VU_nhds : V ∩ posSupportNeighborhood x₀ ∈ 𝓝 x₀ := VU_open.mem_nhds VU_mem
  have W_nhdsWithin : W ∈ 𝓝[stdSimplex ℝ n] x₀ := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨V ∩ posSupportNeighborhood x₀, VU_nhds, by simp [W]⟩
  exact Filter.mem_of_superset W_nhdsWithin fun y hy => by
    show collatzWielandtFn A y < c
    apply lt_of_le_of_lt
    · exact collatzWielandtFn_le_fixedSupportRatios A supp_x₀ ⟨hy.1.2, hy.2⟩
    · exact hV y hy.1.1
def nonnegNeZero : Set (n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0}
omit [Fintype n] in
lemma nonnegNeZero_mem_const_one : (fun _ : n => (1 : ℝ)) ∈ nonnegNeZero := by
  refine ⟨fun _ => zero_le_one, ?_⟩
  intro h
  exact Nonempty.elim ‹Nonempty n› fun i => one_ne_zero (congr_fun h i)
theorem exists_maximizer (A : Matrix n n ℝ) :
    ∃ v ∈ stdSimplex ℝ n, IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v := by
  have h_compact : IsCompact (stdSimplex ℝ n) := by exact _root_.isCompact_stdSimplex ℝ n
  have h_nonempty : (stdSimplex ℝ n).Nonempty := stdSimplex_nonempty
  have h_usc : UpperSemicontinuousOn (collatzWielandtFn A) (stdSimplex ℝ n) :=
    upperSemicontinuousOn A
  exact UpperSemicontinuousOn.exists_isMaxOn h_nonempty h_compact h_usc
omit [Nonempty n] in
lemma eq_iInf_of_nonempty (v : n → ℝ) (h : {i | 0 < v i}.toFinset.Nonempty) :
    collatzWielandtFn A v =
      ⨅ i : {i | 0 < v i}, (A *ᵥ v) i / v i := by
  rw [collatzWielandtFn_eq_inf' A h, Finset.inf'_eq_ciInf h]
  exact Equiv.iInf_congr
    (Equiv.subtypeEquivRight fun i => Set.mem_toFinset (s := {i | 0 < v i})) fun _ => rfl
omit [Nonempty n] in
lemma le_ratio [DecidableEq n] {v : n → ℝ} (i : n) (hi_pos : 0 < v i) :
    collatzWielandtFn A v ≤ (A *ᵥ v) i / v i := by
  have h_support : {j | 0 < v j}.toFinset.Nonempty := ⟨i, by simpa using hi_pos⟩
  rw [collatzWielandtFn_eq_inf' A h_support]
  apply Finset.inf'_le
  simpa using hi_pos
omit [Nonempty n] in
lemma le_mulVec [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i)
    (_ : v ≠ 0) :
    (collatzWielandtFn A v) • v ≤ A *ᵥ v := by
  let r := collatzWielandtFn A v
  intro i
  by_cases hi_supp : v i > 0
  · have h_le_div : r ≤ (A *ᵥ v) i / v i :=
      le_ratio (A := A) i hi_supp
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (le_div_iff₀ hi_supp).mp h_le_div
  · have h_vi_zero : v i = 0 := by linarith [hv_nonneg i, not_lt.mp hi_supp]
    simp only [Pi.smul_apply, smul_eq_mul, h_vi_zero, mul_zero]
    exact mulVec_nonneg hA_nonneg hv_nonneg i
lemma bddAbove [DecidableEq n] (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    BddAbove (collatzWielandtFn A '' nonnegNeZero) := by
  use Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ∑ j, A i j)
  rintro y ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
  obtain ⟨m, h_xm_pos, h_xm_max⟩ := exists_pos_maximal_of_nonneg_ne_zero hx_nonneg hx_ne_zero
  have h_le_ratio : collatzWielandtFn A x ≤ (A *ᵥ x) m / x m :=
    le_ratio (A := A) m h_xm_pos
  have h_ratio_le : (A *ᵥ x) m / x m ≤ Finset.univ.sup' Finset.univ_nonempty (fun k ↦ ∑ l, A k l) := by
    rw [mulVec_apply, div_le_iff h_xm_pos]
    refine le_trans (sum_mul_le_sum_mul_const_of_forall_le (fun j => A m j) x m
      (fun j => hA_nonneg m j) h_xm_max) ?_
    apply mul_le_mul_of_nonneg_right _ (le_of_lt h_xm_pos)
    exact le_sup' (fun k => ∑ l, A k l) (Finset.mem_univ m)
  exact le_trans h_le_ratio h_ratio_le
lemma set_nonempty :
    (collatzWielandtFn A '' nonnegNeZero).Nonempty := by
  exact Set.Nonempty.image _ ⟨_, nonnegNeZero_mem_const_one⟩
omit [Nonempty n] in
lemma collatzWielandtFn_smul [DecidableEq n] {c : ℝ} (hc : 0 < c)
  {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne : x ≠ 0) :
  collatzWielandtFn A (c • x) = collatzWielandtFn A x := by
  dsimp [collatzWielandtFn]
  let S := {i | 0 < x i}.toFinset
  obtain ⟨i₀, hi₀⟩ := exists_pos_of_ne_zero hx_nonneg hx_ne
  have hS_nonempty : S.Nonempty := ⟨i₀, by simp [S, hi₀]⟩
  have h_supp_eq : {i | 0 < (c • x) i}.toFinset = S := by
    ext i
    simp [S, smul_eq_mul, mul_pos_iff_of_pos_left hc]
  rw [dif_pos (h_supp_eq.symm ▸ hS_nonempty), dif_pos hS_nonempty]
  refine inf'_congr (Eq.symm h_supp_eq ▸ hS_nonempty) h_supp_eq ?_
  intro i hi
  simp only [mulVec_smul, smul_eq_mul, Pi.smul_apply]
  rw [mul_div_mul_left _ _ (ne_of_gt hc)]
noncomputable def perronRoot (A : Matrix n n ℝ) : ℝ :=
  sSup (collatzWielandtFn A '' nonnegNeZero)
omit [Nonempty n] in
theorem eq_eigenvalue_of_positive_eigenvector [DecidableEq n] [Nonempty n]
    {r : ℝ} {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    collatzWielandtFn A v = r := by
  have h_supp_nonempty : ({i | 0 < v i}.toFinset).Nonempty := by
    obtain ⟨i, hi⟩ := Finset.univ_nonempty (α := n)
    exact ⟨i, by simpa using hv_pos i⟩
  rw [eq_iInf_of_nonempty v h_supp_nonempty]
  calc
    ⨅ i : {i | 0 < v i}, (A *ᵥ v) i / v i = ⨅ _ : {i | 0 < v i}, r := by
      refine iInf_congr ?_
      intro i
      have h_eig_i : (A *ᵥ v) i = r * v i := by
        simpa [Pi.smul_apply, smul_eq_mul] using congr_fun h_eig i
      rw [h_eig_i, mul_div_assoc, div_self i.2.ne']
      simp
    _ = r := by
      have h_support_nonempty : ({i | 0 < v i} : Set n).Nonempty := by
        rcases h_supp_nonempty with ⟨i, hi⟩
        exact ⟨i, by simpa [Set.mem_toFinset] using hi⟩
      letI : Nonempty {i | 0 < v i} := Set.Nonempty.to_subtype h_support_nonempty
      show (⨅ _ : {i | 0 < v i}, r) = r
      exact ciInf_const (ι := {i | 0 < v i}) (a := r)
theorem eigenvalue_le_perron_root_of_positive_eigenvector
    {r : ℝ} {v : n → ℝ} [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (_ : 0 < r)
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    r ≤ perronRoot A := by
  have hv_nonneg : ∀ i, 0 ≤ v i := fun i ↦ (hv_pos i).le
  have hv_ne_zero : v ≠ 0 := by
    exact Pi.ne_zero_of_pos hv_pos
  have h_r : r = collatzWielandtFn A v :=
    (eq_eigenvalue_of_positive_eigenvector hv_pos h_eig).symm
  have h_le : collatzWielandtFn A v ≤ perronRoot A := by
    dsimp [perronRoot]
    have h_bdd : BddAbove (collatzWielandtFn A '' nonnegNeZero) :=
      bddAbove A hA_nonneg
    apply le_csSup h_bdd
    have hv_in : v ∈ nonnegNeZero := ⟨hv_nonneg, hv_ne_zero⟩
    exact Set.mem_image_of_mem (collatzWielandtFn A) hv_in
  simpa [h_r] using h_le
omit [Nonempty n] in
lemma ones_eigenvector_of_similarity_transform [DecidableEq n]
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    (diagonal (v⁻¹) * A * diagonal v) *ᵥ (fun _ => 1) = fun _ => r := by
  let D := diagonal v
  let D_inv := diagonal (v⁻¹)
  let B := D_inv * A * D
  let ones := fun _ : n => (1 : ℝ)
  calc
    B *ᵥ ones
      = D_inv *ᵥ (A *ᵥ (D *ᵥ ones)) := by
          unfold B
          rw [← mulVec_mulVec, ← mulVec_mulVec]
    _ = D_inv *ᵥ (A *ᵥ v) := by
        have h_D_ones : D *ᵥ ones = v := by
          unfold D ones
          exact diagonal_mulVec_ones v
        rw [h_D_ones]
    _ = D_inv *ᵥ (r • v) := by rw [h_eig]
    _ = r • (D_inv *ᵥ v) := by rw [mulVec_smul]
    _ = r • ones := by
        have h_D_inv_v : D_inv *ᵥ v = ones := by
          unfold D_inv ones
          have hv_ne_zero : ∀ i, v i ≠ 0 := fun i => (hv_pos i).ne'
          exact diagonal_inv_mulVec_self hv_ne_zero
        rw [h_D_inv_v]
    _ = fun _ => r := by
        ext x
        simp only [Pi.smul_apply, smul_eq_mul, mul_one, ones]
omit [Nonempty n] in
lemma row_sum_of_similarity_transformed_matrix [DecidableEq n]
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    ∀ i, ∑ j, (Matrix.diagonal (v⁻¹) * A * Matrix.diagonal v) i j = r := by
  intro i
  let B := Matrix.diagonal (v⁻¹) * A * Matrix.diagonal v
  have row_sum_eq : ∑ j, B i j = (B *ᵥ (fun _ => 1)) i := by
    simp [mulVec_apply_eq_sum]
  rw [row_sum_eq]
  have h_B_eig := ones_eigenvector_of_similarity_transform hv_pos h_eig
  rw [h_B_eig]
lemma le_of_max_le_row_sum [DecidableEq n]
    {B : Matrix n n ℝ} {x : n → ℝ} {c r : ℝ}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (h_B_row_sum : ∀ i, ∑ j, B i j = r)
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) (h_le_Bx : c • x ≤ B *ᵥ x) :
    c ≤ r := by
  obtain ⟨k, h_xk_pos, h_xk_max⟩ := exists_pos_maximal_of_nonneg_ne_zero hx_nonneg hx_ne_zero
  have h_le_k := h_le_Bx k
  simp only [Pi.smul_apply, smul_eq_mul] at h_le_k
  have h_Bx_le : (B *ᵥ x) k ≤ r * x k := by
    rw [mulVec_apply]
    calc
      ∑ j, B k j * x j
          ≤ (∑ j, B k j) * x k :=
        sum_mul_le_sum_mul_const_of_forall_le (fun j => B k j) x k (fun j => hB_nonneg k j) h_xk_max
      _ = r * x k := by rw [h_B_row_sum k]
  exact le_of_mul_le_mul_right (le_trans h_le_k h_Bx_le) h_xk_pos
omit [Nonempty n] in
lemma nonneg_similarity_transform [DecidableEq n]
    {A : Matrix n n ℝ} {v : n → ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hv_pos : ∀ i, 0 < v i) :
    ∀ i j, 0 ≤ (Matrix.diagonal (v⁻¹) * A * Matrix.diagonal v) i j := by
  intro i j
  rw [mul_diagonal, diagonal_mul]
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (hv_pos i).le) (hA_nonneg i j)) (hv_pos j).le
theorem le_eigenvalue_of_right_eigenvector [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ} (_ : 0 < r)
    {v : n → ℝ} (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v)
    {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i) (hw_ne_zero : w ≠ 0) :
    collatzWielandtFn A w ≤ r := by
  let D := Matrix.diagonal v
  let D_inv := Matrix.diagonal (v⁻¹)
  let B := D_inv * A * D
  have hB_nonneg : ∀ i j, 0 ≤ B i j := by
    simpa [B, D, D_inv] using nonneg_similarity_transform hA_nonneg hv_pos
  have h_B_row_sum := row_sum_of_similarity_transformed_matrix hv_pos h_eig
  let x := D_inv *ᵥ w
  have h_w_eq_Dx : w = D *ᵥ x := by
    simpa [D, D_inv, x] using
      (diagonal_mulVec_diagonal_inv_mulVec (d := v) (x := w) fun i => (hv_pos i).ne').symm
  have hx_nonneg : ∀ i, 0 ≤ x i := by
    intro i
    unfold x D_inv
    rw [mulVec_diagonal]
    exact mul_nonneg (inv_nonneg.mpr (hv_pos i).le) (hw_nonneg i)
  have hx_ne_zero : x ≠ 0 := by
    contrapose! hw_ne_zero
    rw [h_w_eq_Dx, hw_ne_zero, mulVec_zero]
  have h_smul_le : (collatzWielandtFn A w) • w ≤ A *ᵥ w :=
    CollatzWielandt.le_mulVec hA_nonneg hw_nonneg hw_ne_zero
  have h_le_Bx : (collatzWielandtFn A w) • x ≤ B *ᵥ x := by
    calc
      (collatzWielandtFn A w) • x = D_inv *ᵥ ((collatzWielandtFn A w) • w) := by
        rw [← mulVec_smul, h_w_eq_Dx]
      _ ≤ D_inv *ᵥ (A *ᵥ w) := by
        simpa [D_inv] using
          diagonal_mulVec_mono (d := v⁻¹) (x := (collatzWielandtFn A w) • w) (y := A *ᵥ w)
            (fun i => inv_nonneg.mpr (hv_pos i).le) h_smul_le
      _ = D_inv *ᵥ (A *ᵥ (D *ᵥ x)) := by rw [h_w_eq_Dx]
      _ = (D_inv * A * D) *ᵥ x := by rw [← mulVec_mulVec, ← mulVec_mulVec]
      _ = B *ᵥ x := rfl
  exact le_of_max_le_row_sum hB_nonneg h_B_row_sum hx_nonneg hx_ne_zero h_le_Bx
theorem eigenvalue_is_ub_of_positive_eigenvector [DecidableEq n]
    (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ} (hr_pos : 0 < r)
    {v : n → ℝ} (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    perronRoot A ≤ r := by
  dsimp [perronRoot]
  apply csSup_le (CollatzWielandt.set_nonempty (A := A))
  rintro _ ⟨w, ⟨hw_nonneg, hw_ne_zero⟩, rfl⟩
  exact CollatzWielandt.le_eigenvalue_of_right_eigenvector
    hA_nonneg hr_pos hv_pos h_eig hw_nonneg hw_ne_zero
omit [Nonempty n] in
lemma sum_pos_of_nonneg_ne_zero [DecidableEq n] {x : n → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    0 < ∑ i, x i := by
  obtain ⟨i, hi⟩ := exists_pos_of_ne_zero hx_nonneg hx_ne_zero
  exact Finset.sum_pos' (fun j _ => hx_nonneg j) ⟨i, Finset.mem_univ _, hi⟩
omit [Nonempty n] in
lemma inv_sum_smul_mem_stdSimplex_of_nonneg_ne_zero [DecidableEq n] {x : n → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    (∑ i, x i)⁻¹ • x ∈ stdSimplex ℝ n := by
  have hs_pos := sum_pos_of_nonneg_ne_zero hx_nonneg hx_ne_zero
  constructor
  · intro i
    exact mul_nonneg (inv_nonneg.mpr hs_pos.le) (hx_nonneg i)
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs_pos.ne'
omit [Nonempty n] in
lemma collatzWielandtFn_inv_sum_smul_of_nonneg_ne_zero [DecidableEq n] {x : n → ℝ}
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    collatzWielandtFn A ((∑ i, x i)⁻¹ • x) = collatzWielandtFn A x :=
  collatzWielandtFn_smul (inv_pos.mpr (sum_pos_of_nonneg_ne_zero hx_nonneg hx_ne_zero))
    hx_nonneg hx_ne_zero
omit [Nonempty n] in
theorem le_of_subinvariant [DecidableEq n]
    {A : Matrix n n ℝ} (_ : ∀ i j, 0 ≤ A i j)
    {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i) (hw_ne_zero : w ≠ 0)
    {lambda : ℝ} (h_sub : lambda • w ≤ A *ᵥ w) :
    lambda ≤ collatzWielandtFn A w := by
  obtain ⟨i, hi⟩ := exists_pos_of_ne_zero hw_nonneg hw_ne_zero
  let S := {j | 0 < w j}.toFinset
  have hS_nonempty : S.Nonempty := ⟨i, by simp [S]; exact hi⟩
  rw [collatzWielandtFn, dif_pos hS_nonempty]
  apply Finset.le_inf'
  intro j hj
  have hw_j_pos : 0 < w j := by simpa [S] using hj
  exact (le_div_iff₀ hw_j_pos).mpr (h_sub j)
end CollatzWielandt
lemma collatzWielandtFn_of_ones_is_pos [DecidableEq n]
    (hA_irred : IsIrreducible A) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    0 < collatzWielandtFn A (fun _ ↦ 1) := by
  let x_ones : n → ℝ := fun _ ↦ 1
  have h_supp_nonempty : ({i | 0 < x_ones i}.toFinset).Nonempty := by
    rw [Set.toFinset_nonempty_iff]
    obtain ⟨i, hi⟩ := Finset.univ_nonempty (α := n)
    exact ⟨i, by simp [x_ones]⟩
  dsimp [collatzWielandtFn]
  rw [dif_pos h_supp_nonempty]
  have h_supp_ones : {i | 0 < x_ones i}.toFinset = Finset.univ := by
    ext a; simp [x_ones, zero_lt_one]
  have h_inf_eq : ({i | 0 < x_ones i}.toFinset.inf' h_supp_nonempty fun i ↦ (A *ᵥ x_ones) i / x_ones i) =
      (Finset.univ.inf' (by rwa [← h_supp_ones]) fun i ↦ (A *ᵥ x_ones) i / x_ones i) := by
    congr
  rw [h_inf_eq]
  apply Finset.inf'_pos Finset.univ_nonempty
  intro i _
  simp_rw [mulVec_apply_eq_sum, x_ones, mul_one, div_one]
  exact row_sum_pos_of_irreducible_nonneg hA_irred hA_nonneg i
