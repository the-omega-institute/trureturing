/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Topology/Compactness/ExtremeValueUSC
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Topology/Compactness/ExtremeValueUSC
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected MCMC finite Perron proof supporting actual weighted graphs. -/
/- Transplanted from or4nge19/MCMC@b901242fd04b6eff425a177e5c9bc6c56257bc62.
Copyright and attribution notices below retained; full license: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean.
Changes: module imports relocated; comment formatting, placement and blank lines adapted for the canonical weighted-graph consumer.
Matteo Cipollina. Changes: unused declarations and branches removed; retained live proof steps preserved; unused local proof terms removed. -/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic
open Set Filter Topology
namespace IsCompact
variable {α : Type*} [TopologicalSpace α]
variable {f : α → ℝ} {K : Set α}
section GeneralProof
lemma upperSemicontinuousOn_iff_upperSemicontinuous {s : Set α}  :
    UpperSemicontinuousOn f s ↔ UpperSemicontinuous (s.domRestrict f) := by
  constructor
  · intro h x c hc
    specialize h x.val x.property c hc
    rw [nhds_subtype_eq_comap_nhdsWithin s x]
    exact h.comap Subtype.val
  · intro h x hx c hc
    specialize h ⟨x, hx⟩ c hc
    rw [nhdsWithin_eq_map_subtype_coe]
    have h_eventually : ∀ᶠ (x' : ↑s) in 𝓝 ⟨x, hx⟩, (s.domRestrict f) x' < c := h
    exact h
theorem bddAbove_image_of_upperSemicontinuousOn (hK : IsCompact K)
    (hf : UpperSemicontinuousOn f K) : BddAbove (f '' K) := by
  by_contra h_unbdd
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : ℕ → Set K := fun n => {x : K | f x < n}
  have hU_open : ∀ n, IsOpen (U n) := by
    intro n
    have hf_restrict : UpperSemicontinuous (K.domRestrict f) :=
      (upperSemicontinuousOn_iff_upperSemicontinuous).mp hf
    rw [upperSemicontinuous_iff_isOpen_preimage] at hf_restrict
    convert hf_restrict n
    ext x
    simp [U, mem_Iio]
  have hU_covers_univ : (univ : Set K) ⊆ ⋃ n, U n := by
    intro x _
    obtain ⟨n, hn⟩ := exists_nat_gt (f x)
    simp only [mem_iUnion]
    exact ⟨n, hn⟩
  rcases isCompact_univ.elim_finite_subcover U hU_open hU_covers_univ with ⟨s, hs_cover⟩
  have s_nonempty : s.Nonempty := by
    rcases K.eq_empty_or_nonempty with rfl | hK_nonempty
    · exfalso; simp at h_unbdd
    · by_contra hs_empty
      rw [Finset.not_nonempty_iff_eq_empty.mp hs_empty] at hs_cover
      aesop
  let N := s.sup id
  have h_union_sub_UN : (⋃ i ∈ s, U i) ⊆ U (N + 1) := by
    intro x hx_union
    simp only [mem_iUnion] at hx_union ⊢
    rcases hx_union with ⟨i, hi_s, hf_lt_i⟩
    have hi_le_N : i ≤ N := Finset.le_sup hi_s (f := id)
    have hi_le_N_real : (i : ℝ) ≤ (N : ℝ) := by norm_cast
    exact hf_lt_i.trans (lt_of_le_of_lt hi_le_N_real (by aesop))
  have h_all_lt : ∀ (x : K), f x < N + 1 := by
    intro x
    have x_in_union : x ∈ ⋃ i ∈ s, U i := hs_cover (mem_univ x)
    have hx : x ∈ U (N + 1) := h_union_sub_UN x_in_union
    simpa [U] using hx
  have h_bdd_final : BddAbove (f '' K) := by
    use (N : ℝ) + 1
    intro y hy_img
    rcases hy_img with ⟨x, hx_K, rfl⟩
    exact (h_all_lt ⟨x, hx_K⟩).le
  exact h_unbdd h_bdd_final
lemma tendsto_const_sub_inv_add_one_atTop (c : ℝ) :
    Tendsto (fun n : ℕ => c - 1 / (n + 1)) atTop (𝓝 c) := by
  have h_inv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using tendsto_const_nhds.sub h_inv
theorem exists_isMaxOn_of_upperSemicontinuousOn (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (hf : UpperSemicontinuousOn f K) : ∃ x₀ ∈ K, IsMaxOn f K x₀ := by
  have h_bdd_above : BddAbove (f '' K) := bddAbove_image_of_upperSemicontinuousOn hK hf
  let s := sSup (f '' K)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : ℕ → Set K := fun n => {x : K | s - 1 / (n + 1 : ℝ) ≤ f x}
  have hC_closed : ∀ n, IsClosed (C n) := by
    intro n
    have hf_restrict : UpperSemicontinuous (K.domRestrict f) :=
      (upperSemicontinuousOn_iff_upperSemicontinuous).mp hf
    have : C n = K.domRestrict f ⁻¹' (Ici (s - 1 / (↑n + 1))) := by
      ext x
      simp [C, s, mem_preimage, mem_Ici]
    rw [this]
    exact UpperSemicontinuous.isClosed_preimage hf_restrict (s - 1 / (↑n + 1))
  have hC_compact : ∀ n, IsCompact (C n) := fun n => (hC_closed n).isCompact
  have hC_directed : Directed (· ⊇ ·) C := by
    intro n m
    refine ⟨max n m, ?_, ?_⟩
    ·
      intro x hx
      have hx_le : s - 1 / ((max n m : ℝ) + 1) ≤ f x := by
        simpa [C] using hx
      have h_thresh : s - 1 / ((n : ℝ) + 1) ≤ s - 1 / ((max n m : ℝ) + 1) := by
        have h_inv : (1 / ((max n m : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) := by
          gcongr; norm_cast; exact le_max_left n m
        simpa using (sub_le_sub_left h_inv s)
      have : s - 1 / ((n : ℝ) + 1) ≤ f x := le_trans h_thresh hx_le
      simpa [C] using this
    ·
      intro x hx
      have hx_le : s - 1 / ((max n m : ℝ) + 1) ≤ f x := by
        simpa [C] using hx
      have h_thresh : s - 1 / ((m : ℝ) + 1) ≤ s - 1 / ((max n m : ℝ) + 1) := by
        have h_inv : (1 / ((max n m : ℝ) + 1)) ≤ 1 / ((m : ℝ) + 1) := by
          gcongr; norm_cast; exact le_max_right n m
        simpa using (sub_le_sub_left h_inv s)
      have : s - 1 / ((m : ℝ) + 1) ≤ f x := le_trans h_thresh hx_le
      simpa [C] using this
  have hC_nonempty : ∀ n, (C n).Nonempty := by
    intro n
    have h_nonempty_image : (f '' K).Nonempty := hK_nonempty.image f
    have h_lt_s : s - 1 / (n + 1 : ℝ) < s :=
      sub_lt_self s (one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n))
    obtain ⟨y, hy_mem, hy_lt⟩ := exists_lt_of_lt_csSup h_nonempty_image h_lt_s
    rcases hy_mem with ⟨x, hx_K, rfl⟩
    use ⟨x, hx_K⟩
    exact le_of_lt hy_lt
  have h_nonempty_inter : (⋂ n, C n).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (t := C) hC_directed hC_nonempty hC_compact hC_closed
  rcases h_nonempty_inter with ⟨x₀, hx₀_inter⟩
  use x₀.val, x₀.prop
  have h_fx_eq_s : f x₀ = s := by
    simp only [mem_iInter] at hx₀_inter
    have h_le : f x₀ ≤ s := le_csSup h_bdd_above (mem_image_of_mem f x₀.prop)
    have h_ge : s ≤ f x₀ :=
      le_of_tendsto (tendsto_const_sub_inv_add_one_atTop s) (Filter.Eventually.of_forall (fun n => hx₀_inter n))
    exact le_antisymm h_le h_ge
  intro y hy
  rw [h_fx_eq_s]
  exact le_csSup h_bdd_above (mem_image_of_mem f hy)
theorem exists_max_on_usco (hK : IsCompact K) (hK_nonempty : K.Nonempty)
    (hf : UpperSemicontinuousOn f K) : ∃ x₀ ∈ K, IsMaxOn f K x₀ :=
  exists_isMaxOn_of_upperSemicontinuousOn hK hK_nonempty hf
end GeneralProof
end IsCompact
