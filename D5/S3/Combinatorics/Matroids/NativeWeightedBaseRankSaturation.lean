/- GID: D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite matroid minimum-weight bases are characterized by every real threshold rank. -/

import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Minor.Restrict
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation

open scoped BigOperators
open Set Matroid

universe u

variable {E : Type u} [Finite E]

noncomputable def baseWeight (w : E → ℝ) (B : Set E) : ℝ :=
  ∑ e ∈ (Set.toFinite B).toFinset, w e

noncomputable def lowerWeightSet (M : Matroid E) (w : E → ℝ) (t : ℝ) : Set E :=
  {e | e ∈ M.E ∧ w e ≤ t}

private lemma baseWeight_exchange (w : E → ℝ) {B : Set E} {e b : E}
    (heB : e ∉ B) (hbB : b ∈ B) :
    baseWeight w (insert e (B \ {b})) = baseWeight w B - w b + w e := by
  classical
  let hB : B.Finite := Set.toFinite B
  let hD : (B \ {b}).Finite := hB.sdiff
  let hI : (insert e (B \ {b})).Finite := hD.insert e
  unfold baseWeight
  change (∑ x ∈ hI.toFinset, w x) =
    (∑ x ∈ hB.toFinset, w x) - w b + w e
  have hI' : hI.toFinset = insert e hD.toFinset := by
    simp [hI]
  have hD' : hD.toFinset = hB.toFinset \ {b} :=
    by simpa using hB.toFinset_sdiff (finite_singleton b) hD
  rw [hI', hD']
  have heD : e ∉ hB.toFinset \ {b} := by simp [heB]
  have hbFin : b ∈ hB.toFinset := by simp [hbB]
  rw [Finset.sum_insert heD]
  rw [Finset.sdiff_singleton_eq_erase]
  have hs := Finset.sum_erase_add hB.toFinset w hbFin
  linarith

private theorem exists_minimum_weight_base (M : Matroid E) (w : E → ℝ) :
    ∃ B, M.IsBase B ∧ ∀ C, M.IsBase C → baseWeight w B ≤ baseWeight w C := by
  classical
  let bases : Set (Set E) := {B | M.IsBase B}
  have hfinite : bases.Finite := by
    apply (M.ground_finite.finite_subsets).subset
    intro B hB
    change M.IsBase B at hB
    exact hB.subset_ground
  obtain ⟨B, hB, hmin⟩ := Set.exists_min_image bases (baseWeight w) hfinite
    (by obtain ⟨B, hB⟩ := M.exists_isBase; exact ⟨B, hB⟩)
  change M.IsBase B at hB
  exact ⟨B, hB, fun C hC => hmin C hC⟩

private theorem minimum_base_saturates_thresholds (M : Matroid E) (w : E → ℝ)
    {B : Set E} (hB : M.IsBase B)
    (hmin : ∀ C, M.IsBase C → baseWeight w B ≤ baseWeight w C) :
    ∀ t : ℝ, (B ∩ lowerWeightSet M w t).ncard =
      (M.eRk (lowerWeightSet M w t)).toNat := by
  classical
  intro t
  let X := lowerWeightSet M w t
  have hXE : X ⊆ M.E := by
    intro e he
    exact he.1
  have hI : M.Indep (B ∩ X) := hB.indep.inter_right X
  have hIX : B ∩ X ⊆ X := inter_subset_right
  have hBasis : M.IsBasis (B ∩ X) X := by
    by_contra hnot
    obtain ⟨J, hJ⟩ := M.exists_isBasis X hXE
    obtain ⟨e, heJ, heI⟩ := hI.exists_insert_of_not_isBasis hIX hnot hJ
    have heX : e ∈ X := hJ.subset heJ.1
    have heNotI : e ∉ B ∩ X := heJ.2
    have heNotB : e ∉ B := by
      intro heB
      exact heNotI ⟨heB, heX⟩
    obtain ⟨b, hb, hB'⟩ :=
      D5.S3.Estimation.ExperimentCost.MinimumCostRoleBasis.exchange_base_over_independent_subset
        hB heNotB heI
    have hbB : b ∈ B := hb.1
    have hbNotX : b ∉ X := by
      intro hbX
      exact hb.2 ⟨hbB, hbX⟩
    have heWt : w e ≤ t := heX.2
    have hbWt : t < w b := by
      exact lt_of_not_ge (fun hb' => hbNotX ⟨hB.subset_ground hbB, hb'⟩)
    have hlt : baseWeight w (insert e (B \ {b})) < baseWeight w B := by
      rw [baseWeight_exchange w heNotB hbB]
      linarith
    exact (not_lt_of_ge (hmin _ hB')) hlt
  rw [ncard_def, hBasis.encard_eq_eRk]

private lemma sorted_list_sum_le (w : E → ℝ) {l₁ l₂ : List E}
    (h₁ : l₁.Pairwise (fun x y => w x ≤ w y))
    (h₂ : l₂.Pairwise (fun x y => w x ≤ w y))
    (hlen : l₁.length = l₂.length)
    (hprefix : ∀ a : ℝ,
      List.countP (fun x => decide (w x ≤ a)) l₁ ≥
        List.countP (fun x => decide (w x ≤ a)) l₂) :
    (l₁.map w).sum ≤ (l₂.map w).sum := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => simp
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases l₂ with
      | nil => simp at hlen
      | cons y ys =>
          have hxy : w x ≤ w y := by
            by_contra hxy'
            have hyx : w y < w x := lt_of_not_ge hxy'
            have hxrest : ∀ z ∈ xs, w x ≤ w z :=
              (List.pairwise_cons.mp h₁).1
            have hzero : List.countP (fun z => decide (w z ≤ w y)) (x :: xs) = 0 := by
              rw [List.countP_eq_zero]
              intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · simp [not_le_of_gt hyx]
              · have hxz := hxrest z hz
                simp [not_le_of_gt (hyx.trans_le hxz)]
            have hpos : 0 < List.countP (fun z => decide (w z ≤ w y)) (y :: ys) := by
              simp [List.countP_cons]
            have := hprefix (w y)
            omega
          have htail : ∀ a : ℝ,
              List.countP (fun z => decide (w z ≤ a)) xs ≥
                List.countP (fun z => decide (w z ≤ a)) ys := by
            intro a
            have h := hprefix a
            have hxrest : ∀ z ∈ xs, w x ≤ w z :=
              (List.pairwise_cons.mp h₁).1
            have hyrest : ∀ z ∈ ys, w y ≤ w z :=
              (List.pairwise_cons.mp h₂).1
            by_cases hxa : w x ≤ a
            · by_cases hya : w y ≤ a
              · simpa [List.countP_cons, hxa, hya] using h
              · have hyzero : List.countP (fun z => decide (w z ≤ a)) ys = 0 := by
                  rw [List.countP_eq_zero]
                  intro z hz
                  have hyz := hyrest z hz
                  simp [not_le_of_gt (lt_of_not_ge hya |>.trans_le hyz)]
                simpa [List.countP_cons, hxa, hya, hyzero] using h
            · by_cases hya : w y ≤ a
              · exact False.elim (hxa (hxy.trans hya))
              · simpa [List.countP_cons, hxa, hya] using h
          have hlen' : xs.length = ys.length := by simp_all
          have hsum := ih (l₂ := ys) (List.pairwise_cons.mp h₁).2
            (List.pairwise_cons.mp h₂).2 hlen' htail
          simp only [List.map_cons, List.sum_cons]
          linarith

private lemma sorted_weight_prefix_comparison (w : E → ℝ) {s t : Finset E} (hcard : s.card = t.card)
    (hprefix : ∀ a : ℝ, (s.filter (fun e => w e ≤ a)).card ≥
      (t.filter (fun e => w e ≤ a)).card) :
    (∑ e ∈ s, w e) ≤ ∑ e ∈ t, w e := by
  classical
  letI := Fintype.ofFinite E
  letI : LinearOrder E := LinearOrder.lift' (Fintype.equivFin E)
    (Fintype.equivFin E).injective
  let r : E → E → Prop := fun x y =>
    w x < w y ∨ (w x = w y ∧ x ≤ y)
  letI : IsTrans E r := ⟨by
    intro a b c hab hbc
    rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hbc with hbc | ⟨hbc, hbc'⟩
    · exact Or.inl (lt_trans hab hbc)
    · exact Or.inl (hbc ▸ hab)
    · exact Or.inl (hab ▸ hbc)
    · exact Or.inr ⟨hab.trans hbc, le_trans hab' hbc'⟩⟩
  letI : Std.Antisymm r := ⟨by
    intro a b hab hba
    rcases hab with hab | ⟨hab, hab'⟩ <;> rcases hba with hba | ⟨hba, hba'⟩
    · exact False.elim (not_lt_of_ge (le_of_lt hba) hab)
    · exact False.elim ((lt_irrefl _)
        (hba ▸ hab))
    · exact False.elim ((lt_irrefl _)
        (hab ▸ hba))
    · exact le_antisymm hab' hba'⟩
  letI : Std.Total r := ⟨by
    intro a b
    change (w a < w b ∨ (w a = w b ∧ a ≤ b)) ∨
      (w b < w a ∨ (w b = w a ∧ b ≤ a))
    by_cases h : w a < w b
    · exact Or.inl (Or.inl h)
    · by_cases h' : w b < w a
      · exact Or.inr (Or.inl h')
      · have heq : w a = w b := le_antisymm (not_lt.mp h') (not_lt.mp h)
        by_cases hab : a ≤ b
        · exact Or.inl (Or.inr ⟨heq, hab⟩)
        · exact Or.inr (Or.inr ⟨heq.symm, le_of_not_ge hab⟩)⟩
  let sl := s.sort r
  let tl := t.sort r
  have hsl : sl.Pairwise r := Finset.pairwise_sort s r
  have htl : tl.Pairwise r := Finset.pairwise_sort t r
  have hlen : sl.length = tl.length := by simp [sl, tl, hcard]
  have hslw : sl.Pairwise (fun x y => w x ≤ w y) := hsl.imp (by
    intro a b h
    change w a < w b ∨ (w a = w b ∧ a ≤ b) at h
    rcases h with h | ⟨h, _⟩
    · exact h.le
    · exact h.le)
  have htlw : tl.Pairwise (fun x y => w x ≤ w y) := htl.imp (by
    intro a b h
    change w a < w b ∨ (w a = w b ∧ a ≤ b) at h
    rcases h with h | ⟨h, _⟩
    · exact h.le
    · exact h.le)
  have hprefix' : ∀ a : ℝ,
      List.countP (fun x => decide (w x ≤ a)) sl ≥
        List.countP (fun x => decide (w x ≤ a)) tl := by
    intro a
    have hsfilter : (s.filter (fun e => w e ≤ a)).card =
        List.countP (fun x => decide (w x ≤ a)) sl := by
      rw [← Finset.sort_toFinset s r]
      exact List.Nodup.card_eq_countP (Finset.sort_nodup s r)
    have htfilter : (t.filter (fun e => w e ≤ a)).card =
        List.countP (fun x => decide (w x ≤ a)) tl := by
      rw [← Finset.sort_toFinset t r]
      exact List.Nodup.card_eq_countP (Finset.sort_nodup t r)
    have hh := hprefix a
    rw [hsfilter, htfilter] at hh
    exact hh
  have hsum := sorted_list_sum_le w hslw htlw hlen hprefix'
  have hsums : (∑ e ∈ s, w e) = (sl.map w).sum := by
    simpa [sl] using (List.sum_toFinset w (Finset.sort_nodup s r))
  have htums : (∑ e ∈ t, w e) = (tl.map w).sum := by
    simpa [tl] using (List.sum_toFinset w (Finset.sort_nodup t r))
  rw [hsums, htums]
  exact hsum

private theorem threshold_saturation_is_minimum (M : Matroid E) (w : E → ℝ)
    {B : Set E} (hB : M.IsBase B)
    (hsat : ∀ t : ℝ, (B ∩ lowerWeightSet M w t).ncard =
      (M.eRk (lowerWeightSet M w t)).toNat) :
    ∀ C, M.IsBase C → baseWeight w B ≤ baseWeight w C := by
  classical
  intro C hC
  let hBfin : B.Finite := Set.toFinite B
  let hCfin : C.Finite := Set.toFinite C
  let s : Finset E := hBfin.toFinset
  let tset : Finset E := hCfin.toFinset
  have hcard : s.card = tset.card := by
    rw [← Set.ncard_eq_toFinset_card B hBfin, ← Set.ncard_eq_toFinset_card C hCfin]
    exact hB.ncard_eq_ncard_of_isBase hC
  have hprefix : ∀ a : ℝ,
      (s.filter (fun e => w e ≤ a)).card ≥ (tset.filter (fun e => w e ≤ a)).card := by
    intro a
    let X := lowerWeightSet M w a
    have rank_bound (D : Set E) (hD : M.IsBase D) :
        (D ∩ X).ncard ≤ (M.eRk X).toNat := by
      have hI : M.Indep (D ∩ X) := hD.indep.inter_right X
      have hmono : M.eRk (D ∩ X) ≤ M.eRk X := M.eRk_mono inter_subset_right
      rw [ncard_def, ← hI.eRk_eq_encard]
      exact ENat.toNat_le_toNat hmono (M.isRkFinite_set X).eRk_lt_top.ne
    have hfilter (D : Set E) (hD : D.Finite) (hDE : D ⊆ M.E) :
        ((hD.toFinset).filter (fun e => w e ≤ a)).card =
          (D ∩ X).ncard := by
      let hDX : (D ∩ X).Finite := hD.inter_of_left X
      rw [Set.ncard_eq_toFinset_card (D ∩ X) hDX]
      congr 1
      ext e
      simp only [Finset.mem_filter]
      simp only [hD.mem_toFinset]
      rw [hDX.mem_toFinset]
      simp only [mem_inter_iff, X, lowerWeightSet, mem_setOf_eq]
      constructor
      · intro he
        have heD : e ∈ D := by simpa using he.1
        exact ⟨heD, hDE heD, he.2⟩
      · rintro ⟨heD, heE, hew⟩
        exact ⟨by simpa using heD, hew⟩
    have hCbound := rank_bound C hC
    have hBsat := hsat a
    have hcardSets : (C ∩ X).ncard ≤ (B ∩ X).ncard := by
      rw [hBsat]
      exact hCbound
    have hBfilter := hfilter B hBfin hB.subset_ground
    have hCfilter := hfilter C hCfin hC.subset_ground
    change (hBfin.toFinset.filter (fun e => w e ≤ a)).card ≥
      (hCfin.toFinset.filter (fun e => w e ≤ a)).card
    rw [hBfilter, hCfilter]
    exact hcardSets
  have hsum := sorted_weight_prefix_comparison w hcard hprefix
  simpa [baseWeight, s, tset, hBfin, hCfin] using hsum

theorem native_weighted_base_rank_saturation (M : Matroid E) (w : E → ℝ) :
    (∃ B, M.IsBase B ∧
      ∀ C, M.IsBase C → baseWeight w B ≤ baseWeight w C) ∧
    ∀ B, M.IsBase B →
      ((∀ C, M.IsBase C → baseWeight w B ≤ baseWeight w C) ↔
        ∀ t : ℝ,
          (B ∩ lowerWeightSet M w t).ncard =
            (M.eRk (lowerWeightSet M w t)).toNat) := by
  constructor
  · exact exists_minimum_weight_base M w
  · intro B hB
    constructor
    · intro hmin
      exact minimum_base_saturates_thresholds M w hB hmin
    · intro hsat
      exact threshold_saturation_is_minimum M w hB hsat

#print axioms native_weighted_base_rank_saturation

end D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
