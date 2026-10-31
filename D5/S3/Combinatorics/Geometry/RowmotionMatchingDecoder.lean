/- GID: D5/S3/Combinatorics/Geometry/RowmotionMatchingDecoder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RowmotionMatchingDecoder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recovery of actual noncrossing partners from cut endpoint data. -/

import D5.S3.Combinatorics.PerfectMatchings.OrderedMatchingIntervals
import Mathlib.Data.Finset.Sort

/-! Recovery of the pairing from its opening predicate at a fixed cut. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder

open CupCapBridgeProposal

/-- The smaller endpoint of a pair after cutting the circle. -/
def IsOpening {m : ℕ} (M : NCMatching m) (k : Fin m) : Prop := k < M.partner k

/-- Recovery retains the actual pairs, not merely the support of the matching. -/
theorem partner_eq_of_openings {m : ℕ} (M Q : NCMatching m)
    (h : ∀ k, IsOpening M k ↔ IsOpening Q k) : M.partner = Q.partner := by
  have close_eq : ∀ k : Fin m, M.partner k < k → M.partner k = Q.partner k := by
    intro k
    induction hk : k.val using Nat.strong_induction_on generalizing k with
    | h v ih =>
      intro hclose
      have hcloseQ : Q.partner k < k := by
        have hn : ¬ IsOpening Q k := fun hh => (not_lt_of_gt hclose) ((h k).mpr hh)
        have hne := Q.noFixed k
        dsimp [IsOpening] at hn
        exact lt_of_le_of_ne (le_of_not_gt hn) hne
      have same (A B : NCMatching m)
          (hab : ∀ t, IsOpening A t ↔ IsOpening B t)
          (hind : ∀ t : Fin m, t.val < v → A.partner t < t → A.partner t = B.partner t)
          (ha : A.partner k < k) (hb : B.partner k < k) :
          ¬ A.partner k < B.partner k := by
        intro hlt
        have ins := A.interior_closed (A.partner k) (B.partner k) hlt
          (by simpa only [A.involutive k] using hb)
        have hopB : IsOpening B (B.partner k) := by
          dsimp [IsOpening]
          simpa only [B.involutive k] using hb
        have hopA : B.partner k < A.partner (B.partner k) := (hab _).mpr hopB
        have hprev : A.partner (B.partner k) < k := by
          simpa only [A.involutive k] using ins.2
        have heq := hind (A.partner (B.partner k)) (by change (A.partner (B.partner k)).val < k.val at hprev; omega)
          (by simpa only [A.involutive (B.partner k)] using hopA)
        have heq' : B.partner k = B.partner (A.partner (B.partner k)) := by
          simpa only [A.involutive (B.partner k)] using heq
        have heq'' := B.partner.injective heq'
        exact (ne_of_lt hprev) heq''.symm
      have hMN : ¬ M.partner k < Q.partner k :=
        same M Q h (fun t ht hc => ih t.val ht t rfl hc) hclose hcloseQ
      have hNM : ¬ Q.partner k < M.partner k :=
        same Q M (fun t => (h t).symm)
          (fun t ht hc => by
            have hm : M.partner t < t := by
              have hn : ¬ IsOpening M t := fun hh => (not_lt_of_gt hc) ((h t).mp hh)
              dsimp [IsOpening] at hn
              exact lt_of_le_of_ne (le_of_not_gt hn) (M.noFixed t)
            exact (ih t.val ht t rfl hm).symm)
          hcloseQ hclose
      exact le_antisymm (le_of_not_gt hNM) (le_of_not_gt hMN)
  apply Equiv.ext
  intro k
  rcases lt_or_gt_of_ne (M.noFixed k) with hc | ho
  · exact close_eq k hc
  · have hc : M.partner (M.partner k) < M.partner k := by
      simpa only [M.involutive k] using ho
    have heq := close_eq (M.partner k) hc
    have heq' : k = Q.partner (M.partner k) := by simpa only [M.involutive k] using heq
    have heq'' := congrArg Q.partner heq'
    simpa only [Q.involutive (M.partner k)] using heq''.symm

private theorem opening_card (M : NCMatching 6) :
    (Finset.univ.filter (IsOpening M)).card = 3 := by
  classical
  let a := Finset.univ.filter (IsOpening M)
  let b := Finset.univ.filter (fun k => ¬ IsOpening M k)
  have himage : a.image M.partner = b := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, a, b]
    constructor
    · rintro ⟨j, hj, rfl⟩ hh
      exact (not_lt_of_gt hj) (by simpa only [IsOpening, M.involutive j] using hh)
    · intro hk
      have hc : M.partner k < k :=
        lt_of_le_of_ne (le_of_not_gt hk) (M.noFixed k)
      exact ⟨M.partner k, by simpa only [IsOpening, M.involutive k] using hc,
        M.involutive k⟩
  have hc : a.card = b.card := by
    rw [← himage, Finset.card_image_of_injective _ M.partner.injective]
  have hs := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := IsOpening M)
  change a.card + b.card = _ at hs
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  change a.card = 3
  omega

private theorem closing_card (M : NCMatching 6) :
    (Finset.univ.filter (fun k => ¬ IsOpening M k)).card = 3 := by
  classical
  have hs := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := IsOpening M)
  rw [opening_card M] at hs
  simp only [Finset.card_univ, Fintype.card_fin] at hs
  omega

/-- Increasing opening ranks at the ordinary cut. -/
noncomputable def openingRanks (M : NCMatching 6) : Fin 3 ↪o Fin 6 := by
  classical
  exact (Finset.univ.filter (IsOpening M)).orderEmbOfFin (opening_card M)

/-- Increasing closing ranks at the same cut, independently sorted. -/
noncomputable def closingRanks (M : NCMatching 6) : Fin 3 ↪o Fin 6 := by
  classical
  exact (Finset.univ.filter (fun k => ¬ IsOpening M k)).orderEmbOfFin (closing_card M)

private theorem opening_is_open (M : NCMatching 6) (j : Fin 3) :
    IsOpening M (openingRanks M j) := by
  classical
  exact (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem _ (opening_card M) j)).2

private theorem closing_is_closed (M : NCMatching 6) (j : Fin 3) :
    M.partner (closingRanks M j) < closingRanks M j := by
  classical
  have hn : ¬ IsOpening M (closingRanks M j) :=
    (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem _ (closing_card M) j)).2
  exact lt_of_le_of_ne (le_of_not_gt hn) (M.noFixed _)

private theorem opening_surjective (M : NCMatching 6) (k : Fin 6)
    (hk : IsOpening M k) : ∃ j, openingRanks M j = k := by
  classical
  let x : {k // k ∈ Finset.univ.filter (IsOpening M)} := ⟨k, by simpa⟩
  let j : Fin 3 := ((Finset.univ.filter (IsOpening M)).orderIsoOfFin (opening_card M)).symm x
  refine ⟨j, ?_⟩
  exact congrArg Subtype.val ((Finset.orderIsoOfFin _ (opening_card M)).apply_symm_apply x)

private theorem closing_surjective (M : NCMatching 6) (k : Fin 6)
    (hk : ¬ IsOpening M k) : ∃ j, closingRanks M j = k := by
  classical
  let x : {k // k ∈ Finset.univ.filter (fun k => ¬ IsOpening M k)} := ⟨k, by simpa⟩
  let j : Fin 3 := ((Finset.univ.filter (fun k => ¬ IsOpening M k)).orderIsoOfFin (closing_card M)).symm x
  refine ⟨j, ?_⟩
  exact congrArg Subtype.val ((Finset.orderIsoOfFin _ (closing_card M)).apply_symm_apply x)

private theorem opening_lt_closing (M : NCMatching 6) (j : Fin 3) :
    openingRanks M j < closingRanks M j := by
  classical
  by_contra hn
  have hle : closingRanks M j ≤ openingRanks M j := le_of_not_gt hn
  let f : Fin (j.val + 1) → Fin j.val := fun i => by
    let ci : Fin 3 := ⟨i.val, by omega⟩
    let k := M.partner (closingRanks M ci)
    have hk : IsOpening M k := by
      dsimp [IsOpening, k]
      simpa only [M.involutive (closingRanks M ci)] using closing_is_closed M ci
    let q := Classical.choose (opening_surjective M k hk)
    have hq : openingRanks M q = k := Classical.choose_spec (opening_surjective M k hk)
    refine ⟨q.val, ?_⟩
    have hqj : q < j := by
      by_contra h
      have hjo : openingRanks M j ≤ openingRanks M q := (openingRanks M).monotone (le_of_not_gt h)
      have hic : closingRanks M ci ≤ closingRanks M j := (closingRanks M).monotone (by
        change i.val ≤ j.val
        omega)
      have hkc : k < closingRanks M ci := closing_is_closed M ci
      rw [hq] at hjo
      exact (not_lt_of_ge (le_trans (le_trans hic hle) hjo)) hkc
    exact hqj
  have hf : Function.Injective f := by
    intro i l hil
    have hval := congrArg Fin.val hil
    dsimp [f] at hval
    have hp := congrArg (fun q : Fin 3 => openingRanks M q)
      (Fin.ext hval)
    rw [Classical.choose_spec (opening_surjective M _ _),
      Classical.choose_spec (opening_surjective M _ _)] at hp
    have hi := M.partner.injective hp
    have hc := (closingRanks M).injective hi
    exact Fin.ext (congrArg Fin.val hc)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

#print axioms partner_eq_of_openings

end D5.S3.Combinatorics.Geometry.RowmotionMatchingDecoder
