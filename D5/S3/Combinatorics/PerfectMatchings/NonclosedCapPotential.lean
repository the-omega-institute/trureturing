/- GID: D5/S3/Combinatorics/PerfectMatchings/NonclosedCapPotential
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/NonclosedCapPotential
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Basic]
   utility: none
   digest: Exact nonclosed-cap boundary potential. -/
import D5.S3.Combinatorics.PerfectMatchings.NonclosedCapLabels
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CupCapBridgeProposal

section AffectedProducts
variable {m : ℕ} (M : NCMatching (m + 2)) (j : Fin (m + 1))
  (hn : M.partner j.castSucc ≠ j.succ)

include hn

/-- Four *distinct* old affected endpoints; every other endpoint is in U. -/
theorem old_affected_product {K : Type*} [CommMonoid K] (f : Fin (m + 2) → K) :
    (∏ t ∈ Finset.univ.filter (fun t => ¬ Unchanged M j t), f t) =
      f j.castSucc * f j.succ * f (M.partner j.castSucc) * f (M.partner j.succ) := by
  classical
  have hab : j.castSucc ≠ j.succ := by
    intro h
    have hval : j.val = j.val + 1 := congrArg Fin.val h
    omega
  have hua := M.noFixed j.castSucc
  have hvb := M.noFixed j.succ
  have hva := (capV_survives M j hn).1
  have huv : M.partner j.castSucc ≠ M.partner j.succ := M.partner.injective.ne hab
  have hs : Finset.univ.filter (fun t => ¬ Unchanged M j t) =
      {j.castSucc, j.succ, M.partner j.castSucc, M.partner j.succ} := by
    apply Finset.ext
    intro t
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Unchanged]
    tauto
  rw [hs]
  simp only [Finset.prod_insert, Finset.prod_singleton,
    Finset.mem_insert, Finset.mem_singleton,
    hab, hua, hua.symm, hvb, hvb.symm, hva, hva.symm,
    hn, hn.symm, huv, huv.symm, not_false_eq_true, or_self]
  ac_rfl

/-- The two distinct surviving partners are exactly the new affected endpoints. -/
theorem short_affected_product {K : Type*} [CommMonoid K] (f : Fin m → K) :
    (∏ k ∈ Finset.univ.filter (fun k => ¬ ShortUnchanged M j k), f k) =
      f (capU M j hn) * f (capV M j hn) := by
  classical
  have huv : capU M j hn ≠ capV M j hn := by
    intro h
    have h' := congrArg (skipPair j) h
    rw [skip_capU, skip_capV] at h'
    have hab := M.partner.injective h'
    have hv : j.val = j.val + 1 := congrArg Fin.val hab
    omega
  have hs : Finset.univ.filter (fun k => ¬ ShortUnchanged M j k) =
      {capU M j hn, capV M j hn} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, ShortUnchanged,
      ← skip_capU M j hn, ← skip_capV M j hn, Set.mem_setOf_eq]
    constructor
    · intro h
      by_cases hu : k = capU M j hn
      · exact Or.inl hu
      · apply Or.inr
        by_contra hv
        exact h ⟨fun he => hu (skipPair_injective j he),
          fun he => hv (skipPair_injective j he)⟩
    · rintro (rfl | rfl) h
      · exact h.1 rfl
      · exact h.2 rfl
  rw [hs, Finset.prod_pair huv]
end AffectedProducts

section Potential
variable {L : Type*} {m : ℕ} (M : NCMatching (m + 2)) (j : Fin (m + 1))
  (hn : M.partner j.castSucc ≠ j.succ)
  (q : L → ℝ) (hq : ∀ a, q a ≠ 0)
  (y : Fin (m + 1) → L) (B : L)

include hn hq

/-- Product transport with the cap coefficient, from the literal finite products.
The proof does not assume the affected coefficient identity: it proves it after
extracting precisely four old and two new endpoints from those products. -/
theorem nonclose_opening_product
    (hx : Compatible M (detourLabels j y B)) :
    openingProduct q M (detourLabels j y B) * (q B / q (y j)) =
      openingProduct q (capSurgery M j) y := by
  let a := j.castSucc
  let b := j.succ
  let u := M.partner a
  let v := M.partner b
  let k := capU M j hn
  let l := capV M j hn
  let A := y j
  let x := detourLabels j y B
  have hxy := (nonclose_compatible_iff M j hn y B).mp hx
  have hy := hxy.1
  have hB : B = y k.castSucc := hxy.2
  have hA : A = y k.succ := cap_outer_label M j hn y hy
  have hp := hy k
  change y k.castSucc = y ((capSurgery M j).partner k).succ ∧
    y k.succ = y ((capSurgery M j).partner k).castSucc at hp
  have hkl : (capSurgery M j).partner k = l := capSurgery_partner_U M j hn
  have hlk : (capSurgery M j).partner l = k := capSurgery_partner_V M j hn
  rw [hkl] at hp
  have hls : y l.succ = B := hp.1.symm.trans hB.symm
  have hlc : y l.castSucc = A := hp.2.symm.trans hA.symm
  have hu := hx a
  have hv := hx b
  change x a.castSucc = x u.succ ∧ x a.succ = x u.castSucc at hu
  change x b.castSucc = x v.succ ∧ x b.succ = x v.castSucc at hv
  have hua : x u.succ = A := by
    simpa only [x, a, A, detour_left_consumed] using hu.1.symm
  have hub : x u.castSucc = B := by
    simpa only [x, a, detour_middle_consumed] using hu.2.symm
  have hvb : x v.succ = B := by
    simpa only [x, b, detour_middle_consumed'] using hv.1.symm
  have hva : x v.castSucc = A := by
    simpa only [x, b, A, detour_right_consumed] using hv.2.symm
  have haL : x a.castSucc = A := detour_left_consumed j y B
  have haR : x a.succ = B := detour_middle_consumed j y B
  have hbL : x b.castSucc = B := detour_middle_consumed' j y B
  have hbR : x b.succ = A := detour_right_consumed j y B
  have hkorder : (k < l) ↔ u < v := by
    have h := (skipPair_strictMono j).lt_iff_lt (a := k) (b := l)
    rw [skip_capU M j hn, skip_capV M j hn] at h
    exact h.symm
  have hlorder : (l < k) ↔ v < u := by
    have h := (skipPair_strictMono j).lt_iff_lt (a := l) (b := k)
    rw [skip_capV M j hn, skip_capU M j hn] at h
    exact h.symm
  have hfa : openingFactor q M x a = if a < u then q B / q A else 1 := by
    change (if a < u then q (x a.succ) / q (x a.castSucc) else 1) = _
    rw [haL, haR]
  have hfb : openingFactor q M x b = if b < v then q A / q B else 1 := by
    change (if b < v then q (x b.succ) / q (x b.castSucc) else 1) = _
    rw [hbL, hbR]
  have hpu : M.partner u = a := M.involutive a
  have hpv : M.partner v = b := M.involutive b
  have hfu : openingFactor q M x u = if u < a then q A / q B else 1 := by
    simp only [openingFactor, hpu, hua, hub]
  have hfv : openingFactor q M x v = if v < b then q B / q A else 1 := by
    simp only [openingFactor, hpv, hva, hvb]
  have hfk : openingFactor q (capSurgery M j) y k =
      if u < v then q A / q B else 1 := by
    simp only [openingFactor, hkl, hkorder, ← hA, ← hB]
  have hfl : openingFactor q (capSurgery M j) y l =
      if v < u then q B / q A else 1 := by
    simp only [openingFactor, hlk, hlorder, hlc, hls]
  obtain ⟨hold, hnew⟩ := opening_products_split M j q y B
  rw [old_affected_product M j hn] at hold
  rw [short_affected_product M j hn] at hnew
  change openingProduct q M x = _ at hold
  change openingProduct q M x * (q B / q A) = _
  rw [hold, hnew]
  change (openingFactor q M x a * openingFactor q M x b *
    openingFactor q M x u * openingFactor q M x v * _) * (q B / q A) =
    (openingFactor q (capSurgery M j) y k * openingFactor q (capSurgery M j) y l) * _
  rw [hfa, hfb, hfu, hfv, hfk, hfl]
  have hab : a < b := by change j.val < j.val + 1; omega
  have hqA := hq A
  have hqB := hq B
  have hcases := cap_order_cases M j
  change u = b ∨ (u < a ∧ b < v) ∨ (b < v ∧ v < u) ∨ (v < u ∧ u < a) at hcases
  rcases hcases with hc | hs | hl | hr
  · exact False.elim (hn hc)
  · have hau : ¬ a < u := not_lt_of_ge (le_of_lt hs.1)
    have hvb : ¬ v < b := not_lt_of_ge (le_of_lt hs.2)
    have huv : u < v := lt_trans hs.1 (lt_trans hab hs.2)
    have hvu : ¬ v < u := not_lt_of_ge (le_of_lt huv)
    simp only [if_neg hau, if_pos hs.2, if_pos hs.1, if_neg hvb, if_pos huv, if_neg hvu]
    field_simp [hqA, hqB]
    <;> ring
  · have hau : a < u := lt_trans hab (lt_trans hl.1 hl.2)
    have hua : ¬ u < a := not_lt_of_ge (le_of_lt hau)
    have hvb : ¬ v < b := not_lt_of_ge (le_of_lt hl.1)
    have huv : ¬ u < v := not_lt_of_ge (le_of_lt hl.2)
    simp only [if_pos hau, if_pos hl.1, if_neg hua, if_neg hvb, if_neg huv, if_pos hl.2]
    field_simp [hqA, hqB]
    <;> ring
  · have hau : ¬ a < u := not_lt_of_ge (le_of_lt hr.2)
    have hvb : v < b := lt_trans hr.1 (lt_trans hr.2 hab)
    have hbv : ¬ b < v := not_lt_of_ge (le_of_lt hvb)
    have huv : ¬ u < v := not_lt_of_ge (le_of_lt hr.1)
    simp only [if_neg hau, if_neg hbv, if_pos hr.2, if_pos hvb, if_neg huv, if_pos hr.1]
    field_simp [hqA, hqB]
    <;> ring

/-- Exact nonclose potential identity, under compatibility of the lifted labels. -/
theorem nonclose_boundaryPotential (hx : Compatible M (detourLabels j y B)) :
    boundaryPotential q M (detourLabels j y B) * (q B / q (y j)) =
      boundaryPotential q (capSurgery M j) y := by
  have hy := compatible_reconnected M j y B hx
  rw [boundaryPotential_eq, if_pos hx, boundaryPotential_eq, if_pos hy]
  exact nonclose_opening_product M j hn q hq y B hx
end Potential
end CupCapBridgeProposal
