/- GID: D5/S3/Combinatorics/PerfectMatchings/ClosedCapFiber
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/ClosedCapFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Closed-cap compatibility and weight transport. -/
import D5.S3.Combinatorics.PerfectMatchings.BoundaryProductTransport
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CupCapBridgeProposal

section Closed
variable {m : ℕ} (M : NCMatching (m + 2)) (j : Fin (m + 1))
  (hc : M.partner j.castSucc = j.succ)

theorem close_partner_right : M.partner j.succ = j.castSucc := by
  simpa only [M.involutive] using congrArg M.partner hc.symm

theorem close_shortUnchanged (k : Fin m) : ShortUnchanged M j k := by
  rw [ShortUnchanged, hc, close_partner_right M j hc]
  exact ⟨(skipPair_survives j k).2, (skipPair_survives j k).1⟩

theorem close_skip_partner (k : Fin m) :
    skipPair j ((capSurgery M j).partner k) = M.partner (skipPair j k) :=
  skipPair_unchanged_partner M j k (close_shortUnchanged M j hc k)

/-- Free middle labels, with both directions proved on the actual side equations. -/
theorem close_compatible_iff {L : Type*} (y : Fin (m + 1) → L) (B : L) :
    Compatible M (detourLabels j y B) ↔ Compatible (capSurgery M j) y := by
  constructor
  · intro hx k
    have hk := hx (skipPair j k)
    rw [← close_skip_partner M j hc k] at hk
    simpa only [detour_skip_left, detour_skip_right] using hk
  · intro hy t
    by_cases hta : t = j.castSucc
    · subst t
      rw [hc]
      simpa only [detour_left_consumed, detour_middle_consumed,
        detour_middle_consumed', detour_right_consumed] using
        And.intro (Eq.refl (y j)) (Eq.refl B)
    by_cases htb : t = j.succ
    · subst t
      rw [close_partner_right M j hc]
      simpa only [detour_left_consumed, detour_middle_consumed,
        detour_middle_consumed', detour_right_consumed] using
        And.intro (Eq.refl B) (Eq.refl (y j))
    let k := unskipPair j t hta htb
    have hk : skipPair j k = t := skipPair_unskipPair j t hta htb
    rw [← hk, ← close_skip_partner M j hc k]
    simpa only [detour_skip_left, detour_skip_right] using hy k

/-- Literal opening-endpoint product transport, before the compatibility indicator. -/
theorem close_opening_product {L : Type*} (q : L → ℝ)
    (y : Fin (m + 1) → L) (B : L) :
    openingProduct q M (detourLabels j y B) =
      (q B / q (y j)) * openingProduct q (capSurgery M j) y := by
  have hab : j.castSucc < j.succ := by change j.val < j.val + 1; omega
  have hba : ¬ j.succ < j.castSucc := not_lt_of_ge (le_of_lt hab)
  unfold openingProduct
  rw [prod_skipPair j]
  have ha : openingFactor q M (detourLabels j y B) j.castSucc = q B / q (y j) := by
    simp only [openingFactor, hc, hab, if_true,
      detour_middle_consumed, detour_left_consumed]
  have hb : openingFactor q M (detourLabels j y B) j.succ = 1 := by
    simp only [openingFactor, close_partner_right M j hc, hba, if_false]
  rw [ha, hb, mul_one]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact (unchanged_factor M j q y B k (close_shortUnchanged M j hc k)).symm

/-- The close potential identity also covers incompatible y, where both sides vanish. -/
theorem close_boundaryPotential {L : Type*} (q : L → ℝ)
    (y : Fin (m + 1) → L) (B : L) :
    boundaryPotential q M (detourLabels j y B) * (q B / q (y j)) =
      (q B / q (y j)) ^ 2 * boundaryPotential q (capSurgery M j) y := by
  classical
  by_cases hy : Compatible (capSurgery M j) y
  · have hx := (close_compatible_iff M j hc y B).mpr hy
    rw [boundaryPotential_eq, if_pos hx, boundaryPotential_eq, if_pos hy,
      close_opening_product M j hc]
    ring
  · have hx : ¬ Compatible M (detourLabels j y B) := by
      intro h
      exact hy ((close_compatible_iff M j hc y B).mp h)
    rw [boundaryPotential_eq, if_neg hx, boundaryPotential_eq, if_neg hy]
    ring

end Closed
end CupCapBridgeProposal
