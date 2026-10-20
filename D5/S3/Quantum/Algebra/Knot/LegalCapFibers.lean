/- GID: D5/S3/Quantum/Algebra/Knot/LegalCapFibers
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Knot/LegalCapFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Adjacent cap fibers of rooted legal paths. -/
import D5.S3.Combinatorics.PerfectMatchings.NonclosedCapLabels
import D5.S3.Quantum.Algebra.Knot.CapFiberContract

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CupCapBridgeProposal
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb

/-- An actual fixed-root legal lift. No substitute path carrier is introduced. -/
def legalDetour {L : Type*} [Fintype L] [DecidableEq L]
    {m : ℕ} (R : L → L → Prop) (hR : Symmetric R) (s : L)
    (j : Fin (m + 1)) (y : LegalPath R m s s)
    (B : {b : L // R (y.val j) b}) : LegalPath R (m + 2) s s := by
  refine ⟨detourLabels j y.val B.val, ?_, ?_, ?_⟩
  · have hz : (0 : Fin (m + 3)).val ≤ j.val := Nat.zero_le _
    simpa [detourLabels, hz] using y.property.1
  · have hl : ¬ (Fin.last (m + 2)).val ≤ j.val := by have := j.isLt; simp; omega
    have hn : (Fin.last (m + 2)).val ≠ j.val + 1 := by have := j.isLt; simp; omega
    simpa [detourLabels, hl, hn] using y.property.2.1
  · intro t
    by_cases hta : t = j.castSucc
    · subst t
      simpa only [detour_left_consumed, detour_middle_consumed] using B.property
    by_cases htb : t = j.succ
    · subst t
      simpa only [detour_middle_consumed', detour_right_consumed] using hR B.property
    let k := unskipPair j t hta htb
    have hk : skipPair j k = t := skipPair_unskipPair j t hta htb
    rw [← hk, detour_skip_left, detour_skip_right]
    exact y.property.2.2 k

section Closed
variable {m : ℕ} (M : NCMatching (m + 2)) (j : Fin (m + 1))
  (hc : M.partner j.castSucc = j.succ)

/-- Exactly the entire closed conjunct of CapFiberGoal on actual rooted paths. -/
theorem capSurgery_close_fiber {L : Type*} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) (q : L → ℝ) (s : L) (y : LegalPath R m s s) :
    (∀ B : {b : L // R (y.val j) b},
      Compatible M (detourLabels j y.val B.val) ↔ Compatible (capSurgery M j) y.val) ∧
    (∀ B : {b : L // R (y.val j) b},
      boundaryPotential q M (detourLabels j y.val B.val) * (q B.val / q (y.val j)) =
        (q B.val / q (y.val j)) ^ 2 * boundaryPotential q (capSurgery M j) y.val) := by
  exact ⟨fun B => close_compatible_iff M j hc y.val B.val,
    fun B => close_boundaryPotential M j hc q y.val B.val⟩
end Closed

section Nonclosed
variable {m : ℕ} (M : NCMatching (m + 2)) (j : Fin (m + 1))
  (hn : M.partner j.castSucc ≠ j.succ)

/-- The singleton is in the subtype of genuine R-neighbors. Its edge is the
surviving LegalPath edge at capU, reversed using the explicit symmetry premise. -/
theorem nonclose_legal_fiber {L : Type*} [Fintype L] [DecidableEq L]
    (R : L → L → Prop) (hR : Symmetric R) (s : L) (y : LegalPath R m s s) :
    Compatible (capSurgery M j) y.val ↔
      ∃! B : {b : L // R (y.val j) b}, Compatible M (detourLabels j y.val B.val) := by
  constructor
  · intro hy
    have hA := cap_outer_label M j hn y.val hy
    let B₀ : {b : L // R (y.val j) b} :=
      ⟨y.val (capU M j hn).castSucc, by
        rw [hA]
        exact hR (y.property.2.2 (capU M j hn))⟩
    refine ⟨B₀, (nonclose_compatible_iff M j hn y.val B₀.val).mpr ⟨hy, rfl⟩, ?_⟩
    intro B hB
    apply Subtype.ext
    exact ((nonclose_compatible_iff M j hn y.val B.val).mp hB).2
  · rintro ⟨B, hB, _⟩
    exact ((nonclose_compatible_iff M j hn y.val B.val).mp hB).1
end Nonclosed
end CupCapBridgeProposal
