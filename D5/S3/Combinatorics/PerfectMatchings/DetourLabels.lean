/- GID: D5/S3/Combinatorics/PerfectMatchings/DetourLabels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/DetourLabels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Insertion of an adjacent labelled detour. -/
import D5.S3.Combinatorics.PerfectMatchings.AdjacentCapSurgery

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CupCapBridgeProposal

section Labels
variable {L : Type*} {m : ℕ} (j : Fin (m + 1))
  (y : Fin (m + 1) → L) (B : L)

theorem detour_left_consumed :
    detourLabels j y B j.castSucc.castSucc = y j := by
  simp only [detourLabels, Fin.val_castSucc, le_refl, dite_true]

theorem detour_middle_consumed :
    detourLabels j y B j.castSucc.succ = B := by
  simp [detourLabels]

theorem detour_middle_consumed' :
    detourLabels j y B j.succ.castSucc = B := by
  simp [detourLabels]

theorem detour_right_consumed :
    detourLabels j y B j.succ.succ = y j := by
  unfold detourLabels
  split_ifs with h₀ h₁
  · simp only [Fin.val_succ] at h₀
    omega
  · simp only [Fin.val_succ] at h₁
    omega
  · apply congrArg y
    apply Fin.ext
    simp only [Fin.val_mk, Fin.val_succ]
    omega

/-- Both sides of every surviving endpoint are literally unchanged. -/
theorem detour_skip_left (k : Fin m) :
    detourLabels j y B (skipPair j k).castSucc = y k.castSucc := by
  have hs : (skipPair j k).val = if k.val < j.val then k.val else k.val + 2 := rfl
  unfold detourLabels
  split_ifs with h₀ h₁
  · apply congrArg y
    apply Fin.ext
    change (skipPair j k).val = k.val
    change (skipPair j k).val ≤ j.val at h₀
    rw [hs] at h₀ ⊢
    split_ifs at * <;> omega
  · exfalso
    change (skipPair j k).val = j.val + 1 at h₁
    rw [hs] at h₁
    split_ifs at h₁ <;> omega
  · apply congrArg y
    apply Fin.ext
    change (skipPair j k).val - 2 = k.val
    change ¬ (skipPair j k).val ≤ j.val at h₀
    rw [hs] at h₀ ⊢
    split_ifs at * <;> omega

theorem detour_skip_right (k : Fin m) :
    detourLabels j y B (skipPair j k).succ = y k.succ := by
  have hs : (skipPair j k).val = if k.val < j.val then k.val else k.val + 2 := rfl
  unfold detourLabels
  split_ifs with h₀ h₁
  · apply congrArg y
    apply Fin.ext
    change (skipPair j k).val + 1 = k.val + 1
    change (skipPair j k).val + 1 ≤ j.val at h₀
    rw [hs] at h₀ ⊢
    split_ifs at * <;> omega
  · exfalso
    change (skipPair j k).val + 1 = j.val + 1 at h₁
    rw [hs] at h₁
    split_ifs at h₁ <;> omega
  · apply congrArg y
    apply Fin.ext
    change (skipPair j k).val + 1 - 2 = k.val + 1
    change ¬ (skipPair j k).val + 1 ≤ j.val at h₀
    rw [hs] at h₀ ⊢
    split_ifs at * <;> omega

end Labels

end CupCapBridgeProposal
