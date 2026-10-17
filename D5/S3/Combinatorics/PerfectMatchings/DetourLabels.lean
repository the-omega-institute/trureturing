/- UNCOMPILED source proposal. Literal detours on the supplier's LegalPath. -/
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
    simp only [skipPair, insertPort, Fin.val_castSucc, Fin.val_mk] at *
    split_ifs at hs <;> omega
  · exfalso
    simp only [Fin.val_castSucc] at *
    split_ifs at hs <;> omega
  · apply congrArg y
    apply Fin.ext
    simp only [skipPair, insertPort, Fin.val_castSucc, Fin.val_mk] at *
    split_ifs at hs <;> omega

theorem detour_skip_right (k : Fin m) :
    detourLabels j y B (skipPair j k).succ = y k.succ := by
  have hs : (skipPair j k).val = if k.val < j.val then k.val else k.val + 2 := rfl
  unfold detourLabels
  split_ifs with h₀ h₁
  · apply congrArg y
    apply Fin.ext
    simp only [skipPair, insertPort, Fin.val_succ, Fin.val_mk] at *
    split_ifs at hs <;> omega
  · exfalso
    simp only [Fin.val_succ] at *
    split_ifs at hs <;> omega
  · apply congrArg y
    apply Fin.ext
    simp only [skipPair, insertPort, Fin.val_succ, Fin.val_mk] at *
    split_ifs at hs <;> omega

end Labels

end CupCapBridgeProposal
