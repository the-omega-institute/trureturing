/- GID: D5/S3/Combinatorics/PerfectMatchings/NonclosedCapLabels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/NonclosedCapLabels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Basic]
   utility: none
   digest: The unique middle label of a reconnected cap. -/
import D5.S3.Combinatorics.PerfectMatchings.ClosedCapFiber

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CupCapBridgeProposal

section ReconnectCompatibility
variable {L : Type*} {m : ℕ} (M : NCMatching (m + 2))
  (j : Fin (m + 1)) (y : Fin (m + 1) → L) (B : L)

/-- Deleting a compatible detour yields the compatibility of the actual surgery. -/
theorem compatible_reconnected (hx : Compatible M (detourLabels j y B)) :
    Compatible (capSurgery M j) y := by
  let x := detourLabels j y B
  have ha := hx j.castSucc
  have hb := hx j.succ
  change x j.castSucc.castSucc = x (M.partner j.castSucc).succ ∧
    x j.castSucc.succ = x (M.partner j.castSucc).castSucc at ha
  change x j.succ.castSucc = x (M.partner j.succ).succ ∧
    x j.succ.succ = x (M.partner j.succ).castSucc at hb
  have hmid : x j.castSucc.succ = x j.succ.castSucc := by
    simp only [x, detour_middle_consumed, detour_middle_consumed']
  have hout : x j.castSucc.castSucc = x j.succ.succ := by
    simp only [x, detour_left_consumed, detour_right_consumed]
  intro k
  have hk := hx (skipPair j k)
  by_cases hpa : M.partner (skipPair j k) = j.castSucc
  · rw [hpa] at hk
    have hp : skipPair j ((capSurgery M j).partner k) = M.partner j.succ := by
      rw [capSurgery_reconnect]
      simp only [reconnectPartner, hpa, if_true]
    have he : x (skipPair j k).castSucc =
          x (skipPair j ((capSurgery M j).partner k)).succ ∧
        x (skipPair j k).succ =
          x (skipPair j ((capSurgery M j).partner k)).castSucc := by
      rw [hp]
      exact ⟨hk.1.trans (hmid.trans hb.1), hk.2.trans (hout.trans hb.2)⟩
    simpa only [x, detour_skip_left, detour_skip_right] using he
  by_cases hpb : M.partner (skipPair j k) = j.succ
  · rw [hpb] at hk
    have hp : skipPair j ((capSurgery M j).partner k) = M.partner j.castSucc := by
      rw [capSurgery_reconnect]
      have hba : j.succ ≠ j.castSucc := by
        intro h
        have hval : j.val + 1 = j.val := congrArg Fin.val h
        omega
      simp only [reconnectPartner, hpb, hba, if_false, if_true]
    have he : x (skipPair j k).castSucc =
          x (skipPair j ((capSurgery M j).partner k)).succ ∧
        x (skipPair j k).succ =
          x (skipPair j ((capSurgery M j).partner k)).castSucc := by
      rw [hp]
      exact ⟨hk.1.trans (hout.symm.trans ha.1), hk.2.trans (hmid.symm.trans ha.2)⟩
    simpa only [x, detour_skip_left, detour_skip_right] using he
  · have hp : skipPair j ((capSurgery M j).partner k) = M.partner (skipPair j k) := by
      rw [capSurgery_reconnect]
      simp only [reconnectPartner, hpa, hpb, if_false]
    rw [← hp] at hk
    simpa only [detour_skip_left, detour_skip_right] using hk

/-- The reverse transport pays the two consumed arcs locally; all other arcs
are the shorter compatibility equations, explicitly transported through skipPair. -/
theorem compatible_of_reconnected
    (hy : Compatible (capSurgery M j) y)
    (ha : detourLabels j y B j.castSucc.castSucc =
        detourLabels j y B (M.partner j.castSucc).succ ∧
      detourLabels j y B j.castSucc.succ =
        detourLabels j y B (M.partner j.castSucc).castSucc)
    (hb : detourLabels j y B j.succ.castSucc =
        detourLabels j y B (M.partner j.succ).succ ∧
      detourLabels j y B j.succ.succ =
        detourLabels j y B (M.partner j.succ).castSucc) :
    Compatible M (detourLabels j y B) := by
  intro t
  by_cases hta : t = j.castSucc
  · subst t; exact ha
  by_cases htb : t = j.succ
  · subst t; exact hb
  by_cases hpa : M.partner t = j.castSucc
  · have htu : t = M.partner j.castSucc := by
      exact (M.involutive t).symm.trans (congrArg M.partner hpa)
    rw [hpa, htu]
    exact ⟨ha.2.symm, ha.1.symm⟩
  by_cases hpb : M.partner t = j.succ
  · have htv : t = M.partner j.succ := by
      exact (M.involutive t).symm.trans (congrArg M.partner hpb)
    rw [hpb, htv]
    exact ⟨hb.2.symm, hb.1.symm⟩
  let k := unskipPair j t hta htb
  have hk : skipPair j k = t := skipPair_unskipPair j t hta htb
  have hp : skipPair j ((capSurgery M j).partner k) = M.partner t := by
    rw [capSurgery_reconnect, hk]
    simp only [reconnectPartner, hpa, hpb, if_false]
  rw [← hp, ← hk]
  simpa only [detour_skip_left, detour_skip_right] using hy k
end ReconnectCompatibility

section Nonclosed
variable {m : ℕ} (M : NCMatching (m + 2)) (j : Fin (m + 1))
  (hn : M.partner j.castSucc ≠ j.succ)

include hn

theorem capU_survives :
    M.partner j.castSucc ≠ j.castSucc ∧ M.partner j.castSucc ≠ j.succ :=
  ⟨M.noFixed _, hn⟩

theorem capV_survives :
    M.partner j.succ ≠ j.castSucc ∧ M.partner j.succ ≠ j.succ := by
  refine ⟨?_, M.noFixed _⟩
  intro h
  apply hn
  exact (congrArg M.partner h).symm.trans (M.involutive j.succ)

/-- The two actual surviving partners, in shorter coordinates. -/
def capU : Fin m := unskipPair j (M.partner j.castSucc)
  (capU_survives M j hn).1 (capU_survives M j hn).2

def capV : Fin m := unskipPair j (M.partner j.succ)
  (capV_survives M j hn).1 (capV_survives M j hn).2

theorem skip_capU : skipPair j (capU M j hn) = M.partner j.castSucc :=
  skipPair_unskipPair j _ _ _

theorem skip_capV : skipPair j (capV M j hn) = M.partner j.succ :=
  skipPair_unskipPair j _ _ _

theorem capSurgery_partner_U :
    (capSurgery M j).partner (capU M j hn) = capV M j hn := by
  apply skipPair_injective j
  rw [capSurgery_reconnect, skip_capU, skip_capV]
  simp only [reconnectPartner, M.involutive j.castSucc, if_true]

theorem capSurgery_partner_V :
    (capSurgery M j).partner (capV M j hn) = capU M j hn := by
  have h := (capSurgery M j).involutive (capU M j hn)
  rw [capSurgery_partner_U] at h
  exact h

/-- The untouched interval inside the old u-a arc, when u is on the left. -/
theorem cap_interval_before (hu : M.partner j.castSucc < j.castSucc) :
    (capSurgery M j).IntervalClosed (capU M j hn).succ j := by
  have huval : (capU M j hn).val = (M.partner j.castSucc).val := by
    unfold capU unskipPair
    simp only [Fin.lt_def, Fin.val_castSucc] at hu
    simp only [Fin.val_mk, if_pos hu]
  intro t hlow hhigh
  change (capU M j hn).val + 1 ≤ t.val at hlow
  change t.val < j.val at hhigh
  have htv : (skipPair j t).val = t.val := by
    simp only [skipPair, insertPort, if_pos hhigh, Fin.val_mk]
  have hi := M.interior_closed (M.partner j.castSucc) (skipPair j t)
    (by change (M.partner j.castSucc).val < (skipPair j t).val
        rw [← huval]
        omega)
    (by rw [M.involutive]; change (skipPair j t).val < j.val; omega)
  rw [M.involutive] at hi
  have hpa : M.partner (skipPair j t) ≠ j.castSucc := ne_of_lt hi.2
  have hpb : M.partner (skipPair j t) ≠ j.succ := by
    intro h; have hv := congrArg Fin.val h
    have hlt := hi.2
    change (M.partner (skipPair j t)).val < j.val at hlt
    simp only [Fin.val_succ] at hv
    omega
  have hp : skipPair j ((capSurgery M j).partner t) = M.partner (skipPair j t) := by
    rw [capSurgery_reconnect]
    simp only [reconnectPartner, hpa, hpb, if_false]
  have hpv := congrArg Fin.val hp
  change (M.partner j.castSucc).val < (M.partner (skipPair j t)).val ∧
    (M.partner (skipPair j t)).val < j.val at hi
  rw [← huval] at hi
  change (if ((capSurgery M j).partner t).val < j.val then
    ((capSurgery M j).partner t).val else ((capSurgery M j).partner t).val + 2) =
    (M.partner (skipPair j t)).val at hpv
  change (capU M j hn).val + 1 ≤ ((capSurgery M j).partner t).val ∧
    ((capSurgery M j).partner t).val < j.val
  split_ifs at hpv <;> omega

/-- The untouched interval inside the old b-v arc, when v is on the right. -/
theorem cap_interval_after (hv : j.succ < M.partner j.succ) :
    (capSurgery M j).IntervalClosed j (capV M j hn).castSucc := by
  have hvval : (capV M j hn).val + 2 = (M.partner j.succ).val := by
    unfold capV unskipPair
    have hnv : ¬ (M.partner j.succ).val < j.val := by
      change j.val + 1 < (M.partner j.succ).val at hv
      omega
    simp only [Fin.val_mk, if_neg hnv]
    change j.val + 1 < (M.partner j.succ).val at hv
    omega
  intro t hlow hhigh
  have htv : (skipPair j t).val = t.val + 2 := by
    simp only [skipPair, insertPort, if_neg (not_lt_of_ge hlow), Fin.val_mk]
  have hi := M.interior_closed j.succ (skipPair j t)
    (by change j.val + 1 < (skipPair j t).val; omega)
    (by change (skipPair j t).val < (M.partner j.succ).val
        simp only [Fin.val_castSucc] at hhigh; omega)
  have hpa : M.partner (skipPair j t) ≠ j.castSucc := by
    intro h
    have hv' := congrArg Fin.val h
    have hlt := hi.1
    change j.val + 1 < (M.partner (skipPair j t)).val at hlt
    simp only [Fin.val_castSucc] at hv'
    omega
  have hpb : M.partner (skipPair j t) ≠ j.succ := ne_of_gt hi.1
  have hp : skipPair j ((capSurgery M j).partner t) = M.partner (skipPair j t) := by
    rw [capSurgery_reconnect]
    simp only [reconnectPartner, hpa, hpb, if_false]
  have hpv := congrArg Fin.val hp
  simp only [Fin.lt_def, Fin.val_succ] at hi
  change (if ((capSurgery M j).partner t).val < j.val then
    ((capSurgery M j).partner t).val else ((capSurgery M j).partner t).val + 2) =
    (M.partner (skipPair j t)).val at hpv
  simp only [Fin.val_castSucc] at hhigh ⊢
  split_ifs at hpv <;> omega

/-- The missing distant-label equality: the gap at j equals the right side of u.
Its proof really consumes untouched interval equations through closed_interval_gap. -/
theorem cap_outer_label {L : Type*} (y : Fin (m + 1) → L)
    (hy : Compatible (capSurgery M j) y) : y j = y (capU M j hn).succ := by
  by_cases hu : M.partner j.castSucc < j.castSucc
  · have huv : (capU M j hn).val = (M.partner j.castSucc).val := by
      unfold capU unskipPair
      simp only [Fin.lt_def, Fin.val_castSucc] at hu
      simp only [Fin.val_mk, if_pos hu]
    have hle : (capU M j hn).succ ≤ j := by
      change (capU M j hn).val + 1 ≤ j.val
      change (M.partner j.castSucc).val < j.val at hu
      omega
    exact ((capSurgery M j).closed_interval_gap y hy _ _ hle
      (cap_interval_before M j hn hu)).symm
  · have hv : j.succ < M.partner j.succ := by
      have hcases := cap_order_cases M j
      rcases hcases with hclose | hcases
      · exact False.elim (hn hclose)
      rcases hcases with hsib | hcases
      · exact False.elim (hu hsib.1)
      rcases hcases with hleft | hright
      · exact hleft.1
      · exact False.elim (hu hright.2)
    have hle : j ≤ (capV M j hn).castSucc := by
      have hvv := skip_capV M j hn
      have hvval := congrArg Fin.val hvv
      change (if (capV M j hn).val < j.val then (capV M j hn).val
        else (capV M j hn).val + 2) = (M.partner j.succ).val at hvval
      change j.val + 1 < (M.partner j.succ).val at hv
      change j.val ≤ (capV M j hn).val
      split_ifs at hvval <;> omega
    have hgap := (capSurgery M j).closed_interval_gap y hy _ _ hle
      (cap_interval_after M j hn hv)
    have hp := (hy (capU M j hn)).2
    rw [capSurgery_partner_U] at hp
    exact hgap.trans hp.symm

/-- All three nonclose cases have one common exact fiber formula. The forced
label is the *left side of u* in shorter coordinates; the distant right-side
identity is supplied by cap_outer_label, not by the new pair alone. -/
theorem nonclose_compatible_iff {L : Type*} (y : Fin (m + 1) → L) (B : L) :
    Compatible M (detourLabels j y B) ↔
      Compatible (capSurgery M j) y ∧ B = y (capU M j hn).castSucc := by
  constructor
  · intro hx
    refine ⟨compatible_reconnected M j y B hx, ?_⟩
    have h := (hx j.castSucc).2
    rw [← skip_capU M j hn] at h
    simpa only [detour_middle_consumed, detour_skip_left] using h
  · rintro ⟨hy, hB⟩
    have hA := cap_outer_label M j hn y hy
    have hp := hy (capU M j hn)
    rw [capSurgery_partner_U] at hp
    apply compatible_of_reconnected M j y B hy
    · rw [← skip_capU M j hn]
      simpa only [detour_left_consumed, detour_middle_consumed,
        detour_skip_left, detour_skip_right] using And.intro hA hB
    · rw [← skip_capV M j hn]
      simpa only [detour_middle_consumed', detour_right_consumed,
        detour_skip_left, detour_skip_right] using
        And.intro (hB.trans hp.1) (hA.trans hp.2)

end Nonclosed
end CupCapBridgeProposal
