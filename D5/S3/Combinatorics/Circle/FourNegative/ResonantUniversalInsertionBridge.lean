/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionBridge
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Universal resonant source-to-target physical word bridge. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionInventory

/-! # Universal physical target bridge -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport

theorem resonant_target_word_endpoint_of_source {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell ≤ k)
    (word : List (Fin (k + 1))) (hsource : resonantSourceWord k w word)
    (orientation : Fin ell → Bool) :
    (resonantLiftWord word orientation).Perm (List.finRange (k + ell + 1)) ∧
      ((resonantLiftWord word orientation).map (resonantTargetFirst k ell w)).sum = 0 ∧
      ((resonantLiftWord word orientation).map (resonantTargetSecond k ell w)).sum = 0 := by
  obtain ⟨_, hk, hwpos, _, hroom⟩ := resonant_hypotheses_facts hw hell hm hdiv hlarge hkl
  have hcharge := resonant_charge_total hk hroom
  have hear := resonant_ear_total k
  have hlow := resonant_low_weight_total hm hkl
  have hchargeWord : (word.map (resonantCharge k w)).sum = (w : ℤ) := by
    rw [(hsource.1.map _).sum_eq, hcharge]
  have hearWord : (word.map (resonantEar k)).sum = 1 := by
    rw [(hsource.1.map _).sum_eq, hear]
  have hlowWord : (word.map (resonantLowWeight (ell := ell))).sum = (m : ℤ) - 1 := by
    rw [(hsource.1.map _).sum_eq, hlow]
  have hfirst : resonantFirstState k ell w m word = 0 := by
    simp only [resonantFirstState]
    rw [hsource.2.1, hchargeWord, hlowWord]
    norm_num [Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  have hsecond : resonantSecondState k ell w m word = 0 := by
    simp only [resonantSecondState]
    rw [hsource.2.2.1, hchargeWord, hearWord, hlowWord]
    norm_num [Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  refine ⟨resonant_inventory hkl word hsource.1 orientation, ?_, ?_⟩
  · rw [(resonant_liftWord_states hw hell hm hdiv hlarge hkl word orientation).1, hfirst]
  · rw [(resonant_liftWord_states hw hell hm hdiv hlarge hkl word orientation).2, hsecond]

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
