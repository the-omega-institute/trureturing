/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripInjection
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripInjection
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.finite_certificate
   digest: The one-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229590Strip.result)
base_injections: proof_shape=bind-only; consumers=injection_powers
new_recurrence: proof_shape=bind-only; consumers=injection_powers
injection_powers: proof_shape=bind-only; consumers=HardinA229590StripPowers.powers_table
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData

/-! Exact five-row one-defect class transfers and suffix counts. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripInjection
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix (scalarRelationShift)
open HardinA229590StripData
set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 0 in
private theorem base_injections (k : Fin 12) :
    R.mulVec (W k) = RU ⟨k.val, by omega⟩ := by
  fin_cases k <;> exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem new_recurrence (k : Fin 6) :
    RU ⟨k.val+12, by omega⟩ = ∑ j : Fin 7,
      coefficients j • RU ⟨k.val+5+j.val, by omega⟩ := by
  fin_cases k <;> exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
theorem injection_powers (k : Fin 18) :
    R.mulVec ((Q ^ k.val).mulVec (1 : Fin 41 → ℤ)) = RU k := by
  suffices all : ∀ n (hn : n < 18),
      R.mulVec ((Q ^ n).mulVec (1 : Fin 41 → ℤ)) = RU ⟨n, hn⟩ from all k.val k.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hl : n < 12
    · rw [powers_table (⟨n, hl⟩ : Fin 12)]
      exact base_injections ⟨n, hl⟩
    · funext i
      have h := scalarRelationShift Q (R i) 7 4 coefficients power_polynomial (n-11)
      have he : n-11+4+7 = n := by omega
      rw [he] at h
      have ev (j : Fin 7) :
          dotProduct (R i) ((Q ^ (n-11+4+j.val)).mulVec (1 : Fin 41 → ℤ)) =
            RU ⟨n-7+j.val, by omega⟩ i := by
        have e : n-11+4+j.val = n-7+j.val := by omega
        rw [e]
        exact congrFun (ih (n-7+j.val) (by omega) (by omega)) i
      simp_rw [ev] at h
      have t := congrFun (new_recurrence (⟨n-12, by omega⟩ : Fin 6)) i
      have e (j : Fin 7) : n-12+5+j.val = n-7+j.val := by omega
      have e0 : n-12+12 = n := by omega
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e, e0] at t
      exact h.trans t.symm

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripInjection
