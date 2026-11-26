/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripInjection
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripInjection
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.finite_certificate
   digest: The two-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31594; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229698Strip.result)
base_injections: proof_shape=bind-only; consumers=two_injection_powers
new_recurrence: proof_shape=bind-only; consumers=two_injection_powers
two_injection_powers: proof_shape=bind-only; consumers=injection_powers
base_old_injections: proof_shape=bind-only; consumers=injection_powers
old_recurrence: proof_shape=bind-only; consumers=injection_powers
injection_powers: proof_shape=bind-only; consumers=HardinA229698StripPowers.powers_table
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTwoInjectionGroup3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripOneInjectionGroup0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripOneInjectionGroup1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripOneInjectionGroup2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripOneInjectionGroup3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripOneInjectionGroup4

/-! Exact three-colour counts on five-row HA strips with two defects. -/



open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripInjection
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590
open HardinA229698StripData
open HardinA229698StripTables
open D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix (scalarRelationShift)

set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 0 in
private theorem base_injections (k : Fin 12) :
    S.mulVec (W k) = SQ ⟨k.val, by omega⟩ := by
  fin_cases k
  · exact HardinA229698StripTwoInjectionGroup0.rows 0
  · exact HardinA229698StripTwoInjectionGroup0.rows 1
  · exact HardinA229698StripTwoInjectionGroup0.rows 2
  · exact HardinA229698StripTwoInjectionGroup1.rows 0
  · exact HardinA229698StripTwoInjectionGroup1.rows 1
  · exact HardinA229698StripTwoInjectionGroup1.rows 2
  · exact HardinA229698StripTwoInjectionGroup2.rows 0
  · exact HardinA229698StripTwoInjectionGroup2.rows 1
  · exact HardinA229698StripTwoInjectionGroup2.rows 2
  · exact HardinA229698StripTwoInjectionGroup3.rows 0
  · exact HardinA229698StripTwoInjectionGroup3.rows 1
  · exact HardinA229698StripTwoInjectionGroup3.rows 2

set_option maxHeartbeats 0 in
private theorem new_recurrence (k : Fin 7) :
    SQ ⟨k.val+12, by omega⟩ = ∑ j : Fin 7,
      D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.coefficients j •
        SQ ⟨k.val+5+j.val, by omega⟩ := by
  fin_cases k <;> exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
theorem two_injection_powers (k : Fin 19) :
    S.mulVec ((Q ^ k.val).mulVec (1 : Fin 41 → ℤ)) = SQ k := by
  suffices all : ∀ n (hn : n < 19),
      S.mulVec ((Q ^ n).mulVec (1 : Fin 41 → ℤ)) = SQ ⟨n, hn⟩ from all k.val k.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hl : n < 12
    · rw [powers_table (⟨n, hl⟩ : Fin 12)]
      exact base_injections ⟨n, hl⟩
    · funext i
      have h := scalarRelationShift Q (S i) 7 4
        D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.coefficients
        power_polynomial (n-11)
      have he : n-11+4+7 = n := by omega
      rw [he] at h
      have ev (j : Fin 7) :
          dotProduct (S i) ((Q ^ (n-11+4+j.val)).mulVec (1 : Fin 41 → ℤ)) =
            SQ ⟨n-7+j.val, by omega⟩ i := by
        have e : n-11+4+j.val = n-7+j.val := by omega
        rw [e]
        exact congrFun (ih (n-7+j.val) (by omega) (by omega)) i
      simp_rw [ev] at h
      have t := congrFun (new_recurrence (⟨n-12, by omega⟩ : Fin 7)) i
      have e (j : Fin 7) : n-12+5+j.val = n-7+j.val := by omega
      have e0 : n-12+12 = n := by omega
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e, e0] at t
      exact h.trans t.symm

set_option maxHeartbeats 0 in
private theorem base_old_injections (k : Fin 19) :
    HardinA229590StripData.R.mulVec (HardinA229590StripData.U k) + SQ k =
      J ⟨k.val, by omega⟩ := by
  fin_cases k
  · exact HardinA229698StripOneInjectionGroup0.rows 0
  · exact HardinA229698StripOneInjectionGroup0.rows 1
  · exact HardinA229698StripOneInjectionGroup0.rows 2
  · exact HardinA229698StripOneInjectionGroup0.rows 3
  · exact HardinA229698StripOneInjectionGroup1.rows 0
  · exact HardinA229698StripOneInjectionGroup1.rows 1
  · exact HardinA229698StripOneInjectionGroup1.rows 2
  · exact HardinA229698StripOneInjectionGroup1.rows 3
  · exact HardinA229698StripOneInjectionGroup2.rows 0
  · exact HardinA229698StripOneInjectionGroup2.rows 1
  · exact HardinA229698StripOneInjectionGroup2.rows 2
  · exact HardinA229698StripOneInjectionGroup2.rows 3
  · exact HardinA229698StripOneInjectionGroup3.rows 0
  · exact HardinA229698StripOneInjectionGroup3.rows 1
  · exact HardinA229698StripOneInjectionGroup3.rows 2
  · exact HardinA229698StripOneInjectionGroup3.rows 3
  · exact HardinA229698StripOneInjectionGroup4.rows 0
  · exact HardinA229698StripOneInjectionGroup4.rows 1
  · exact HardinA229698StripOneInjectionGroup4.rows 2

set_option maxHeartbeats 0 in
private theorem old_recurrence (k : Fin 8) :
    J ⟨k.val+19, by omega⟩ = ∑ j : Fin 14,
      (![-64,768,-3648,8336,-7472,-5464,18879,-14888,-816,9016,-6494,2200,-384,32] j : ℤ) •
        J ⟨k.val+5+j.val, by omega⟩ := by
  fin_cases k <;> exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
theorem injection_powers (k : Fin 27) :
    B.mulVec ((HardinA229590StripData.T ^ k.val).mulVec HardinA229590StripData.terminal) = J k := by
  suffices all : ∀ n (hn : n < 27),
      B.mulVec ((HardinA229590StripData.T ^ n).mulVec HardinA229590StripData.terminal) = J ⟨n, hn⟩
      from all k.val k.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hl : n < 19
    · rw [HardinA229590StripPowers.powers_table (⟨n,hl⟩ : Fin 19)]
      have split (u v : Fin 41 → ℤ) :
          B.mulVec (Sum.elim u v) = HardinA229590StripData.R.mulVec u + S.mulVec v := by
        funext i
        simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, B,
          Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
      rw [split, two_injection_powers (⟨n,hl⟩ : Fin 19)]
      exact base_old_injections ⟨n,hl⟩
    · funext i
      have h := congrArg (fun w => dotProduct (B i)
        ((HardinA229590StripData.T ^ (n-18)).mulVec w))
          HardinA229590StripPowers.power_polynomial
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        ← pow_add, dotProduct_sum, dotProduct_smul, smul_eq_mul, ← Nat.add_assoc] at h
      have he : n-18+4+14 = n := by omega
      rw [he] at h
      have ev (j : Fin 14) :
          dotProduct (B i) ((HardinA229590StripData.T ^ (n-18+4+j.val)).mulVec
            HardinA229590StripData.terminal) = J ⟨n-14+j.val, by omega⟩ i := by
        have e : n-18+4+j.val = n-14+j.val := by omega
        rw [e]
        exact congrFun (ih (n-14+j.val) (by omega) (by omega)) i
      simp_rw [ev] at h
      have t := congrFun (old_recurrence (⟨n-19, by omega⟩ : Fin 8)) i
      have e (j : Fin 14) : n-19+5+j.val = n-14+j.val := by omega
      have e0 : n-19+19 = n := by omega
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e, e0] at t
      exact h.trans t.symm

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripInjection
