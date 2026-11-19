/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripPowers
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripPowers
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.finite_certificate
   digest: The two-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31594; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229698Strip.result)
one_steps: proof_shape=bind-only; consumers=powers_table
powers_table: proof_shape=bind-only; consumers=power_polynomial
power_polynomial: proof_shape=bind-only; consumers=HardinA229698Strip.result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripInjection
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup0
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup1
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup2
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup3
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripStepGroup5

/-! Exact three-colour counts on five-row HA strips with two defects. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripPowers
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590
open HardinA229698StripData
open HardinA229698StripTables

set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 0 in
private theorem one_steps (k : Fin 27) :
    V k.succ = Q.mulVec (V k.castSucc) + J k := by
  fin_cases k
  · exact HardinA229698StripStepGroup0.steps 0
  · exact HardinA229698StripStepGroup0.steps 1
  · exact HardinA229698StripStepGroup0.steps 2
  · exact HardinA229698StripStepGroup0.steps 3
  · exact HardinA229698StripStepGroup0.steps 4
  · exact HardinA229698StripStepGroup1.steps 0
  · exact HardinA229698StripStepGroup1.steps 1
  · exact HardinA229698StripStepGroup1.steps 2
  · exact HardinA229698StripStepGroup1.steps 3
  · exact HardinA229698StripStepGroup1.steps 4
  · exact HardinA229698StripStepGroup2.steps 0
  · exact HardinA229698StripStepGroup2.steps 1
  · exact HardinA229698StripStepGroup2.steps 2
  · exact HardinA229698StripStepGroup2.steps 3
  · exact HardinA229698StripStepGroup2.steps 4
  · exact HardinA229698StripStepGroup3.steps 0
  · exact HardinA229698StripStepGroup3.steps 1
  · exact HardinA229698StripStepGroup3.steps 2
  · exact HardinA229698StripStepGroup3.steps 3
  · exact HardinA229698StripStepGroup3.steps 4
  · exact HardinA229698StripStepGroup4.steps 0
  · exact HardinA229698StripStepGroup4.steps 1
  · exact HardinA229698StripStepGroup4.steps 2
  · exact HardinA229698StripStepGroup4.steps 3
  · exact HardinA229698StripStepGroup4.steps 4
  · exact HardinA229698StripStepGroup5.steps 0
  · exact HardinA229698StripStepGroup5.steps 1

set_option maxHeartbeats 0 in
theorem powers_table (k : Fin 28) :
    (T ^ k.val).mulVec terminal =
      Sum.elim (V k) ((HardinA229590StripData.T ^ k.val).mulVec HardinA229590StripData.terminal) := by
  induction k using Fin.induction with
  | zero =>
    simp only [Fin.val_zero, pow_zero, Matrix.one_mulVec]
    ext (i | i)
    · fin_cases i <;> rfl
    · rfl
  | succ k ih =>
    simp only [Fin.val_castSucc] at ih
    rw [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec, ih,
      T, Matrix.fromBlocks_mulVec]
    simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.zero_mulVec, zero_add]
    rw [HardinA229698StripInjection.injection_powers k, ← one_steps k]
    congr 1
    rw [pow_succ', ← Matrix.mulVec_mulVec]

set_option maxHeartbeats 0 in
theorem power_polynomial : (T ^ (6+21)).mulVec terminal =
    ∑ j : Fin 21, coefficients j • (T ^ (6+j.val)).mulVec terminal := by
  have tab (j : Fin 21) : (T ^ (6+j.val)).mulVec terminal =
      Sum.elim (V ⟨6+j.val, by omega⟩)
        ((HardinA229590StripData.T ^ (6+j.val)).mulVec HardinA229590StripData.terminal) :=
    powers_table ⟨6+j.val, by omega⟩
  rw [show 6+21 = (27 : Fin 28).val from rfl, powers_table]
  simp_rw [tab]
  ext (i | i)
  · change V 27 i = _
    simp only [Finset.sum_apply, Pi.smul_apply, Sum.elim_inl, smul_eq_mul]
    have h : V 27 = ∑ j : Fin 21, coefficients j • V ⟨6+j.val, by omega⟩ :=
      List.ofFn_inj.mp rfl
    exact congrFun h i
  · change (HardinA229590StripData.T ^ 27).mulVec HardinA229590StripData.terminal i = _
    simp only [Finset.sum_apply, Pi.smul_apply, Sum.elim_inr, smul_eq_mul]
    have shift (m : ℕ) := congrArg (fun w =>
      ((HardinA229590StripData.T ^ m).mulVec w) i)
        HardinA229590StripPowers.power_polynomial
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      ← pow_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at shift
    have h0 := shift 2
    have h1 := shift 3
    have h2 := shift 4
    have h3 := shift 5
    have h4 := shift 6
    have h5 := shift 7
    have h6 := shift 8
    have h7 := shift 9
    norm_num only [HardinA229698StripData.coefficients, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ,
      Fin.val_one, Nat.reduceAdd] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
    linear_combination h7 - (-8) * h0 - (48) * h1 - (-84) * h2 - (17) * h3 - (76) * h4 - (-64) * h5 - (16) * h6

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripPowers
