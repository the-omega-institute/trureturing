/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripPowers
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripPowers
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.finite_certificate
   digest: The one-defect extension of the five-row HA quotient. -/

/-
admission_basis: open-problem-resolution (#31329; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229590Strip.result)
step0: proof_shape=bind-only; consumers=one_steps
step1: proof_shape=bind-only; consumers=one_steps
step2: proof_shape=bind-only; consumers=one_steps
step3: proof_shape=bind-only; consumers=one_steps
step4: proof_shape=bind-only; consumers=one_steps
step5: proof_shape=bind-only; consumers=one_steps
step6: proof_shape=bind-only; consumers=one_steps
step7: proof_shape=bind-only; consumers=one_steps
step8: proof_shape=bind-only; consumers=one_steps
step9: proof_shape=bind-only; consumers=one_steps
step10: proof_shape=bind-only; consumers=one_steps
step11: proof_shape=bind-only; consumers=one_steps
step12: proof_shape=bind-only; consumers=one_steps
step13: proof_shape=bind-only; consumers=one_steps
step14: proof_shape=bind-only; consumers=one_steps
step15: proof_shape=bind-only; consumers=one_steps
step16: proof_shape=bind-only; consumers=one_steps
step17: proof_shape=bind-only; consumers=one_steps
one_steps: proof_shape=bind-only; consumers=powers_table
powers_table: proof_shape=bind-only; consumers=power_polynomial
power_polynomial: proof_shape=bind-only; consumers=HardinA229590Strip.result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripInjection
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripCut

/-! Exact five-row one-defect class transfers and suffix counts. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix (scalarRelationShift)
open HardinA229590StripData
set_option maxRecDepth 100000
set_option Elab.async false

set_option maxHeartbeats 0 in
private theorem step0 : U 1 = Q.mulVec (U 0) + RU 0 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step1 : U 2 = Q.mulVec (U 1) + RU 1 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step2 : U 3 = Q.mulVec (U 2) + RU 2 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step3 : U 4 = Q.mulVec (U 3) + RU 3 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step4 : U 5 = Q.mulVec (U 4) + RU 4 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step5 : U 6 = Q.mulVec (U 5) + RU 5 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step6 : U 7 = Q.mulVec (U 6) + RU 6 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step7 : U 8 = Q.mulVec (U 7) + RU 7 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step8 : U 9 = Q.mulVec (U 8) + RU 8 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step9 : U 10 = Q.mulVec (U 9) + RU 9 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step10 : U 11 = Q.mulVec (U 10) + RU 10 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step11 : U 12 = Q.mulVec (U 11) + RU 11 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step12 : U 13 = Q.mulVec (U 12) + RU 12 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step13 : U 14 = Q.mulVec (U 13) + RU 13 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step14 : U 15 = Q.mulVec (U 14) + RU 14 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step15 : U 16 = Q.mulVec (U 15) + RU 15 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step16 : U 17 = Q.mulVec (U 16) + RU 16 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem step17 : U 18 = Q.mulVec (U 17) + RU 17 := by
  exact List.ofFn_inj.mp rfl

set_option maxHeartbeats 0 in
private theorem one_steps (k : Fin 18) :
    U k.succ = Q.mulVec (U k.castSucc) + RU k := by
  fin_cases k
  · exact step0
  · exact step1
  · exact step2
  · exact step3
  · exact step4
  · exact step5
  · exact step6
  · exact step7
  · exact step8
  · exact step9
  · exact step10
  · exact step11
  · exact step12
  · exact step13
  · exact step14
  · exact step15
  · exact step16
  · exact step17


set_option maxHeartbeats 0 in
theorem powers_table (k : Fin 19) :
    (T ^ k.val).mulVec terminal =
      Sum.elim (U k) ((Q ^ k.val).mulVec (1 : Fin 41 → ℤ)) := by
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
    rw [HardinA229590StripInjection.injection_powers k, ← one_steps k]
    congr 1
    rw [pow_succ', ← Matrix.mulVec_mulVec]

set_option maxHeartbeats 0 in
theorem power_polynomial : (T ^ (4+14)).mulVec terminal =
    ∑ j : Fin 14, (![-64,768,-3648,8336,-7472,-5464,18879,-14888,-816,9016,-6494,2200,-384,32] j : ℤ) • (T ^ (4+j.val)).mulVec terminal := by
  have tab (j : Fin 14) : (T ^ (4+j.val)).mulVec terminal =
      Sum.elim (U ⟨4+j.val, by omega⟩) ((Q ^ (4+j.val)).mulVec (1 : Fin 41 → ℤ)) :=
    powers_table ⟨4+j.val, by omega⟩
  rw [show 4+14 = (18 : Fin 19).val from rfl, powers_table]
  simp_rw [tab]
  ext (i | i)
  · change U 18 i = _
    simp only [Finset.sum_apply, Pi.smul_apply, Sum.elim_inl, smul_eq_mul]
    have h : U 18 = ∑ j : Fin 14, (![-64,768,-3648,8336,-7472,-5464,18879,-14888,-816,9016,-6494,2200,-384,32] j : ℤ) • U ⟨4+j.val, by omega⟩ :=
      List.ofFn_inj.mp rfl
    exact congrFun h i
  · change (Q ^ 18).mulVec (1 : Fin 41 → ℤ) i = _
    simp only [Finset.sum_apply, Pi.smul_apply, Sum.elim_inr, smul_eq_mul]
    have h0 := scalarRelationShift Q (Pi.single i 1) 7 4 coefficients D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.power_polynomial 0
    have h1 := scalarRelationShift Q (Pi.single i 1) 7 4 coefficients D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.power_polynomial 1
    have h2 := scalarRelationShift Q (Pi.single i 1) 7 4 coefficients D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.power_polynomial 2
    have h3 := scalarRelationShift Q (Pi.single i 1) 7 4 coefficients D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.power_polynomial 3
    have h4 := scalarRelationShift Q (Pi.single i 1) 7 4 coefficients D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.power_polynomial 4
    have h5 := scalarRelationShift Q (Pi.single i 1) 7 4 coefficients D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.power_polynomial 5
    have h6 := scalarRelationShift Q (Pi.single i 1) 7 4 coefficients D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.power_polynomial 6
    have h7 := scalarRelationShift Q (Pi.single i 1) 7 4 coefficients D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.power_polynomial 7
    simp only [single_one_dotProduct] at h0 h1 h2 h3 h4 h5 h6 h7
    norm_num only [coefficients, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ,
      Fin.val_one, Nat.reduceAdd] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
    linear_combination h7 - (-8) * h0 - (48) * h1 - (-84) * h2 - (17) * h3 - (76) * h4 - (-64) * h5 - (16) * h6

end D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
