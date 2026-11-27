/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripPowers
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604StripPowers
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229604Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229604Strip.result)
old_relation: proof_shape=bind-only; consumers=relation
new_relation: proof_shape=bind-only; consumers=relation
leading_steps: proof_shape=bind-only; consumers=steps
normalize_step: proof_shape=bind-only; consumers=steps
steps: proof_shape=bind-only; consumers=HardinA229604Strip.result
relation: proof_shape=bind-only; consumers=HardinA229604Strip.result
initial_relation: proof_shape=bind-only; consumers=HardinA229604Strip.result
-/

import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Mathlib.Tactic.LinearCombination
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep0
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep1
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep2
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep3
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep4
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep5
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep6
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep7
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep8
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep9
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep10
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.TwoDefects.Powers.HardinA229604StripStep11

/-! Forward identities with the old coordinates supplied by the one-defect transfer. -/
open D5.S3.StatisticalMechanics.Potts.StripDefects
open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
open HardinA229604StripData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem leading_steps (i : Fin 24) (s : Fin 42) :
    W i.succ (s.castAdd 54) = Matrix.vecMul (W i.castSucc) T (s.castAdd 54) := by
  have lower (j : Fin 54) : T (j.natAdd 42) (s.castAdd 54) = 0 := by
    simp only [T, Fin.val_natAdd, Fin.val_castAdd]
    split_ifs <;> omega
  have h := HardinA229457StripPowers.steps.2 (i.castAdd 1) s
  have hsucc : (i.castAdd 1).succ = (i.succ).castAdd 1 := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castAdd]
  have hprev : (i.castAdd 1).castSucc = (i.castSucc).castAdd 1 := by
    apply Fin.ext
    rfl
  rw [hsucc, hprev] at h
  rw [Matrix.vecMul, dotProduct, Fin.sum_univ_add (a := 42) (b := 54)]
  simpa only [W, Fin.append_left, leading_block, lower, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.vecMul, dotProduct] using h

private theorem normalize_step (i : Fin 24) (j : Fin 54) (x y : ℕ)
    (hx : x ≤ i.val) (hy : y ≤ j.val)
    (h : W ⟨x + (i.val - x) + 1, by omega⟩ ⟨42 + y + (j.val - y), by omega⟩ =
      Matrix.vecMul (W ⟨x + (i.val - x), by omega⟩) T ⟨42 + y + (j.val - y), by omega⟩) :
    W i.succ (j.natAdd 42) = Matrix.vecMul (W i.castSucc) T (j.natAdd 42) := by
  have hprev : (⟨x + (i.val - x), by omega⟩ : Fin 25) = i.castSucc := by
    apply Fin.ext
    dsimp <;> omega
  have hsucc : (⟨x + (i.val - x) + 1, by omega⟩ : Fin 25) = i.succ := by
    apply Fin.ext
    dsimp <;> omega
  have htarget : (⟨42 + y + (j.val - y), by omega⟩ : Fin 96) = j.natAdd 42 := by
    apply Fin.ext
    dsimp <;> omega
  rw [hprev, hsucc, htarget] at h
  exact h

theorem steps : W 0 = initial ∧ ∀ i : Fin 24,
    ∀ s : Fin 96, W i.succ s = Matrix.vecMul (W i.castSucc) T s := by
  refine ⟨by decide +kernel, ?_⟩
  intro i s
  by_cases hs : s.val < 42
  · exact leading_steps i ⟨s.val, hs⟩
  · have target : ∃ j : Fin 54, s = j.natAdd 42 := by
      refine ⟨⟨s.val - 42, by omega⟩, ?_⟩
      apply Fin.ext
      dsimp
      omega
    obtain ⟨j, hj⟩ := target
    rw [hj]
    by_cases h0 : 0 ≤ i.val ∧ i.val < 6 ∧ 0 ≤ j.val ∧ j.val < 18
    · have h := TwoDefects.Powers.HardinA229604StripStep0.steps ⟨i.val - 0, by omega⟩ ⟨j.val - 0, by omega⟩
      exact normalize_step i j 0 0 (by omega) (by omega) h
    by_cases h1 : 0 ≤ i.val ∧ i.val < 6 ∧ 18 ≤ j.val ∧ j.val < 36
    · have h := TwoDefects.Powers.HardinA229604StripStep1.steps ⟨i.val - 0, by omega⟩ ⟨j.val - 18, by omega⟩
      exact normalize_step i j 0 18 (by omega) (by omega) h
    by_cases h2 : 0 ≤ i.val ∧ i.val < 6 ∧ 36 ≤ j.val ∧ j.val < 54
    · have h := TwoDefects.Powers.HardinA229604StripStep2.steps ⟨i.val - 0, by omega⟩ ⟨j.val - 36, by omega⟩
      exact normalize_step i j 0 36 (by omega) (by omega) h
    by_cases h3 : 6 ≤ i.val ∧ i.val < 12 ∧ 0 ≤ j.val ∧ j.val < 18
    · have h := TwoDefects.Powers.HardinA229604StripStep3.steps ⟨i.val - 6, by omega⟩ ⟨j.val - 0, by omega⟩
      exact normalize_step i j 6 0 (by omega) (by omega) h
    by_cases h4 : 6 ≤ i.val ∧ i.val < 12 ∧ 18 ≤ j.val ∧ j.val < 36
    · have h := TwoDefects.Powers.HardinA229604StripStep4.steps ⟨i.val - 6, by omega⟩ ⟨j.val - 18, by omega⟩
      exact normalize_step i j 6 18 (by omega) (by omega) h
    by_cases h5 : 6 ≤ i.val ∧ i.val < 12 ∧ 36 ≤ j.val ∧ j.val < 54
    · have h := TwoDefects.Powers.HardinA229604StripStep5.steps ⟨i.val - 6, by omega⟩ ⟨j.val - 36, by omega⟩
      exact normalize_step i j 6 36 (by omega) (by omega) h
    by_cases h6 : 12 ≤ i.val ∧ i.val < 18 ∧ 0 ≤ j.val ∧ j.val < 18
    · have h := TwoDefects.Powers.HardinA229604StripStep6.steps ⟨i.val - 12, by omega⟩ ⟨j.val - 0, by omega⟩
      exact normalize_step i j 12 0 (by omega) (by omega) h
    by_cases h7 : 12 ≤ i.val ∧ i.val < 18 ∧ 18 ≤ j.val ∧ j.val < 36
    · have h := TwoDefects.Powers.HardinA229604StripStep7.steps ⟨i.val - 12, by omega⟩ ⟨j.val - 18, by omega⟩
      exact normalize_step i j 12 18 (by omega) (by omega) h
    by_cases h8 : 12 ≤ i.val ∧ i.val < 18 ∧ 36 ≤ j.val ∧ j.val < 54
    · have h := TwoDefects.Powers.HardinA229604StripStep8.steps ⟨i.val - 12, by omega⟩ ⟨j.val - 36, by omega⟩
      exact normalize_step i j 12 36 (by omega) (by omega) h
    by_cases h9 : 18 ≤ i.val ∧ i.val < 24 ∧ 0 ≤ j.val ∧ j.val < 18
    · have h := TwoDefects.Powers.HardinA229604StripStep9.steps ⟨i.val - 18, by omega⟩ ⟨j.val - 0, by omega⟩
      exact normalize_step i j 18 0 (by omega) (by omega) h
    by_cases h10 : 18 ≤ i.val ∧ i.val < 24 ∧ 18 ≤ j.val ∧ j.val < 36
    · have h := TwoDefects.Powers.HardinA229604StripStep10.steps ⟨i.val - 18, by omega⟩ ⟨j.val - 18, by omega⟩
      exact normalize_step i j 18 18 (by omega) (by omega) h
    by_cases h11 : 18 ≤ i.val ∧ i.val < 24 ∧ 36 ≤ j.val ∧ j.val < 54
    · have h := TwoDefects.Powers.HardinA229604StripStep11.steps ⟨i.val - 18, by omega⟩ ⟨j.val - 36, by omega⟩
      exact normalize_step i j 18 36 (by omega) (by omega) h
    omega

private theorem old_relation (s : Fin 42) : HardinA229457StripData.W 24 s =
    ∑ j : Fin 21, (![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] j : ℤ) * HardinA229457StripData.W ⟨3 + j.val, by omega⟩ s := by
  have tab (i : Fin 26) :
      DefectTransfer.forward HardinA229457StripData.T HardinA229457StripData.initial i.val = HardinA229457StripData.W i := by
    induction i using Fin.induction with
    | zero => exact HardinA229457StripPowers.steps.1.symm
    | succ i ih =>
      rw [DefectTransfer.forward, Fin.val_succ, Function.iterate_succ_apply']
      change Matrix.vecMul (DefectTransfer.forward HardinA229457StripData.T HardinA229457StripData.initial i.val)
        HardinA229457StripData.T = HardinA229457StripData.W i.succ
      change DefectTransfer.forward HardinA229457StripData.T HardinA229457StripData.initial i.val = HardinA229457StripData.W i.castSucc at ih
      rw [ih]
      exact (funext (HardinA229457StripPowers.steps.2 i)).symm
  have poly : DefectTransfer.forward HardinA229457StripData.T HardinA229457StripData.initial (1 + 14) =
      ∑ j : Fin 14, (![-266256, 2220864, -8262712, 18139608, -26188161, 26218062, -18693789, 9593166, -3537110, 924894, -167163, 20016, -1482, 60] j : ℤ) •
        DefectTransfer.forward HardinA229457StripData.T HardinA229457StripData.initial (1 + j.val) := by
    rw [tab ⟨15, by omega⟩]
    simp_rw [show ∀ j : Fin 14,
      DefectTransfer.forward HardinA229457StripData.T HardinA229457StripData.initial (1 + j.val) =
        HardinA229457StripData.W ⟨1 + j.val, by omega⟩ from fun j => tab ⟨1 + j.val, by omega⟩]
    rw [show (⟨15, by omega⟩ : Fin 26) = (15 : Fin 26) by decide]
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      HardinA229457StripPowers.relation x
  have obs (i : Fin 26) : dotProduct HardinA229457StripData.initial
      ((HardinA229457StripData.T ^ i.val).mulVec (Pi.single s 1)) = HardinA229457StripData.W i s := by
    rw [Matrix.dotProduct_mulVec, ← DefectTransfer.forward_eq, tab i,
      dotProduct_single_one]
  have shifted (k : Fin 8) : HardinA229457StripData.W ⟨17 + k.val, by omega⟩ s =
      ∑ j : Fin 14, (![-266256, 2220864, -8262712, 18139608, -26188161, 26218062, -18693789, 9593166, -3537110, 924894, -167163, 20016, -1482, 60] j : ℤ) *
        HardinA229457StripData.W ⟨3 + k.val + j.val, by omega⟩ s := by
    have h := DefectTransfer.forward_shift HardinA229457StripData.T HardinA229457StripData.initial
      (Pi.single s 1) 14 1 ![-266256, 2220864, -8262712, 18139608, -26188161, 26218062, -18693789, 9593166, -3537110, 924894, -167163, 20016, -1482, 60] poly (2 + k.val)
    rw [obs ⟨2 + k.val + 1 + 14, by omega⟩] at h
    simp_rw [show ∀ j : Fin 14, dotProduct HardinA229457StripData.initial
      ((HardinA229457StripData.T ^ (2 + k.val + 1 + j.val)).mulVec (Pi.single s 1)) =
        HardinA229457StripData.W ⟨2 + k.val + 1 + j.val, by omega⟩ s from
          fun j => obs ⟨2 + k.val + 1 + j.val, by omega⟩] at h
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.reduceAdd] using h
  have h0 := shifted 0
  have h1 := shifted 1
  have h2 := shifted 2
  have h3 := shifted 3
  have h4 := shifted 4
  have h5 := shifted 5
  have h6 := shifted 6
  have h7 := shifted 7
  rw [show (24 : Fin 26) = ⟨24, by omega⟩ by apply Fin.ext; norm_num]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one, Fin.val_ofNat, Nat.reduceMod, Nat.reduceAdd] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  linear_combination (-516 : ℤ) * h0 + (2152 : ℤ) * h1 + (-3519 : ℤ) * h2 + (2901 : ℤ) * h3 + (-1278 : ℤ) * h4 + (291 : ℤ) * h5 + (-30 : ℤ) * h6 + (1 : ℤ) * h7

private theorem new_relation : ∀ j : Fin 54, W 24 (j.natAdd 42) =
    ∑ k : Fin 21, (![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] k : ℤ) * W ⟨3 + k.val, by omega⟩ (j.natAdd 42) := by
  decide +kernel

theorem relation (s : Fin 96) : W 24 s =
    ∑ j : Fin 21, (![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] j : ℤ) * W ⟨3 + j.val, by omega⟩ s := by
  by_cases hs : s.val < 42
  · let j : Fin 42 := ⟨s.val, hs⟩
    have he : s = j.castAdd 54 := rfl
    rw [he]
    have h24 : (24 : Fin 25).castAdd 1 = (24 : Fin 26) := by decide
    have hcast (k : Fin 21) :
        (⟨3 + k.val, by omega⟩ : Fin 25).castAdd 1 =
          (⟨3 + k.val, by omega⟩ : Fin 26) := by
      apply Fin.ext
      rfl
    simpa only [W, Fin.append_left, h24, hcast] using old_relation j
  · let j : Fin 54 := ⟨s.val - 42, by omega⟩
    have he : s = j.natAdd 42 := by apply Fin.ext; dsimp [j]; omega
    rw [he]
    exact new_relation j

theorem initial_relation : dotProduct (W 23) terminal =
    ∑ j : Fin 21, (![137388096, -1718948736, 9979813584, -35729023024, 88409012652, -160604595216, 222060410955, -239066083215, 203308881255, -137758028106, 74677395474, -32398609896, 11214272853, -3076398702, 661896144, -110021385, 13836015, -1278486, 83214, -3573, 90] j : ℤ) * dotProduct (W ⟨2 + j.val, by omega⟩) terminal := by
  decide +kernel

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripPowers
