/- GID: D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripPowers
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457StripPowers
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.result; premises=D5/S3/StatisticalMechanics/Potts/SquareStripDefects/HardinA229457Strip.finite_certificate
   digest: Exact residual-budget square-lattice strip transfer. -/

/-
admission_basis: open-problem-resolution (#31660; Proved)
escape_witness: none (consumed bind-only helpers of the settlement on the live path of HardinA229457Strip.result)
top: proof_shape=bind-only; consumers=leading_steps
lower: proof_shape=bind-only; consumers=leading_steps
balance: proof_shape=bind-only; consumers=weighted_step
no_return: proof_shape=bind-only; consumers=weighted_step
weighted_step: proof_shape=bind-only; consumers=zero_image, leading_steps
zero_image: proof_shape=bind-only; consumers=leading_steps
leading_steps: proof_shape=bind-only; consumers=steps
steps: proof_shape=bind-only; consumers=HardinA229457Strip.result
relation: proof_shape=bind-only; consumers=HardinA229457Strip.result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripStep0
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripStep1
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData

/-! Exact residual-budget square-lattice strip transfer. -/

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open HardinA229457StripData
open D5.S3.Combinatorics.TraceAvoidingArrays
private theorem top (i j : Fin 10) :
    T (i.castAdd 32) (j.castAdd 32) = ProperTransfer.T i j := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem lower : ∀ (i : Fin 32) (j : Fin 10),
    T (i.natAdd 10) (j.castAdd 32) = 0 := by decide +kernel

private theorem balance : ∀ i j : Fin 10,
    64 * initial (i.castAdd 32) * ProperTransfer.T i j =
      initial (j.castAdd 32) * HardinA233127SquareStrip.transfer
        ⟨j.val + 1, by omega⟩ ⟨i.val + 1, by omega⟩ := by decide +kernel

private theorem no_return : ∀ j : Fin 10,
    HardinA233127SquareStrip.transfer ⟨j.val + 1, by omega⟩ 0 = 0 := by decide +kernel

private theorem weighted_step (i : Fin 25)
    (ih : ∀ j : Fin 10, (64 : ℤ)^i.val * W i.castSucc (j.castAdd 32) =
      initial (j.castAdd 32) * HardinA233127SquareStrip.w i.val ⟨j.val + 1, by omega⟩)
    (j : Fin 10) :
    initial (j.castAdd 32) * HardinA233127SquareStrip.w i.succ.val ⟨j.val + 1, by omega⟩ =
      (64 : ℤ)^i.succ.val * ∑ m : Fin 10, W i.castSucc (m.castAdd 32) * ProperTransfer.T m j := by
  change initial (j.castAdd 32) * (∑ m : Fin 11,
    HardinA233127SquareStrip.transfer ⟨j.val + 1, by omega⟩ m *
      HardinA233127SquareStrip.w i.val m) = _
  rw [Fin.sum_univ_succ]
  simp only [no_return, zero_mul, zero_add]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  change initial (j.castAdd 32) *
    (HardinA233127SquareStrip.transfer ⟨j.val + 1, by omega⟩ ⟨m.val + 1, by omega⟩ *
      HardinA233127SquareStrip.w i.val ⟨m.val + 1, by omega⟩) = _
  calc
    _ = (64 * ProperTransfer.T m j) *
        (initial (m.castAdd 32) * HardinA233127SquareStrip.w i.val ⟨m.val + 1, by omega⟩) := by
      rw [show (64 * ProperTransfer.T m j) *
        (initial (m.castAdd 32) * HardinA233127SquareStrip.w i.val ⟨m.val + 1, by omega⟩) =
        (64 * initial (m.castAdd 32) * ProperTransfer.T m j) *
          HardinA233127SquareStrip.w i.val ⟨m.val + 1, by omega⟩ by ring, balance]
      ring
    _ = _ := by rw [← ih m]; simp only [Fin.val_succ, pow_succ]; ring

private theorem zero_image (k : Fin 26) : ∀ j : Fin 10,
    (64 : ℤ)^k.val * W k (j.castAdd 32) =
      initial (j.castAdd 32) * HardinA233127SquareStrip.w k.val ⟨j.val + 1, by omega⟩ := by
  induction k using Fin.induction with
  | zero => intro j; simp [W, HardinA233127SquareStrip.w]
  | succ i ih =>
    intro j
    simp only [Fin.val_castSucc] at ih
    have hs := weighted_step i ih j
    simp only [W, Fin.append_left]
    rw [hs, Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by decide : (64 : ℤ) ≠ 0))]

private theorem leading_steps (i : Fin 25) (j : Fin 10) :
    W i.succ (j.castAdd 32) = Matrix.vecMul (W i.castSucc) T (j.castAdd 32) := by
  rw [Matrix.vecMul, dotProduct, Fin.sum_univ_add (a := 10) (b := 32)]
  simp only [top, lower, mul_zero, Finset.sum_const_zero, add_zero]
  apply mul_left_cancel₀ (pow_ne_zero i.succ.val (by decide : (64 : ℤ) ≠ 0))
  rw [zero_image i.succ]
  exact weighted_step i (by simpa only [Fin.val_castSucc] using zero_image i.castSucc) j

theorem steps : W 0 = initial ∧ ∀ i : Fin 25,
    ∀ s : Fin 42, W i.succ s = Matrix.vecMul (W i.castSucc) T s := by
  refine ⟨by decide +kernel, ?_⟩
  intro i s
  by_cases hs : s.val < 10
  · let j : Fin 10 := ⟨s.val, hs⟩
    have he : s = j.castAdd 32 := rfl
    rw [he]
    exact leading_steps i j
  · let j : Fin 32 := ⟨s.val - 10, by omega⟩
    have he : s = j.natAdd 10 := by apply Fin.ext; dsimp [j]; omega
    rw [he]
    clear he
    by_cases hi : i.val < 13
    · have h := HardinA229457StripStep0.steps ⟨i.val, hi⟩ j
      have h0 : (⟨0 + i.val, by omega⟩ : Fin 26) = i.castSucc := by
        apply Fin.ext
        dsimp
        omega
      have h1 : (⟨0 + i.val + 1, by omega⟩ : Fin 26) = i.succ := by
        apply Fin.ext
        dsimp
        omega
      rw [h0, h1] at h
      exact h
    · have h := HardinA229457StripStep1.steps ⟨i.val - 13, by omega⟩ j
      have h0 : (⟨13 + (i.val - 13), by omega⟩ : Fin 26) = i.castSucc := by
        apply Fin.ext
        dsimp
        omega
      have h1 : (⟨13 + (i.val - 13) + 1, by omega⟩ : Fin 26) = i.succ := by
        apply Fin.ext
        dsimp
        omega
      rw [h0, h1] at h
      exact h

theorem relation (s : Fin 42) : W 15 s = ∑ j : Fin 14, (![-266256, 2220864, -8262712, 18139608, -26188161, 26218062, -18693789, 9593166, -3537110, 924894, -167163, 20016, -1482, 60] j : ℤ) * W ⟨1 + j.val, by omega⟩ s := by
  decide +kernel +revert

end D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripPowers
