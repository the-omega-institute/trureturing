/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635.result; premises=D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_power,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.step_checks,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.residual_entries,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.initial_readout,D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635IntegerCertificate.image_entries
   digest: Signed residual at the first index and its one-step image. -/

import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Sparse
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck0
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck1
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck2

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635IntegerCertificate

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects
open HardinA229635State HardinA229635Transfer HardinA229635Sparse
open HardinA229635SparseData HardinA229635Powers HardinA229635Residual
open DefectTransfer (forward)

private def initialResidual (s : State) : ℤ :=
  if s = 12 then 192 else
  if s = 14 then -192 else
  if s = 15 then -192 else
  if s = 16 then 192 else
  0

private theorem initial_power : ∀ s : State, power 0 s = initial s := by decide +kernel

private theorem step_checks (i : Fin 30) : power i.succ = step (power i.castSucc) := by
  by_cases h0 : i.val < 10
  · let k : Fin 10 := ⟨i.val, h0⟩
    have hi : (⟨0 + k.val, by omega⟩ : Fin 30) = i := Fin.ext (by simp [k])
    simpa only [hi] using HardinA229635PowerCheck0.checked k
  by_cases h1 : i.val < 20
  · let k : Fin 10 := ⟨i.val - 10, by omega⟩
    have hi : (⟨10 + k.val, by omega⟩ : Fin 30) = i := Fin.ext (by dsimp [k]; omega)
    simpa only [hi] using HardinA229635PowerCheck1.checked k
  · let k : Fin 10 := ⟨i.val - 20, by omega⟩
    have hi : (⟨20 + k.val, by omega⟩ : Fin 30) = i := Fin.ext (by dsimp [k]; omega)
    simpa only [hi] using HardinA229635PowerCheck2.checked k

private theorem forward_table {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ)
    (v : Fin d → ℤ) (next : (Fin d → ℤ) → Fin d → ℤ) (p : Fin 31 → Fin d → ℤ)
    (hnext : ∀ w, next w = Matrix.vecMul w M) (hzero : p 0 = v)
    (hstep : ∀ i : Fin 30, p i.succ = next (p i.castSucc)) (i : Fin 31) :
    forward M v i.val = p i := by
  induction i using Fin.induction with
  | zero => exact hzero.symm
  | succ i ih =>
    have hs : forward M v (i.val + 1) = Matrix.vecMul (forward M v i.val) M := by
      simp only [DefectTransfer.forward_eq, pow_succ, Matrix.vecMul_vecMul]
    calc
      forward M v i.succ.val = Matrix.vecMul (forward M v i.val) M := hs
      _ = Matrix.vecMul (p i.castSucc) M := congrArg (fun w => Matrix.vecMul w M) ih
      _ = next (p i.castSucc) := (hnext _).symm
      _ = p i.succ := (hstep i).symm

/- forward_table_iff: proof_shape=bind-only; consumers=HardinA229693Strip.forward_table -/
theorem forward_table_iff {d n : ℕ} (m : Matrix (Fin d) (Fin d) ℤ)
    (v : Fin d → ℤ) (p : Fin (n + 1) → Fin d → ℤ) :
    (∀ i : Fin (n + 1), forward m v i.val = p i) ↔
      p 0 = v ∧ ∀ i : Fin n, p i.succ = Matrix.vecMul (p i.castSucc) m := by
  constructor
  · intro h
    refine ⟨(h 0).symm, ?_⟩
    intro i
    rw [← h i.succ, ← h i.castSucc]
    simp only [Fin.val_succ, Fin.val_castSucc, DefectTransfer.forward_eq, pow_succ,
      Matrix.vecMul_vecMul]
  · rintro ⟨hz, hs⟩ i
    induction i using Fin.induction with
    | zero => exact hz.symm
    | succ i ih =>
      have h : forward m v (i.val + 1) = Matrix.vecMul (forward m v i.val) m := by
        simp only [DefectTransfer.forward_eq, pow_succ, Matrix.vecMul_vecMul]
      exact h.trans ((congrArg (fun w => Matrix.vecMul w m) ih).trans (hs i).symm)

private def lagIndex (j : Fin 27) : Fin 31 := ⟨29 - j.val, by omega⟩

private theorem residual_vector_of_table {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ)
    (v : Fin d → ℤ) (p : Fin 31 → Fin d → ℤ)
    (h : ∀ i : Fin 31, forward M v i.val = p i) :
    residualVector M v = p 30 - ∑ j : Fin 27, coefficients j • p (lagIndex j) := by
  have hlead : forward M v 30 = p 30 := h 30
  have hlag (j : Fin 27) : forward M v (29 - j.val) = p (lagIndex j) := h (lagIndex j)
  simp only [residualVector, hlead, hlag]

private theorem residual_of_zero_image {d : ℕ} (M : Matrix (Fin d) (Fin d) ℤ)
    (v e w : Fin d → ℤ) (hv : residualVector M v = w)
    (hread : dotProduct w e = 0) (hstep : Matrix.vecMul w M = 0) (t : ℕ) :
    residual M v e t = 0 := by
  calc
    residual M v e t = dotProduct (residualVector M v) ((M ^ t).mulVec e) :=
      residual_as_power M v e t
    _ = dotProduct w ((M ^ t).mulVec e) :=
      congrArg (fun u => dotProduct u ((M ^ t).mulVec e)) hv
    _ = 0 := by
      cases t with
      | zero => simpa only [pow_zero, Matrix.one_mulVec] using hread
      | succ k =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hstep, zero_dotProduct]

private def residualEntry (s : State) : ℤ :=
  power 30 s - (List.ofFn fun j : Fin 27 => coefficients j * power (lagIndex j) s).sum

private theorem entries_0 : ∀ k : Fin 32,
    let s : State := k.castAdd 95
    residualEntry s = initialResidual s := by
  decide +kernel

private theorem entries_32 : ∀ k : Fin 32,
    let s : State := (k.castAdd 63).natAdd 32
    residualEntry s = initialResidual s := by
  decide +kernel

private theorem entries_64 : ∀ k : Fin 32,
    let s : State := ((k.castAdd 31).natAdd 32).natAdd 32
    residualEntry s = initialResidual s := by
  decide +kernel

private theorem entries_96 : ∀ k : Fin 31,
    let s : State := ((k.natAdd 32).natAdd 32).natAdd 32
    residualEntry s = initialResidual s := by
  decide +kernel

private theorem residual_entries (s : State) :
    (power 30 - ∑ j : Fin 27, coefficients j • power (lagIndex j)) s =
      initialResidual s := by
  have checked : residualEntry s = initialResidual s :=
    Fin.addCases (m := 32) (n := 95) entries_0
      (Fin.addCases (m := 32) (n := 63) entries_32
        (Fin.addCases (m := 32) (n := 31) entries_64 entries_96)) s
  simpa only [residualEntry, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    List.sum_ofFn] using checked

private theorem initial_readout : dotProduct initialResidual terminal = 0 := by decide +kernel

private theorem image_entries : ∀ s : State, step initialResidual s = 0 := by decide +kernel

theorem residual_all_offsets (t : ℕ) : residual T initial terminal t = 0 := by
  have hforward : ∀ i : Fin 31, forward T initial i.val = power i :=
    forward_table T initial step power step_correct (funext initial_power) step_checks
  have hvector : residualVector T initial = initialResidual :=
    (residual_vector_of_table T initial power hforward).trans (funext residual_entries)
  have himage : Matrix.vecMul initialResidual T = 0 :=
    (step_correct initialResidual).symm.trans (funext image_entries)
  exact residual_of_zero_image T initial terminal initialResidual hvector initial_readout himage t

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635IntegerCertificate
