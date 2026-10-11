/- GID: D5/S3/Quantum/Measurement/FirstReadReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FirstReadReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full deterministic finite histories reduce exactly to the first coordinate read. -/

import D5.S3.Quantum.Measurement.ActualModeProtocol

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder NNReal ENNReal

namespace D5.S3.Quantum.Measurement.FirstReadReduction

open D5.S3.Quantum.Measurement.ActualModeProtocol
open D5.S3.Quantum.Measurement.VisibleAdaptiveRecordLaw (actualWait)
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.TotalVariation.Pinsker (totalVariation)
open D5.S3.TotalVariation.Metric

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total variation on the actual, fully retained finite history space. -/
def historyTV (K : Matrix ι ι ℂ) {n : ℕ} (π : Protocol ι n)
    (X Y : Matrix ι ι ℂ) : ℝ := totalVariation (historyWeight K π X) (historyWeight K π Y)

/-- Probabilities of one full mode read after the specified nonnegative wait. -/
def firstReadProbability (K : Matrix ι ι ℂ) (t : ℝ≥0)
    (X : Matrix ι ι ℂ) (s : ι) : ℝ := (waitState K t X s s).re

def firstReadTV (K : Matrix ι ι ℂ) (t : ℝ≥0) (X Y : Matrix ι ι ℂ) : ℝ :=
  totalVariation (firstReadProbability K t X) (firstReadProbability K t Y)

/-- `none` means Stop was reached without a read. Otherwise this is the sum of
all waits on the common, input-independent prefix before the first read. -/
def firstReadTime : {n : ℕ} → Protocol ι n → Option ℝ≥0
  | _, .stop => none
  | _, .wait t next => (firstReadTime next).map (t + ·)
  | _, .read _ => some 0

private theorem wait_zero (K : Matrix ι ι ℂ) (X : Matrix ι ι ℂ) : waitState K 0 X = X := by
  simp [waitState, actualWait]

private theorem wait_add (K : Matrix ι ι ℂ) (s t : ℝ≥0) (X : Matrix ι ι ℂ) :
    waitState K t (waitState K s X) = waitState K (s + t) X := by
  have hu : actualWait K (s + t) = actualWait K t * actualWait K s := by
    change NormedSpace.exp ((-Complex.I * ((s + t : ℝ≥0) : ℂ)) • K) =
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • K) *
        NormedSpace.exp ((-Complex.I * (s : ℂ)) • K)
    have hc : (-Complex.I * ((s + t : ℝ≥0) : ℂ)) • K =
        (-Complex.I * (t : ℂ)) • K + (-Complex.I * (s : ℂ)) • K := by
      rw [NNReal.coe_add, Complex.ofReal_add, mul_add, add_smul, add_comm]
    rw [hc]
    apply Matrix.exp_add_of_commute
    exact ((Commute.refl K).smul_left _).smul_right _
  simp only [waitState, NNReal.coe_add, hu, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem read_tv (K : Matrix ι ι ℂ) (hK : K.IsHermitian) {n : ℕ}
    (next : ι → Protocol ι n) (X Y : Matrix ι ι ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    historyTV K (.read next) X Y = totalVariation (fun s => (X s s).re)
      (fun s => (Y s s).re) := by
  obtain ⟨hpos, hmass, hfactor⟩ := first_read_factorization K hK next
  unfold historyTV totalVariation
  congr 1
  change (∑ h : (s : ι) × (next s).History,
    |historyWeight K (.read next) X h - historyWeight K (.read next) Y h|) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [hfactor X hX, hfactor Y hY, ← sub_mul, abs_mul,
    abs_of_nonneg (hpos s _)]
  rw [← Finset.mul_sum, hmass, mul_one]

/-- Exact deterministic first-read identity on actual Schrödinger histories.
The two initial matrices may be any positive substates of the same mass. -/
theorem deterministic_first_read (K : Matrix ι ι ℂ) (hK : K.IsHermitian) {n : ℕ}
    (π : Protocol ι n) (X Y : Matrix ι ι ℂ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hmass : Matrix.trace X = Matrix.trace Y) :
    historyTV K π X Y = (firstReadTime π).elim 0 (fun t => firstReadTV K t X Y) := by
  induction π generalizing X Y with
  | stop =>
      change historyTV K .stop X Y = 0
      simp [historyTV, totalVariation, historyWeight, Protocol.History, hmass]
  | read next ih =>
      change historyTV K (.read next) X Y =
        totalVariation (fun s => (waitState K 0 X s s).re)
          (fun s => (waitState K 0 Y s s).re)
      rw [wait_zero, wait_zero]
      exact read_tv K hK next X Y hX hY
  | wait t next ih =>
      have hm : Matrix.trace (waitState K t X) = Matrix.trace (waitState K t Y) := by
        rw [waitState_trace K hK, waitState_trace K hK, hmass]
      change historyTV K next (waitState K t X) (waitState K t Y) = _
      rw [ih (waitState K t X) (waitState K t Y)
        (hX.mul_mul_conjTranspose_same _) (hY.mul_mul_conjTranspose_same _) hm]
      cases ht : firstReadTime next with
      | none => simp only [firstReadTime, ht, Option.map_none, Option.elim_none]
      | some s =>
          simp only [firstReadTime, ht, Option.map_some, Option.elim_some,
            firstReadTV]
          congr 1 <;> funext i <;> dsimp [firstReadProbability] <;> rw [wait_add]

/-- Supremum over all finite deterministic depths. The extended nonnegative
codomain avoids conditional completeness; probability inputs bound it by one. -/
def deterministicDistance (K : Matrix ι ι ℂ) (ρ σ : DensityState ι) : ℝ≥0∞ :=
  ⨆ n, ⨆ π : Protocol ι n, ENNReal.ofReal
    (historyTV K π (CStarMatrix.ofMatrix.symm ρ.1) (CStarMatrix.ofMatrix.symm σ.1))

/-- Every first-read comparison is realized by wait/read/Stop, and every
deterministic finite history has exactly one such comparison or zero. -/
theorem deterministic_distance_eq_first_read (K : Matrix ι ι ℂ) (hK : K.IsHermitian)
    (ρ σ : DensityState ι) :
    deterministicDistance K ρ σ = ⨆ t : ℝ≥0, ENNReal.ofReal
      (firstReadTV K t (CStarMatrix.ofMatrix.symm ρ.1) (CStarMatrix.ofMatrix.symm σ.1)) := by
  unfold deterministicDistance
  let X := CStarMatrix.ofMatrix.symm ρ.1
  let Y := CStarMatrix.ofMatrix.symm σ.1
  have hX : X.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)
  have hY : Y.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm σ.2.1)
  have hm : Matrix.trace X = Matrix.trace Y := ρ.2.2.trans σ.2.2.symm
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun π => ?_
    rw [deterministic_first_read K hK π X Y hX hY hm]
    cases firstReadTime π with
    | none =>
        change ENNReal.ofReal 0 ≤ _
        simp only [ENNReal.ofReal_zero, zero_le]
    | some t =>
        change ENNReal.ofReal (firstReadTV K t X Y) ≤ _
        exact le_iSup (fun u : ℝ≥0 => ENNReal.ofReal (firstReadTV K u X Y)) t
  · refine iSup_le (fun t : ℝ≥0 => ?_)
    let π : Protocol ι 2 := .wait t (.read fun _ => .stop)
    have hp := deterministic_first_read K hK π X Y hX hY hm
    have ht : firstReadTime π = some t := by simp only [π, firstReadTime, Option.map_some, add_zero]
    rw [ht] at hp
    exact le_iSup_of_le 2 (le_iSup_of_le π (by rw [hp]; rfl))

#print axioms deterministic_first_read
#print axioms deterministic_distance_eq_first_read

end D5.S3.Quantum.Measurement.FirstReadReduction
