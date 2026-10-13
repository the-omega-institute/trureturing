/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.claim; result=D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.result; claim=D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.claim
   digest: A three-level mixed state refutes log-convexity of purity under optical loss. -/

import D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation
import D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
import D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation

open D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation (FockSpace e)
open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
open D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
  (purePartialTrace mixture)
open D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
  (fockPair_apply)

local notation "H" => FockSpace
local notation "PairH" => lp (fun _ : ℕ => H) 2
local notation "Op" => H →L[ℂ] H

/-- A finite ensemble of arbitrary unit vectors in the full one-mode Fock space. -/
structure Ensemble (k : ℕ) where
  weight : Fin k → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  vector : Fin k → H
  vector_unit : ∀ i, ‖vector i‖ = 1

/-- Vacuum-environment optical loss, with the second mode traced out. -/
def loss {k : ℕ} (E : Ensemble k) (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) : Op :=
  ∑ i : Fin k, (E.weight i : ℂ) •
    purePartialTrace (beamSplitter T hT (tensor (E.vector i) (e 0)))

/-- The Fock-basis trace of the square, including convergence and reality of its value. -/
def IsPurityCurve {k : ℕ} (E : Ensemble k) (P : ℝ → ℝ) : Prop :=
  ∀ (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1),
    HasSum (fun n : ℕ => inner ℂ (e n) ((loss E T hT ∘L loss E T hT) (e n)))
      (P T : ℂ)

/-- The finite-ensemble restriction of Conjecture 7 of arXiv:2501.02047v1, §III. -/
def claim : Prop :=
  ∀ (k : ℕ) (E : Ensemble k), ∃ P : ℝ → ℝ,
    IsPurityCurve E P ∧ ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun T => Real.log (P T))

private def witness : Ensemble 3 where
  weight := ![(1 / 100 : ℝ), 3 / 4, 6 / 25]
  weight_nonneg := by intro i; fin_cases i <;> norm_num
  weight_sum := by norm_num [Fin.sum_univ_succ]
  vector := fun i => e (i : ℕ)
  vector_unit := by
    intro i
    unfold e
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    exact norm_one

private def split (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) : PairH :=
  beamSplitter T hT (tensor (e n) (e 0))

private def middleAmplitude (T : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sqrt T * Real.sqrt (1 - T)

private theorem split_zero (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    split T hT 0 = fockPair 0 0 := by
  unfold split
  change beamSplitter T hT (fockPair 0 0) = _
  unfold beamSplitter
  rw [beamUnitary_fock]
  norm_num [fockExpansion, Fin.sum_univ_succ]

private theorem split_one (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    split T hT 1 = (Real.sqrt T : ℂ) • fockPair 1 0 +
      (Real.sqrt (1 - T) : ℂ) • fockPair 0 1 := by
  unfold split
  change beamSplitter T hT (fockPair 1 0) = _
  unfold beamSplitter
  rw [beamUnitary_fock]
  norm_num [fockExpansion, Fin.sum_univ_succ]
  ac_rfl

private theorem split_two (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    split T hT 2 = (T : ℂ) • fockPair 2 0 +
      (middleAmplitude T : ℂ) • fockPair 1 1 +
      ((1 - T : ℝ) : ℂ) • fockPair 0 2 := by
  unfold split
  change beamSplitter T hT (fockPair 2 0) = _
  unfold beamSplitter
  rw [beamUnitary_fock]
  norm_num [fockExpansion, Fin.sum_univ_succ, Nat.choose]
  change (Real.sqrt (1 - T) : ℂ) ^ 2 • fockPair 0 2 +
    ((2 * (Real.sqrt T : ℂ) * (Real.sqrt (1 - T) : ℂ) / (Real.sqrt 2 : ℂ)) •
      fockPair 1 1 + (Real.sqrt T : ℂ) ^ 2 • fockPair 2 0) =
    (T : ℂ) • fockPair 2 0 + (middleAmplitude T : ℂ) • fockPair 1 1 +
      (1 - (T : ℂ)) • fockPair 0 2
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h0 := Real.sq_sqrt hT.1
  have h1 := Real.sq_sqrt (sub_nonneg.mpr hT.2)
  have hc1 : (2 * Real.sqrt T * Real.sqrt (1 - T) / Real.sqrt 2 : ℝ) =
      middleAmplitude T := by
    unfold middleAmplitude
    apply (div_eq_iff hs).mpr
    calc
      _ = Real.sqrt 2 ^ 2 * Real.sqrt T * Real.sqrt (1 - T) := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      _ = _ := by ring
  have hc0 : (Real.sqrt (1 - T) : ℂ) ^ 2 = 1 - (T : ℂ) := by exact_mod_cast h1
  have hc2 : (Real.sqrt T : ℂ) ^ 2 = (T : ℂ) := by exact_mod_cast h0
  have hcm : 2 * (Real.sqrt T : ℂ) * (Real.sqrt (1 - T) : ℂ) /
      (Real.sqrt 2 : ℂ) = (middleAmplitude T : ℂ) := by exact_mod_cast hc1
  rw [hc0, hcm, hc2]
  ac_rfl

private theorem split_zero_slice (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    split T hT 0 j = if j = 0 then e 0 else 0 := by
  rw [split_zero]
  apply lp.ext
  funext p
  simp only [fockPair_apply]
  split_ifs <;> simp_all [e, lp.single_apply]

private theorem split_one_slice (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    split T hT 1 j =
      if j = 0 then (Real.sqrt T : ℂ) • e 1
      else if j = 1 then (Real.sqrt (1 - T) : ℂ) • e 0 else 0 := by
  rw [split_one]
  by_cases hj0 : j = 0
  · subst j
    apply lp.ext
    funext p
    change (Real.sqrt T : ℂ) * fockPair 1 0 0 p +
      (Real.sqrt (1 - T) : ℂ) * fockPair 0 1 0 p = (Real.sqrt T : ℂ) * e 1 p
    rw [fockPair_apply, fockPair_apply]
    simp [e, lp.single_apply, Pi.single_apply]
  · by_cases hj1 : j = 1
    · subst j
      apply lp.ext
      funext p
      change (Real.sqrt T : ℂ) * fockPair 1 0 1 p +
        (Real.sqrt (1 - T) : ℂ) * fockPair 0 1 1 p =
          (Real.sqrt (1 - T) : ℂ) * e 0 p
      rw [fockPair_apply, fockPair_apply]
      simp [e, lp.single_apply, Pi.single_apply]
    · rw [if_neg hj0, if_neg hj1]
      apply lp.ext
      funext p
      change (Real.sqrt T : ℂ) * fockPair 1 0 j p +
        (Real.sqrt (1 - T) : ℂ) * fockPair 0 1 j p = 0
      rw [fockPair_apply, fockPair_apply]
      simp [hj0, hj1]

private theorem split_two_slice (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    split T hT 2 j =
      if j = 0 then (T : ℂ) • e 2
      else if j = 1 then (middleAmplitude T : ℂ) • e 1
      else if j = 2 then ((1 - T : ℝ) : ℂ) • e 0 else 0 := by
  rw [split_two]
  by_cases hj0 : j = 0
  · subst j
    apply lp.ext
    funext p
    change (T : ℂ) * fockPair 2 0 0 p +
      (middleAmplitude T : ℂ) * fockPair 1 1 0 p +
      ((1 - T : ℝ) : ℂ) * fockPair 0 2 0 p = (T : ℂ) * e 2 p
    rw [fockPair_apply, fockPair_apply, fockPair_apply]
    simp [e, lp.single_apply, Pi.single_apply]
  · by_cases hj1 : j = 1
    · subst j
      apply lp.ext
      funext p
      change (T : ℂ) * fockPair 2 0 1 p +
        (middleAmplitude T : ℂ) * fockPair 1 1 1 p +
        ((1 - T : ℝ) : ℂ) * fockPair 0 2 1 p = (middleAmplitude T : ℂ) * e 1 p
      rw [fockPair_apply, fockPair_apply, fockPair_apply]
      simp [e, lp.single_apply, Pi.single_apply]
    · by_cases hj2 : j = 2
      · subst j
        rw [if_neg (by decide : (2 : ℕ) ≠ 0), if_neg (by decide : (2 : ℕ) ≠ 1), if_pos rfl]
        apply lp.ext
        funext p
        change (T : ℂ) * fockPair 2 0 2 p +
          (middleAmplitude T : ℂ) * fockPair 1 1 2 p +
          ((1 - T : ℝ) : ℂ) * fockPair 0 2 2 p = ((1 - T : ℝ) : ℂ) * e 0 p
        rw [fockPair_apply, fockPair_apply, fockPair_apply]
        simp [e, lp.single_apply, Pi.single_apply]
      · rw [if_neg hj0, if_neg hj1, if_neg hj2]
        apply lp.ext
        funext p
        change (T : ℂ) * fockPair 2 0 j p +
          (middleAmplitude T : ℂ) * fockPair 1 1 j p +
          ((1 - T : ℝ) : ℂ) * fockPair 0 2 j p = 0
        rw [fockPair_apply, fockPair_apply, fockPair_apply]
        simp [hj0, hj1, hj2]

private def proj (n : ℕ) : Op := InnerProductSpace.rankOne ℂ (e n) (e n)

private def diag3 (a b c : ℝ) : Op :=
  (a : ℂ) • proj 0 + (b : ℂ) • proj 1 + (c : ℂ) • proj 2

private theorem rankOne_real_smul (a : ℝ) (v : H) :
    InnerProductSpace.rankOne ℂ ((a : ℂ) • v) ((a : ℂ) • v) =
      ((a ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ v v := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left, Complex.conj_ofReal,
    smul_apply, smul_smul, Complex.ofReal_pow]
  congr 1
  ring

private theorem partialTrace_three_slices (v : PairH) (hv : ∀ j : ℕ, 3 ≤ j → v j = 0) :
    purePartialTrace v =
      ∑ j ∈ Finset.range 3, InnerProductSpace.rankOne ℂ (v j) (v j) := by
  unfold purePartialTrace mixture
  change (∑' j : ℕ, InnerProductSpace.rankOne ℂ (v j) (v j)) = _
  apply tsum_eq_sum
  intro j hj
  have hj' : 3 ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
  rw [hv j hj']
  simp only [map_zero]

private theorem middleAmplitude_sq (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    middleAmplitude T ^ 2 = 2 * T * (1 - T) := by
  unfold middleAmplitude
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hT.1, Real.sq_sqrt (sub_nonneg.mpr hT.2)]

private theorem partialTrace_zero (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    purePartialTrace (split T hT 0) = diag3 1 0 0 := by
  rw [partialTrace_three_slices _ (by
    intro j hj
    rw [split_zero_slice, if_neg (by omega)])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, split_zero_slice]
  norm_num [diag3, proj]

private theorem partialTrace_one (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    purePartialTrace (split T hT 1) = diag3 (1 - T) T 0 := by
  rw [partialTrace_three_slices _ (by
    intro j hj
    rw [split_one_slice, if_neg (by omega), if_neg (by omega)])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, split_one_slice]
  norm_num only [Nat.zero_ne_one, Nat.one_ne_zero, ite_true, ite_false, zero_add,
    rankOne_real_smul, Real.sq_sqrt hT.1, Real.sq_sqrt (sub_nonneg.mpr hT.2)]
  simp only [diag3, proj, Complex.ofReal_zero, zero_smul, add_zero, map_zero]
  ac_rfl

private theorem partialTrace_two (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    purePartialTrace (split T hT 2) =
      diag3 ((1 - T) ^ 2) (2 * T * (1 - T)) (T ^ 2) := by
  rw [partialTrace_three_slices _ (by
    intro j hj
    rw [split_two_slice, if_neg (by omega), if_neg (by omega), if_neg (by omega)])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, split_two_slice]
  norm_num only [Nat.zero_ne_one, Nat.one_ne_zero, ite_true, ite_false, zero_add,
    rankOne_real_smul]
  rw [middleAmplitude_sq T hT]
  unfold diag3 proj
  ac_rfl

private def q0 (T : ℝ) : ℝ :=
  1 / 100 + (3 / 4) * (1 - T) + (6 / 25) * (1 - T) ^ 2

private def q1 (T : ℝ) : ℝ :=
  (3 / 4) * T + (12 / 25) * T * (1 - T)

private def q2 (T : ℝ) : ℝ := (6 / 25) * T ^ 2

private theorem witness_output (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    loss witness T hT = diag3 (q0 T) (q1 T) (q2 T) := by
  unfold loss
  change (∑ i : Fin 3, (witness.weight i : ℂ) •
    purePartialTrace (split T hT i.val)) = _
  simp only [Fin.sum_univ_succ]
  change ((1 / 100 : ℝ) : ℂ) • purePartialTrace (split T hT 0) +
    (((3 / 4 : ℝ) : ℂ) • purePartialTrace (split T hT 1) +
    (((6 / 25 : ℝ) : ℂ) • purePartialTrace (split T hT 2) + 0)) = _
  rw [partialTrace_zero, partialTrace_one, partialTrace_two]
  unfold diag3 q0 q1 q2
  simp only [smul_add, smul_smul, Complex.ofReal_zero, Complex.ofReal_one,
    one_smul, zero_smul, add_zero, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  module

end D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation

-- The canonical utility header is a single machine-readable line.
set_option linter.style.longLine false
