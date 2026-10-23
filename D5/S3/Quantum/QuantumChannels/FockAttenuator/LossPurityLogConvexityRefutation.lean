/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.claim; result=D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.result; claim=D5/S3/Quantum/QuantumChannels/FockAttenuator/LossPurityLogConvexityRefutation.claim
   digest: A three-level mixed state refutes log-convexity of purity under optical loss. -/

import D5.S3.Quantum.Measurement.PureLossIncompatibility
import D5.S3.Quantum.QuantumChannels.FockAttenuator.Entropy

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation

open D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation (FockSpace e)
open D5.S3.Quantum.Measurement
open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
open D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
  (purePartialTrace mixture)
open D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
  (fockPair_apply)

open D5.S3.Quantum.Measurement.PureLossIncompatibility (H K Op)
open D5.S3.Quantum.QuantumChannels.FockAttenuator.Entropy (finiteDiagonal)

/-- Vacuum-environment optical loss, with the second mode traced out. -/
def loss {k : ℕ} (p : Fin k → ℝ) (φ : Fin k → H)
    (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) : Op :=
  ∑ i : Fin k, (p i : ℂ) •
    purePartialTrace (beamSplitter T hT (tensor (φ i) (e 0)))

/-- The Fock-basis trace of the square, including convergence and reality of its value. -/
def IsPurityCurve {k : ℕ} (p : Fin k → ℝ) (φ : Fin k → H) (P : ℝ → ℝ) : Prop :=
  ∀ (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1),
    HasSum (fun n : ℕ => inner ℂ (e n) ((loss p φ T hT ∘L loss p φ T hT) (e n)))
      (P T : ℂ)

/-- The finite-ensemble restriction of Conjecture 7 of arXiv:2501.02047v1, §III. -/
def claim : Prop :=
  ∀ (k : ℕ) (p : Fin k → ℝ) (φ : Fin k → H),
    (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → (∀ i, ‖φ i‖ = 1) →
    ∃ P : ℝ → ℝ,
      IsPurityCurve p φ P ∧ ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun T => Real.log (P T))

private def weights : Fin 3 → ℝ := ![(1 / 100 : ℝ), 3 / 4, 6 / 25]

private def vectors (i : Fin 3) : H := e (i : ℕ)

private def middleAmplitude (T : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sqrt T * Real.sqrt (1 - T)

private theorem split_stinespring (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    beamSplitter T hT (tensor (e n) (e 0)) =
      PureLossIncompatibility.stinespring ⟨T, hT⟩ (e n) := by
  change beamSplitter T hT (tensor (e n) (e 0)) =
    beamSplitter T hT (PureLossIncompatibility.vacuumEmbedding (e n))
  rw [PureLossIncompatibility.vacuum_tensor]

private theorem split_two (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    beamSplitter T hT (tensor (e 2) (e 0)) = (T : ℂ) • fockPair 2 0 +
      (middleAmplitude T : ℂ) • fockPair 1 1 +
      ((1 - T : ℝ) : ℂ) • fockPair 0 2 := by
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
    beamSplitter T hT (tensor (e 0) (e 0)) j = if j = 0 then e 0 else 0 := by
  rw [split_stinespring]
  exact PureLossIncompatibility.split_zero_coord ⟨T, hT⟩ j

private theorem split_one_slice (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    beamSplitter T hT (tensor (e 1) (e 0)) j =
      if j = 0 then (Real.sqrt T : ℂ) • e 1
      else if j = 1 then (Real.sqrt (1 - T) : ℂ) • e 0 else 0 := by
  rw [split_stinespring]
  exact PureLossIncompatibility.split_one_coord ⟨T, hT⟩ j

private theorem split_two_slice (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    beamSplitter T hT (tensor (e 2) (e 0)) j =
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

private theorem finiteDiagonal_three_eq (a b c : ℝ) :
    finiteDiagonal ![a, b, c] =
      (a : ℂ) • InnerProductSpace.rankOne ℂ (e 0) (e 0) +
      (b : ℂ) • InnerProductSpace.rankOne ℂ (e 1) (e 1) +
      (c : ℂ) • InnerProductSpace.rankOne ℂ (e 2) (e 2) := by
  change (∑ i : Fin 3, ((![(a : ℝ), b, c] : Fin 3 → ℝ) i : ℂ) •
    InnerProductSpace.rankOne ℂ (e (i : ℕ)) (e (i : ℕ))) = _
  simp only [Fin.sum_univ_succ]
  change (a : ℂ) • InnerProductSpace.rankOne ℂ (e 0) (e 0) +
    ((b : ℂ) • InnerProductSpace.rankOne ℂ (e 1) (e 1) +
    ((c : ℂ) • InnerProductSpace.rankOne ℂ (e 2) (e 2) + 0)) = _
  simp only [add_zero, add_assoc]

private theorem rankOne_real_smul (a : ℝ) (v : H) :
    InnerProductSpace.rankOne ℂ ((a : ℂ) • v) ((a : ℂ) • v) =
      ((a ^ 2 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ v v := by
  rw [ContinuousLinearMap.map_smul, smul_apply, ContinuousLinearMap.map_smulₛₗ,
    starRingEnd_apply, Complex.star_def, Complex.conj_ofReal, smul_smul,
    ← pow_two, ← Complex.ofReal_pow]

private theorem partialTrace_three_slices (v : K) (hv : ∀ j : ℕ, 3 ≤ j → v j = 0) :
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
    purePartialTrace (beamSplitter T hT (tensor (e 0) (e 0))) = finiteDiagonal ![1, 0, 0] := by
  rw [partialTrace_three_slices _ (by
    intro j hj
    rw [split_zero_slice, if_neg (by omega)])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, split_zero_slice]
  rw [finiteDiagonal_three_eq]
  norm_num

private theorem partialTrace_one (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    purePartialTrace (beamSplitter T hT (tensor (e 1) (e 0))) = finiteDiagonal ![1 - T, T, 0] := by
  rw [partialTrace_three_slices _ (by
    intro j hj
    rw [split_one_slice, if_neg (by omega), if_neg (by omega)])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, split_one_slice]
  norm_num only [ite_true, ite_false, zero_add,
    rankOne_real_smul, Real.sq_sqrt hT.1, Real.sq_sqrt (sub_nonneg.mpr hT.2)]
  rw [finiteDiagonal_three_eq]
  simp only [Complex.ofReal_zero, zero_smul, add_zero, map_zero]
  ac_rfl

private theorem partialTrace_two (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    purePartialTrace (beamSplitter T hT (tensor (e 2) (e 0))) =
      finiteDiagonal ![(1 - T) ^ 2, 2 * T * (1 - T), T ^ 2] := by
  rw [partialTrace_three_slices _ (by
    intro j hj
    rw [split_two_slice, if_neg (by omega), if_neg (by omega), if_neg (by omega)])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, split_two_slice]
  norm_num only [ite_true, ite_false, zero_add,
    rankOne_real_smul]
  rw [middleAmplitude_sq T hT]
  rw [finiteDiagonal_three_eq]
  ac_rfl

private def q0 (T : ℝ) : ℝ :=
  1 / 100 + (3 / 4) * (1 - T) + (6 / 25) * (1 - T) ^ 2

private def q1 (T : ℝ) : ℝ :=
  (3 / 4) * T + (12 / 25) * T * (1 - T)

private def q2 (T : ℝ) : ℝ := (6 / 25) * T ^ 2

private theorem witness_output (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    loss weights vectors T hT = finiteDiagonal ![q0 T, q1 T, q2 T] := by
  unfold loss
  change (∑ i : Fin 3, (weights i : ℂ) •
    purePartialTrace (beamSplitter T hT (tensor (e i.val) (e 0)))) = _
  simp only [Fin.sum_univ_succ]
  change ((1 / 100 : ℝ) : ℂ) • purePartialTrace (beamSplitter T hT (tensor (e 0) (e 0))) +
    (((3 / 4 : ℝ) : ℂ) • purePartialTrace (beamSplitter T hT (tensor (e 1) (e 0))) +
    (((6 / 25 : ℝ) : ℂ) • purePartialTrace (beamSplitter T hT (tensor (e 2) (e 0))) + 0)) = _
  rw [partialTrace_zero, partialTrace_one, partialTrace_two]
  rw [finiteDiagonal_three_eq, finiteDiagonal_three_eq,
    finiteDiagonal_three_eq, finiteDiagonal_three_eq]
  unfold q0 q1 q2
  simp only [smul_add, smul_smul, Complex.ofReal_zero, Complex.ofReal_one,
    one_smul, zero_smul, add_zero, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  module

private theorem finiteDiagonal_three_purity (a b c : ℝ) :
    HasSum (fun n : ℕ => inner ℂ (e n)
      ((finiteDiagonal ![a, b, c] ∘L finiteDiagonal ![a, b, c]) (e n)))
      ((a ^ 2 + b ^ 2 + c ^ 2 : ℝ) : ℂ) := by
  have hinner (i j : ℕ) : inner ℂ (e i) (e j) = if i = j then 1 else 0 := by
    simp [e, lp.inner_single_left, lp.single_apply, Pi.single_apply, RCLike.inner_apply]
  have hdiag (n : ℕ) : finiteDiagonal ![a, b, c] (e n) =
      ((if n = 0 then a else if n = 1 then b else if n = 2 then c else 0 : ℝ) : ℂ) •
        e n := by
    simp only [finiteDiagonal_three_eq, add_apply, smul_apply,
      InnerProductSpace.rankOne_apply, hinner]
    by_cases h0 : n = 0
    · subst n; norm_num
    · by_cases h1 : n = 1
      · subst n; norm_num
      · by_cases h2 : n = 2
        · subst n; norm_num
        · simp [h0, h1, h2, Ne.symm h0, Ne.symm h1, Ne.symm h2]
  have hterm (n : ℕ) :
      inner ℂ (e n) ((finiteDiagonal ![a, b, c] ∘L finiteDiagonal ![a, b, c]) (e n)) =
        if n = 0 then ((a ^ 2 : ℝ) : ℂ)
        else if n = 1 then ((b ^ 2 : ℝ) : ℂ)
        else if n = 2 then ((c ^ 2 : ℝ) : ℂ) else 0 := by
    simp only [ContinuousLinearMap.comp_apply, hdiag, map_smul, inner_smul_right,
      hinner, ite_true]
    split_ifs <;> simp_all [pow_two]
  have hs : HasSum
      (fun n : ℕ => inner ℂ (e n) ((finiteDiagonal ![a, b, c] ∘L finiteDiagonal ![a, b, c]) (e n)))
      (∑ n ∈ Finset.range 3,
        inner ℂ (e n) ((finiteDiagonal ![a, b, c] ∘L finiteDiagonal ![a, b, c]) (e n))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    have hn3 : 3 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    rw [hterm, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  convert hs using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hterm]
  norm_num

private def P (T : ℝ) : ℝ :=
  (1728 * T ^ 4 - 8856 * T ^ 3 + 17529 * T ^ 2 - 12300 * T + 5000) / 5000

private theorem P_eq (T : ℝ) :
    P T = (1728 * T ^ 4 - 8856 * T ^ 3 + 17529 * T ^ 2 - 12300 * T + 5000) / 5000 := rfl

private theorem purity_polynomial (T : ℝ) :
    q0 T ^ 2 + q1 T ^ 2 + q2 T ^ 2 = P T := by
  rw [P_eq]
  unfold q0 q1 q2
  ring

private theorem witness_purity : IsPurityCurve weights vectors P := by
  intro T hT
  rw [witness_output]
  rw [← purity_polynomial]
  exact finiteDiagonal_three_purity (q0 T) (q1 T) (q2 T)

private theorem midpoint_certificate :
    P (39 / 40) * P (197 / 200) < P (49 / 50) ^ 2 := by
  rw [P_eq, P_eq, P_eq]
  norm_num

theorem result : ¬ claim := by
  intro hclaim
  have hnonneg : ∀ i, 0 ≤ weights i := by
    intro i
    change 0 ≤ (![(1 / 100 : ℝ), 3 / 4, 6 / 25] : Fin 3 → ℝ) i
    fin_cases i <;> norm_num
  have hsum : ∑ i, weights i = 1 := by
    change ∑ i : Fin 3, (![(1 / 100 : ℝ), 3 / 4, 6 / 25] : Fin 3 → ℝ) i = 1
    norm_num [Fin.sum_univ_succ]
  have hunit : ∀ i, ‖vectors i‖ = 1 := by
    intro i
    change ‖lp.single (E := fun _ : ℕ => ℂ) 2 (i : ℕ) (1 : ℂ)‖ = 1
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    exact norm_one
  obtain ⟨F, hF, hconv⟩ := hclaim 3 weights vectors hnonneg hsum hunit
  have hx : (39 / 40 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hm : (49 / 50 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hy : (197 / 200 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have heq (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 1) : F T = P T := by
    exact_mod_cast (hF T hT).unique (witness_purity T hT)
  have hc := hconv.2 hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) • (39 / 40 : ℝ) + (1 / 2 : ℝ) • (197 / 200 : ℝ) =
      (49 / 50 : ℝ) := by norm_num
  rw [hmid] at hc
  dsimp only at hc
  rw [heq _ hm, heq _ hx, heq _ hy] at hc
  have hlog : 2 * Real.log (P (49 / 50)) ≤
      Real.log (P (39 / 40)) + Real.log (P (197 / 200)) := by
    simp only [smul_eq_mul] at hc
    linarith
  have hpx : 0 < P (39 / 40) := by rw [P_eq]; norm_num
  have hpm : 0 < P (49 / 50) := by rw [P_eq]; norm_num
  have hpy : 0 < P (197 / 200) := by rw [P_eq]; norm_num
  have hle : P (49 / 50) ^ 2 ≤ P (39 / 40) * P (197 / 200) := by
    apply (Real.log_le_log_iff (pow_pos hpm 2) (mul_pos hpx hpy)).mp
    rw [Real.log_pow, Real.log_mul hpx.ne' hpy.ne']
    norm_num only [Nat.cast_ofNat]
    exact hlog
  exact (not_lt_of_ge hle) midpoint_certificate

end D5.S3.Quantum.QuantumChannels.FockAttenuator.LossPurityLogConvexityRefutation

-- The canonical utility header is a single machine-readable line.
set_option linter.style.longLine false
