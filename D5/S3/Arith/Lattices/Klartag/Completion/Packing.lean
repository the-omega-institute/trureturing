/- GID: D5/S3/Arith/Lattices/Klartag/Completion/Packing
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/Packing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One positive packing constant for every natural dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Completion.PackingBounds

set_option linter.unusedSectionVars false

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Drift
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.Lemma43R
open D5.S3.Arith.Lattices.Klartag.Lemma43R2
open D5.S3.Arith.Lattices.Klartag.Lemma43R3
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Tail
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Completion.Packing

open MeasureTheory
open Matrix
open Finset
open Module
open scoped ENNReal NNReal RealInnerProductSpace
open D5.S3.Arith.Lattices.Klartag
open D5.S3.Arith.Lattices.Klartag.Walk.Increments
open D5.S3.Arith.Lattices.Klartag.Walk.StoppedChain
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2
open D5.S3.Arith.Lattices.Klartag.State.RawDataInst2RW2
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped
open D5.S3.Arith.Lattices.Klartag.Drift.Stopped.DriftStopped8R5
open D5.S3.Arith.Lattices.Klartag.Drift.DriftAccumulated
open D5.S3.Arith.Lattices.Klartag.State.PaddedLawSetupRW2
open D5.S3.Arith.Lattices.Klartag.Tail.TailSideSetup2
open D5.S3.Arith.Lattices.Klartag.Tail.TailAtStepR5W2
open D5.S3.Arith.Lattices.Klartag.Completion.Theorem2R4
open D5.S3.Arith.Lattices.Klartag.Completion.FinalDischarge


noncomputable def Bfam (m : ℕ) : ℝ := 140 / ((m + 1 : ℕ) : ℝ) ^ 2

theorem Bfam_nonneg (m : ℕ) : 0 ≤ Bfam m := by rw [Bfam]; positivity

/-- **The cut index**: one step short of the horizon. -/
noncomputable def Kcut (m : ℕ) : ℕ := ParamsAdopted2.numStepsAdopted2 (m + 1) - 1

theorem Kcut_lt (m : ℕ) (hm : Threshold2.n₁ ≤ m) :
    Kcut m < ParamsAdopted2.numStepsAdopted2 (m + 1) := by
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have := three_le_numStepsAdopted2 (n := m + 1) (by omega)
  rw [Kcut]; omega

theorem Kcut_succ (m : ℕ) (hm : Threshold2.n₁ ≤ m) :
    Kcut m + 1 = ParamsAdopted2.numStepsAdopted2 (m + 1) := by
  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have := three_le_numStepsAdopted2 (n := m + 1) (by omega)
  rw [Kcut]; omega

/-- The shortfall's free parameter `rr`, chosen so that `rr·mAt ≥ (1+c₃)·η` with `mAt ≥ 1/2`. -/
noncomputable def rrAt (n : ℕ) : ℝ :=
  2 * (1 + DriftStopped6c.c3Adopted'' n) * DriftStopped6.etaAdopted n

noncomputable def epsAt (n : ℕ) : ℝ := 1 / Real.sqrt (Real.sqrt (n : ℝ))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The challenge statement, with no hypotheses.** -/
theorem klartag_packing :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let V := EuclideanSpace ℝ (Fin (n + 1))
      ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
        (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
        {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine Theorem2R5.klartag_packing_final_lightB (A := 1) (B := Bfam) one_pos Bfam_nonneg
    (C' := 10000000) (K := Kcut) Kcut_lt ?_
  intro m hm p hp hp0 α hα hn3 hraw hnd g hlight

  have hm1 : 2073600 ≤ m + 1 := by
    have h2 : 2073600 ≤ m := by simpa [Threshold2.n₁] using hm
    omega
  have hnR : (2073600 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hm1
  have hn0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by linarith
  have hKlt := Kcut_lt m hm
  have hKsucc := Kcut_succ m hm
  have hN1 : 1 ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by omega
  have hKleN : Kcut m ≤ ParamsAdopted2.numStepsAdopted2 (m + 1) := by omega
  have hKle : (Kcut m : ℝ) ≤ ((ParamsAdopted2.numStepsAdopted2 (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast hKleN

  have hq37 : (37 : ℝ) ≤ Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := WindowR.qrt_ge hm1
  have hq0 : (0 : ℝ) < Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := by linarith
  have hq4 : Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ^ 4 = ((m + 1 : ℕ) : ℝ) :=
    WindowR.qrt_pow_four hn0.le
  have hqle : Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤ ((m + 1 : ℕ) : ℝ) :=
    qrt_le_self hq37 hq4

  have hc30 := DriftStopped6c.c3_adopted_nonnegative (m + 1)
  have hc3pos := DriftStopped6c.c3Adopted''_pos (n := m + 1) (by omega)
  have hc3eta := DriftStopped6c.c3Adopted''_eta_le hm1
  have hc3q := DriftStopped6c.c3eta_le hm1
  have hη0 : (0 : ℝ) ≤ DriftStopped6.etaAdopted (m + 1) := DriftStopped7.etaAdopted_nonneg
  have hηq := eta_le_qrt hm1
  have hr00 : (0 : ℝ) ≤ DriftStopped6.r0Adopted (m + 1) := DriftStopped7.r0Adopted_nonneg
  have hr0q := r0_le_qrt hm1
  have hmhalf := GoodPathBounds.half_le_mAt hm1 hc3eta
  have hmone := AdoptedConstants95.mAt_le_one (n := m + 1) (by omega) hc30
  have hMone := GoodPathBounds.one_le_MAt hm1 hc30
  have hcq0 := GoodPathBounds.cqAt_nonneg hm1 hc3eta hc30
  have hcqh := DriftStopped6b.cqAt_le_half hm1 hc30 hc3eta
  have ha01 := DriftStopped7.one_le_a0C (n := m + 1) (by omega)
  have ha0u := AdoptedConstants95.a0C_sub_one_le (n := m + 1) (by omega)
  have h4r0 := AdoptedConstants95.four_div_le_r0 (n := m + 1) (by omega)

  have hu0 : (0 : ℝ) ≤ DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1) := by positivity
  have huq : DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)
      ≤ 10 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    have : (8 : ℝ) / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))
        + 2 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))
        = 10 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := by ring
    linarith [hr0q, hc3q, this.le, this.ge]
  have hq10 : (10 : ℝ) / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hq0 (by norm_num)]; linarith
  have hu3 : DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1) ≤ 1 / 3 := by
    linarith
  have hmAtEq : GoodPathBounds.mAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
      = a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) :=
    rfl
  have hMAtEq : GoodPathBounds.MAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
      = a0C (m + 1) + (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) :=
    rfl
  have hmm : (1 : ℝ) / 2 ≤ a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) := by
    rw [hmAtEq] at hmhalf; exact hmhalf
  have hmm1 : a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
      + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) ≤ 1 := by
    rw [hmAtEq] at hmone; exact hmone
  have hmu : 1 - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))
      ≤ a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) := by linarith
  have hMu : GoodPathBounds.MAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
      ≤ 1 + 2 * (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) := by
    rw [hMAtEq]
    have hce : (0 : ℝ) ≤ DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1) :=
      by positivity
    linarith

  have hdd0 := GoodPathBounds.deltaAt_nonneg hm1 hc3eta
  have hddq : GoodPathBounds.deltaAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
      ≤ 2 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    rw [GoodPathBounds.deltaAt, hmAtEq]
    exact delta_le_two_div hq0 hηq hmm
  have hq2 : (2 : ℝ) / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq0 (by norm_num)]; linarith
  have hdd4 : GoodPathBounds.deltaAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)) ≤ 1 / 4 := by
    linarith

  have hrr0 : (0 : ℝ) ≤ rrAt (m + 1) := by rw [rrAt]; positivity
  have hrrq : 2 * rrAt (m + 1) ≤ 12 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
    rw [rrAt]
    exact rr_le_twelve hq0 hηq hc3q
  have hq12 : (12 : ℝ) / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hq0 (by norm_num)]; linarith
  have hrrhalf : rrAt (m + 1) ≤ 1 / 2 := by linarith
  have hrm : (1 + DriftStopped6c.c3Adopted'' (m + 1)) * DriftStopped6.etaAdopted (m + 1)
      ≤ rrAt (m + 1) * (a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))) := by
    rw [rrAt]
    have hnn : (0 : ℝ) ≤ (1 + DriftStopped6c.c3Adopted'' (m + 1))
        * DriftStopped6.etaAdopted (m + 1) := by positivity
    exact rm_ge hnn hmm

  have heps0 : (0 : ℝ) < epsAt (m + 1) := by rw [epsAt]; positivity
  have hepsq : epsAt (m + 1) = 1 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) := rfl
  have hepsle : epsAt (m + 1) ≤ 1 := by
    rw [epsAt, div_le_one hq0]; linarith
  have hepsle5 : epsAt (m + 1) ≤ 1 / 5 := by
    rw [epsAt, div_le_div_iff₀ hq0 (by norm_num)]; linarith

  have hkapup : (1 / 2 + 2 * rrAt (m + 1))
        / (a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
          + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))) ^ 2
      ≤ 1 / 2 + 12 * (DriftStopped6.r0Adopted (m + 1)
          + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))
        + 2 * rrAt (m + 1) :=
    kappa_upper hmu hmm hmm1 hu0 hu3 hrr0 hrrhalf
  have hkaphalf : (1 : ℝ) / 2 ≤ (1 / 2 + 2 * rrAt (m + 1))
      / (a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))) ^ 2 := by
    have h := AdoptedConstants95.kappa_ge_half (n := m + 1) (c₃ := DriftStopped6c.c3Adopted'' (m + 1))
      (rr := rrAt (m + 1)) hm1 hc30 hc3eta hrr0
    rwa [hmAtEq] at h
  have hkap5 : (1 / 2 + 2 * rrAt (m + 1))
      / (a0C (m + 1) - (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))) ^ 2 ≤ 5 := by
    have hq120 : (12 : ℝ) * (10 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ≤ 4 := by
      rw [show (12 : ℝ) * (10 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)))
        = 120 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) by ring, div_le_iff₀ hq0]
      linarith
    have h12 : 12 * (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1)) ≤ 4 := by
      linarith
    linarith
  have hcqlow : 1 / 2 - 4 * (DriftStopped6.r0Adopted (m + 1)
        + DriftStopped6c.c3Adopted'' (m + 1) * DriftStopped6.etaAdopted (m + 1))
      - 3 * GoodPathBounds.deltaAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))
      ≤ GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)) := by
    rw [GoodPathBounds.cqAt]
    exact cq_lower hMone hMu hu0 hu3 hdd0 hdd4

  have hηpos : (0 : ℝ) < DriftStopped6.etaAdopted (m + 1) := eta_pos hn3
  have hh0 : (0 : ℝ) < ParamsAdopted2.stepSizeAdopted2 (m + 1) :=
    TailSideSetup2.stepSizeAdopted2_pos hn3
  have hhne : ParamsAdopted2.stepSizeAdopted2 (m + 1) ≠ 0 := ne_of_gt hh0
  have hcsq := TruncSumMean.cAdopted_sq (n := m + 1) hn3
  have hfr : (finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)
      = (Fintype.card (UT (m + 1)) : ℝ) := by rw [finrank_euclideanSpace]
  have hlt := GoodPathBounds.lt_a0C_of_mAt hm1 hc3eta
  have hlog1 : (1 : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := ChainDrift.log_pos_of_three hn3
  have hlog4 := WindowR.log_le_four_qrt hm1

  have hp1 : 1 < p := Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1.le
  have hpn1 : (1 : ℝ) ≤ ((p ^ (m + 1 - 1) : ℕ) : ℝ) := by
    have : 1 ≤ p ^ (m + 1 - 1) := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have hppos1 : (1 : ℝ) < (p : ℝ) ^ (m + 1) :=
    one_lt_pow₀ (by exact_mod_cast hp1) (by omega)

  have hthetaB : ThetaTight.thetaTight p (m + 1)
      (TailAtStepR5W2.C3 (m + 1) 1 (Bfam m) α) ≤ 2800000 := by
    have hBm : Bfam m = 140 / ((m + 1 : ℕ) : ℝ) ^ 2 := rfl
    rw [hBm]
    exact thetaTight_le_2800000 hm1 hα hraw.tiling_defect hraw.alpha_norm hp1R hpn1 hppos1
  have hThT0 : (0 : ℝ) < 10000 * ((m + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hBmul : Bfam m * (2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2)) = 2800000 := by
    rw [Bfam]; field_simp; ring
  have h₁ : Theorem2R4.θ3 1 (Bfam m) p m α
      ≤ ENNReal.ofReal 1 * ENNReal.ofReal 2800000 := by
    rw [Theorem2R4.θ3, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1), one_mul]
    exact ENNReal.ofReal_le_ofReal hthetaB
  have h₂ : Theorem2R4.θ3 1 (Bfam m) p m α
      ≤ ENNReal.ofReal (Bfam m) * ENNReal.ofReal (2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [Theorem2R4.θ3, ← ENNReal.ofReal_mul (Bfam_nonneg m), hBmul]
    exact ENNReal.ofReal_le_ofReal hthetaB

  have hcnt := TailWiring.hcnt_win (p := p) (m := m) (α := α) (A := 1) (B := Bfam m)
    (Θ := 2800000) (ΘT := 10000 * ((m + 1 : ℕ) : ℝ) ^ 2)
    (c₃ := DriftStopped6c.c3Adopted'' (m + 1)) (K := Kcut m)
    hm hα one_pos (Bfam_nonneg m) g hraw hnd hKlt hc3pos (by norm_num) hThT0 h₁ h₂ hlight
  have hpcnt0 : (0 : ℝ) ≤ (2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0)
      / DriftStopped6c.c3Adopted'' (m + 1) := by positivity
  have hpcq : (2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / DriftStopped6c.c3Adopted'' (m + 1)
      ≤ 2 * 10000 / Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)) ^ 3 :=
    count_ratio_q hm1 (by norm_num) (le_refl _)

  have hlog0 : (0 : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by linarith
  have hpbad0 : (0 : ℝ) ≤ GoodPathBounds.failTotal (m + 1)
      ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / DriftStopped6c.c3Adopted'' (m + 1)) :=
    failTotal_nonneg hn3 hpcnt0
  have hfi := failTotal_le_inv hm1
    ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / DriftStopped6c.c3Adopted'' (m + 1))

  have hξm : ∀ j, Measurable
      (ChainSetup.step (ι := UT (m + 1)) (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1)) j) :=
    fun j => ChainSetup.measurable_step _ j
  have hGms : ∀ k, MeasurableSet[ChainSetup.filtration
        (F := EuclideanSpace ℝ (UT (m + 1))) k]
      (stateGood (qC α) (windowOfR2 α p m g) (A0C (m + 1))
        (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1)))
        (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
        (DriftStopped6c.c3Adopted'' (m + 1)) k) :=
    fun k => DriftInputsStopped.measurableSet_stateGood_step _ _ _ _ k
  have hτ : Measurable (tau (qC α) (windowOfR2 α p m g) (A0C (m + 1))
      (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1)))
      (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6.r0Adopted (m + 1))
      (DriftStopped6c.c3Adopted'' (m + 1)) (ParamsAdopted2.numStepsAdopted2 (m + 1))) :=
    DriftStopped5.measurable_tau
      (ChainSetup.filtration (F := EuclideanSpace ℝ (UT (m + 1)))) hGms _
  have hfail : (ChainSetup.gaussPath (EuclideanSpace ℝ (UT (m + 1)))).real
      (GoodPathBounds.goodCut 1 (ChainSetup.coord 0)
        (ChainSetup.step (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1)))
        (6 * 1 * 1 * Real.sqrt ((m + 1 : ℕ) : ℝ))
        (ParamsAdopted2.numStepsAdopted2 (m + 1)) (DriftStopped6.etaAdopted (m + 1))
        (qC α) (windowOfR2 α p m g) (A0C (m + 1)) (DriftStopped6.r0Adopted (m + 1))
        (DriftStopped6c.c3Adopted'' (m + 1)) (Kcut m))ᶜ
      ≤ GoodPathBounds.failTotal (m + 1)
        ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0)
          / DriftStopped6c.c3Adopted'' (m + 1)) :=
    goodCut_fail_le hn3 hcnt
  have hSlight := TailWiring.hS_light_win (p := p) (m := m) (α := α) (A := 1) (B := Bfam m)
    (Θ := 2800000) (ΘT := 10000 * ((m + 1 : ℕ) : ℝ) ^ 2) (K := Kcut m)
    hm hα one_pos (Bfam_nonneg m) g hraw hnd hKleN (by norm_num) hThT0 h₁ h₂ hlight

  have hkap0 : (0 : ℝ) ≤ ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2) := by linarith
  have hEa : (DriftAccumulated.EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) ≤ 1 := by
    rw [DriftAccumulated.EaccAt_eq]
    have hid : (DriftStopped6c.c3Adopted'' (m + 1)) * ((DriftStopped6.etaAdopted (m + 1)) / GoodPathBounds.mAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)))
        = ((DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1))) / GoodPathBounds.mAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)) := by ring
    rw [hid, div_le_one (by linarith)]
    linarith
  have hCB := DriftStopped6b.slackHyp_at hm1 hc30 hc3eta
  rw [DriftStopped4.SlackHyp, DriftStopped6.slackAdopted] at hCB
  have hce0 : (0 : ℝ) ≤ (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)) := by positivity
  have hsq2 : (2 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)))) ^ 2 = 4 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 2 := by rw [div_pow]; norm_num
  have hxx : ((DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1))) ^ 2 ≤ 4 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 2 :=
    hsq2 ▸ pow_le_pow_left₀ hce0 hc3q 2
  have hGle : ((Kcut m : ℝ) * (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1) ^ 2 * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)))) ≤ 64 * (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) := by
    have hassoc : ((Kcut m : ℝ) * (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1) ^ 2 * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ))))
        = ((Kcut m : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1))
          * (Fintype.card (UT (m + 1)) : ℝ) := by rw [hcsq, hfr]; ring
    have hNh := ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn3
    have hKh : (Kcut m : ℝ) * ParamsAdopted2.stepSizeAdopted2 (m + 1)
        ≤ ChainDrift.horizon (m + 1) := by
      rw [← hNh]; exact mul_le_mul_of_nonneg_right hKle hh0.le
    have hcard0 : (0 : ℝ) ≤ (Fintype.card (UT (m + 1)) : ℝ) := Nat.cast_nonneg _
    have hstep := mul_le_mul_of_nonneg_right hKh hcard0
    have hhc := horizon_mul_card_le (n := m + 1) hm1
    rw [hassoc]
    linarith
  have hG0 : (0 : ℝ) ≤ ((Kcut m : ℝ) * (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1) ^ 2 * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)))) := by positivity

  have hqpc := mul_le_mul_of_nonneg_left hpcq hq0.le
  have hid1 : (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (2 * 10000 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 3) = 20000 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 2 := by
    field_simp; ring
  have hq2b : (20000 : ℝ) / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 2 ≤ 15 :=
    twenty_k_div_sq_le hq37
  have hqfi := mul_le_mul_of_nonneg_left hfi hq0.le
  have hid2 : (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1))) + 1 / (1000 * ((m + 1 : ℕ) : ℝ)))
      = (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1))) + (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (1 / (1000 * ((m + 1 : ℕ) : ℝ))) := by ring
  have hqn : (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (1 / (1000 * ((m + 1 : ℕ) : ℝ))) ≤ 1 / 1000 := by
    rw [show (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (1 / (1000 * ((m + 1 : ℕ) : ℝ)))
      = (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) / (1000 * ((m + 1 : ℕ) : ℝ)) by ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [hqle]
  have hpb : (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) * (GoodPathBounds.failTotal (m + 1) ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1)))) ≤ 16 := by
    linarith [hqfi, hid2.le, hid2.ge, hqpc, hid1.le, hid1.ge, hq2b, hqn]

  have hgap : ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2) * (1 + epsAt (m + 1)) - (GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) ≤ 200 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) := by
    have hinvid : ∀ c : ℝ, c / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) = c * (1 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)))) := fun c => by ring
    have hkeps := mul_le_mul_of_nonneg_right hkap5 heps0.le
    rw [hepsq] at hkeps
    rw [hepsq, hinvid 200]
    rw [hinvid 10] at huq
    rw [hinvid 12] at hrrq
    rw [hinvid 2] at hddq
    exact gap_le (by positivity) hkapup hcqlow huq hrrq hddq hkeps

  refine ⟨((Kcut m : ℝ) * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ))
      - 2800000 / ParamsAdopted2.stepSizeAdopted2 (m + 1)
      - ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)) * ((Kcut m : ℝ) * GoodPathBounds.failTotal (m + 1) ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1))))), ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1))), (ChainWiring.logDet (A0C (m + 1)) - ((DriftChargeTotal.driftCen (n := m + 1) (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))
          (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1)) ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2) (epsAt (m + 1)) (Kcut m)) + 1) - 1), 20, ?_, ?_, ?_, ?_, ?_⟩
  · exact hS_of_intWeight_cut hh0 hKlt hξm hτ hSlight hfail
  · exact hcnt
  · refine le_trans (ChainShortfall.hshort_at_chain (n := m + 1) (xs := xOf α)
      (W := windowOfR2 α p m g) (A₀ := A0C (m + 1)) (η := (DriftStopped6.etaAdopted (m + 1)))
      (a₀ := a0C (m + 1)) (r₀ := (DriftStopped6.r0Adopted (m + 1))) (c₃ := (DriftStopped6c.c3Adopted'' (m + 1)))
      (rr := rrAt (m + 1)) (ε := epsAt (m + 1)) (cstep := D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))
      (t := 1) (t' := 1) (s' := 1) (N := ParamsAdopted2.numStepsAdopted2 (m + 1))
      (K := Kcut m)
      hN1 hξm hτ (kSet_A0C_win hα hn3) (hq_win hα hn3) (hne_win hα hn3)
      (StateSupply.symMat_A0C (m + 1)) hη0 hr00 hc30 hlt hrr0 hrrhalf hrm heps0
      (by norm_num) (by norm_num) (by norm_num)) ?_
    refine shortfall_le_twenty ?_ (vterm_le hm1 hKle hmm) ?_ (wterm_le hm1 hKle) ?_ ?_
    · positivity
    · positivity
    · have h1 : (0 : ℝ) ≤ 1 + epsAt (m + 1) := by linarith
      exact mul_nonneg hkap0 h1
    · exact kp_le_six hkap0 hkap5 heps0.le hepsle5
  · exact hLb_of_bounds_cut hm1 hkaphalf hkap0 heps0 (by norm_num) (by norm_num) hKsucc
      (by norm_num)
  · have hcenle := driftCen_le (n := m + 1) hn3 (c := D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))
      (κ := ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2)) (ε := epsAt (m + 1)) (c₃ := (DriftStopped6c.c3Adopted'' (m + 1))) (η := (DriftStopped6.etaAdopted (m + 1)))
      hηpos hkap0 heps0 (Kcut m)
    have hnum := num_le_const (qv := (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ)))) hq37 hepsq hcenle hgap hG0 hGle hkap0 hkap5
      (by positivity) hxx hcq0 hcqh (by norm_num) (le_refl (2800000 : ℝ)) hpbad0 hpb
      hEa hCB (le_refl (1 : ℝ)) (le_refl (1 : ℝ)) (le_refl (20 : ℝ))
    refine budget_lt_one'' (Anum := 1450000) (Bden := 9999000) (Fb := 2 / 5)
      (by norm_num) (by norm_num) ?_ ?_ ?_ (by norm_num)
    · have hid : DriftAccumulated.driftRHS_acc (m + 1) (A0C (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1)) (DriftAccumulated.EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) ((Kcut m : ℝ) * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ))
      - 2800000 / ParamsAdopted2.stepSizeAdopted2 (m + 1)
      - ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)) * ((Kcut m : ℝ) * GoodPathBounds.failTotal (m + 1) ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1)))))
            - (ChainWiring.logDet (A0C (m + 1)) - ((DriftChargeTotal.driftCen (n := m + 1) (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))
          (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1)) ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2) (epsAt (m + 1)) (Kcut m)) + 1) - 1) + 20
          = (DriftChargeTotal.driftCen (n := m + 1) (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1))
          (DriftStopped6.etaAdopted (m + 1)) (DriftStopped6c.c3Adopted'' (m + 1)) ((1 / 2 + 2 * rrAt (m + 1)) / (a0C (m + 1) - ((DriftStopped6.r0Adopted (m + 1)) + (DriftStopped6c.c3Adopted'' (m + 1)) * (DriftStopped6.etaAdopted (m + 1)))) ^ 2) (epsAt (m + 1)) (Kcut m)) - (GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) * ((Kcut m : ℝ) * (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1) ^ 2 * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)))) + (GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) * 2800000 + (GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) * ((Kcut m : ℝ) * (D5.S3.Arith.Lattices.Klartag.cAdopted (m + 1) ^ 2 * ((finrank ℝ (EuclideanSpace ℝ (UT (m + 1))) : ℝ)))) * (GoodPathBounds.failTotal (m + 1) ((2 * (10000 * ((m + 1 : ℕ) : ℝ) ^ 2) + 0) / (DriftStopped6c.c3Adopted'' (m + 1))))
            + (DriftAccumulated.EaccAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) + (DriftStopped4.C₁ (m + 1) (GoodPathBounds.mAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1))) (GoodPathBounds.cqAt (m + 1) (DriftStopped6c.c3Adopted'' (m + 1)))
            * (2 * D5.S3.Arith.Lattices.Klartag.B_adopted (m + 1))) + 1 + 1 + 20 := by
        rw [DriftAccumulated.driftRHS_acc, hcsq]
        exact rhs_identity hhne
      rw [hid]
      exact hnum
    · have hcenge := driftCen_ge_cut (n := m + 1) (c₃ := (DriftStopped6c.c3Adopted'' (m + 1))) hm1 hkaphalf hkap0 heps0 hKsucc
      have hA0 := AdoptedConstants95.logDet_A0C_le (n := m + 1) hn3
      have hsmall := log_div_le (n := m + 1) hm1
      linarith
    · have hpc3b : 2 * 10000 / (Real.sqrt (Real.sqrt ((m + 1 : ℕ) : ℝ))) ^ 3 ≤ 396 / 1000 :=
        twenty_k_div_cube_le hq37
      have hinvn : 1 / (1000 * ((m + 1 : ℕ) : ℝ)) ≤ 1 / 1000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith [hfi, hpcq, hpc3b, hinvn]

end D5.S3.Arith.Lattices.Klartag.Completion.Packing

#print axioms D5.S3.Arith.Lattices.Klartag.Completion.Packing.klartag_packing
