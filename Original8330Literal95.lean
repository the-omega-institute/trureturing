import Original8330Literal94Repair1
import D5.S3.Observer.MetricGeometry.ArithmeticHorizon
import D5.S1.Depth.ContinuedFractions.IrrationalSlopeFaithfulness
import D5.S3.ObserverMemory.Trajectories.FibonacciNearReturn
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Find

/-!
Transient SOURCE-ONLY candidate. No parser, elaborator, kernel, build, test, or
inspector has been run. This is not a retained library declaration or proof credit.
Project 7716a33a25feda45ad185b97597f8a5cdf89a66d; Lean 4.35.0;
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
Original theory: 5c45065d8764eb2a31c735593cfdba54f3ac5130, definitions 8.1/9.1,
theorem 9.5. The imported transient 9.4 source has SHA256
5cfc1797ca0849100da59d16c55289f11c6b21a13598b6bf2827a5ec30a6454a.
Its native acceptance remains pending and is a dependency of this entire file.
-/

namespace Original8330Literal95SourceOnly

noncomputable section

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality (runWord)
open D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality (run_unit_word)
open D5.S3.Observer.MetricGeometry.BinaryShiftExactBitLaw (HasFiniteHorizonPredictor)
open D5.S3.Observer.MetricGeometry.ArithmeticHorizon (Psi torusNorm)
open D5.S1.Depth.ContinuedFractions.IrrationalSlopeFaithfulness
open D5.S3.ObserverMemory.Trajectories.FibonacciNearReturn

private abbrev F : Unit → UnitAddCircle → UnitAddCircle :=
  fun _ x => x + ((Real.goldenRatio⁻¹ : ℝ) : UnitAddCircle)

private noncomputable abbrev o (x : UnitAddCircle) : ℂ :=
  (AddCircle.toCircle (T := (1 : ℝ)) x : ℂ)

private abbrev P (H : ℕ) (ε : ℝ) (s : ℕ) : Prop :=
  HasFiniteHorizonPredictor F o H ε s

private noncomputable abbrev cutoff (H : ℕ) (ε : ℝ) : ℝ :=
  max (max 2 (2 * Real.pi / ε)) (Real.sqrt (4 * Real.pi * (H : ℝ) / ε))

private theorem inverse_identity : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
  rw [Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

-- Original displacement q is preserved throughout. In particular q=1 is
-- handled directly and never replaced by a reduced rational denominator.
private theorem golden_separation (q : ℕ) (hq : 0 < q) :
    1 / (3 * (q : ℝ)) < torusNorm ((q : ℝ) * Real.goldenRatio⁻¹) := by
  have hsqrt : Real.sqrt 5 < (5 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  by_cases hq1 : q = 1
  · subst q
    have hφ : (3 / 2 : ℝ) < Real.goldenRatio ∧ Real.goldenRatio < 5 / 3 := by
      dsimp only [Real.goldenRatio]
      constructor <;>
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    have hone : ((1 : ℝ) : UnitAddCircle) = 0 := by
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨1, by norm_num⟩
    have hcenter :
        ‖((Real.goldenRatio⁻¹ - 1 : ℝ) : UnitAddCircle)‖ =
          |Real.goldenRatio⁻¹ - 1| := by
      apply (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr
      have hsmall : |Real.goldenRatio⁻¹ - 1| ≤ (1 / 2 : ℝ) := by
        rw [inverse_identity]
        exact abs_le.mpr ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
      simpa using hsmall
    have hn : torusNorm Real.goldenRatio⁻¹ = 2 - Real.goldenRatio := by
      dsimp only [torusNorm]
      have hcenter' : ‖((Real.goldenRatio⁻¹ : ℝ) : UnitAddCircle)‖ =
          |Real.goldenRatio⁻¹ - 1| := by
        simpa only [AddCircle.coe_sub, hone, sub_zero] using hcenter
      rw [hcenter', inverse_identity, abs_of_neg (by linarith [hφ.2])]
      ring
    simpa only [Nat.cast_one, one_mul, hn] using
      (show (1 : ℝ) / (3 * 1) < 2 - Real.goldenRatio by linarith [hφ.2])
  · have hq2 : 2 ≤ q := by omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    let r : ℤ := round ((q : ℝ) * Real.goldenRatio⁻¹)
    have hgap :=
      (irrational_slope_faithfulness Real.goldenRatio Real.goldenRatio_irrational).2.2.2
        q hq ((q : ℤ), -(q : ℤ) - r) (0, 0)
        (by simp)
        (by
          intro h
          have hfirst : (q : ℤ) = 0 := congrArg Prod.fst h
          have hz : q = 0 := by exact_mod_cast hfirst
          omega)
    have heq :
        |slopeEncoding Real.goldenRatio ((q : ℤ), -(q : ℤ) - r) -
          slopeEncoding Real.goldenRatio (0, 0)| =
            torusNorm ((q : ℝ) * Real.goldenRatio⁻¹) := by
      rw [torusNorm, UnitAddCircle.norm_eq]
      dsimp only [slopeEncoding, r]
      push_cast
      rw [inverse_identity]
      congr 1
      ring
    rw [heq] at hgap
    have hden : Real.sqrt 5 * (q : ℝ) + 1 < 3 * (q : ℝ) := by
      have hqR2 : (2 : ℝ) ≤ q := by exact_mod_cast hq2
      nlinarith [mul_lt_mul_of_pos_right hsqrt hqR]
    exact (one_div_lt_one_div_of_lt (by positivity) hden).trans
      (by simpa only [finitePrecisionGap] using hgap)

-- The least Fibonacci crossing is chosen before applying the exact 9.4 clock.
private theorem fibonacci_feasible (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 3 ≤ m ∧ cutoff H ε ≤ (Nat.fib m : ℝ) ∧
      (Nat.fib (m - 1) : ℝ) < cutoff H ε ∧
      (Nat.fib m : ℝ) < 2 * cutoff H ε ∧ P H ε (Nat.fib m) := by
  classical
  let T := cutoff H ε
  have hT2 : (2 : ℝ) ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt T
  have hex : ∃ m : ℕ, T ≤ (Nat.fib m : ℝ) := by
    refine ⟨N + 5, ?_⟩
    have hf := Nat.le_fib_self (n := N + 5) (by omega)
    have hfR : ((N + 5 : ℕ) : ℝ) ≤ (Nat.fib (N + 5) : ℝ) := by exact_mod_cast hf
    have hNN : (N : ℝ) ≤ ((N + 5 : ℕ) : ℝ) := by
      exact_mod_cast (show N ≤ N + 5 by omega)
    exact hN.le.trans (hNN.trans hfR)
  let m := Nat.find hex
  have hcross : T ≤ (Nat.fib m : ℝ) := Nat.find_spec hex
  have hm : 3 ≤ m := by
    by_contra h
    have hsmall : m ≤ 2 := by omega
    have hfsmall : Nat.fib m ≤ 1 := by simpa using Nat.fib_mono hsmall
    have hfR : (Nat.fib m : ℝ) ≤ 1 := by exact_mod_cast hfsmall
    linarith
  have hprevious : (Nat.fib (m - 1) : ℝ) < T := by
    exact lt_of_not_ge (Nat.find_min hex (show m - 1 < Nat.find hex by change m - 1 < m; omega))
  have hidx : m - 2 + 2 = m := by omega
  have hidx' : m - 2 + 1 = m - 1 := by omega
  have hrec := Nat.fib_add_two (n := m - 2)
  rw [hidx, hidx'] at hrec
  have hmono : Nat.fib (m - 2) ≤ Nat.fib (m - 1) := Nat.fib_mono (by omega)
  have htwice : Nat.fib m ≤ 2 * Nat.fib (m - 1) := by omega
  have hupper : (Nat.fib m : ℝ) < 2 * T := by
    have ht : (Nat.fib m : ℝ) ≤ 2 * (Nat.fib (m - 1) : ℝ) := by exact_mod_cast htwice
    linarith
  let q := Nat.fib m
  let p := Nat.fib (m - 1)
  have hq : 0 < q := Nat.fib_pos.mpr (by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := hqR.ne'
  have hm1 : 1 ≤ m := by omega
  have hidx'' : m - 1 + 1 = m := by omega
  have hpower : Real.goldenRatio * (q : ℝ) + (p : ℝ) = Real.goldenRatio ^ m := by
    simpa only [hidx'', q, p] using Real.goldenRatio_mul_fib_succ_add_fib (m - 1)
  have hpowerpos : 0 < Real.goldenRatio ^ m := pow_pos Real.goldenRatio_pos _
  have hbig : (q : ℝ) < Real.goldenRatio ^ m := by
    have hmul := mul_lt_mul_of_pos_right Real.one_lt_goldenRatio hqR
    have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    nlinarith
  have hdefect : |(q : ℝ) / Real.goldenRatio - (p : ℝ)| =
      1 / Real.goldenRatio ^ m := by
    have hd := fibonacci_near_return.2.2.1 m hm1
    simpa only [fibonacciReturnDefect, q, p, zpow_neg, zpow_natCast, one_div] using hd
  have hfrac : |Real.goldenRatio⁻¹ - (p : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 := by
    calc
      _ = |((q : ℝ) / Real.goldenRatio - (p : ℝ)) / (q : ℝ)| := by
        congr 1
        field_simp [hqne, Real.goldenRatio_ne_zero]
        <;> ring
      _ = (1 / Real.goldenRatio ^ m) / (q : ℝ) := by
        rw [abs_div, hdefect, abs_of_pos hqR]
      _ < (1 / (q : ℝ)) / (q : ℝ) :=
        div_lt_div_of_pos_right (one_div_lt_one_div_of_lt hqR hbig) hqR
      _ = 1 / (q : ℝ) ^ 2 := by field_simp [hqne] <;> ring
  have hgrid : 2 * Real.pi / ε ≤ (q : ℝ) :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hcross)
  have hsqrt : Real.sqrt (4 * Real.pi * (H : ℝ) / ε) ≤ (q : ℝ) :=
    (le_max_right _ _).trans hcross
  have hfirst : Real.pi / (q : ℝ) ≤ ε / 2 := by
    apply (div_le_iff₀ hqR).mpr
    have hg := (div_le_iff₀ hε).mp hgrid
    nlinarith
  have hsecond : 2 * Real.pi * (H : ℝ) / (q : ℝ) ^ 2 ≤ ε / 2 := by
    have hsq := (Real.sqrt_le_iff.mp hsqrt).2
    have hscale := (div_le_iff₀ hε).mp hsq
    apply (div_le_iff₀ (sq_pos_of_pos hqR)).mpr
    nlinarith
  have herror : Real.pi / (q : ℝ) + 2 * Real.pi * (H : ℝ) *
      |Real.goldenRatio⁻¹ - ((p : ℤ) : ℝ) / (q : ℝ)| ≤ ε := by
    have hc : (0 : ℝ) ≤ 2 * Real.pi * (H : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hfrac.le hc
    simp only [Int.cast_natCast]
    have hsecond' : 2 * Real.pi * (H : ℝ) * (1 / (q : ℝ) ^ 2) ≤ ε / 2 := by
      simpa only [div_eq_mul_inv, one_div, one_mul] using hsecond
    linarith
  have hclock := Original8330Literal94SourceOnly.full_exact_application
    Real.goldenRatio⁻¹ (p : ℤ) q hq H
  rcases hclock with ⟨_, _, _, e, G, h, _, _, _, _, _, hpred⟩
  have hfeasible : P H ε q := by
    rcases hpred with ⟨S, finiteS, nonemptyS, hcard, e', G', h', herr⟩
    refine ⟨S, finiteS, nonemptyS, hcard, e', G', h', ?_⟩
    intro x w hw
    simpa only [F, o] using (herr x w hw).trans herror
  exact ⟨m, hm, hcross, hprevious, hupper, hfeasible⟩

private theorem actual_machine_lower {H s : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hεh : ε < 1 / 2) (hp : P H ε s) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ s ∧ P H ε r ∧
      (H : ℝ) < (r : ℝ) + 3 * (Real.arcsin ε / Real.pi) * (r : ℝ) ^ 2 := by
  classical
  rcases hp with ⟨S, finiteS, nonemptyS, hcard, e, G, h, herr⟩
  letI : Fintype S := finiteS
  letI : Nonempty S := nonemptyS
  let r := Fintype.card S
  have hr : 1 ≤ r := Fintype.card_pos
  have hG : G = fun _ : Unit => G () := by funext u; cases u; rfl
  have accuracy (n : ℕ) (hn : n ≤ H) :
      ‖h (((G ())^[n]) (e 0)) -
        (AddCircle.toCircle (T := (1 : ℝ))
          (0 + n • ((Real.goldenRatio⁻¹ : ℝ) : UnitAddCircle)) : ℂ)‖ ≤ ε := by
    have hw := herr 0 (List.replicate n ()) (by simpa using hn)
    rw [hG] at hw
    simpa only [F, o, run_unit_word, List.length_replicate,
      add_right_iterate_apply, dist_eq_norm] using hw
  have hα : Irrational Real.goldenRatio⁻¹ :=
    irrational_inv_iff.mpr Real.goldenRatio_irrational
  have hbound := D5.S3.Observer.MetricGeometry.ArithmeticHorizon.finite_predictor_horizon
    (G ()) h (e 0) 0 Real.goldenRatio⁻¹ ε hα hε hεh H accuracy
  have hPsi : Psi Real.goldenRatio⁻¹ r ≤ 3 * (r : ℝ) ^ 2 := by
    rw [Psi, dif_pos hr]
    apply (Finset.sup'_le_iff
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hr⟩⟩
      (fun p : ℕ => (p : ℝ) / torusNorm ((p : ℝ) * Real.goldenRatio⁻¹))).mpr
    intro p hp
    obtain ⟨hp1, hpr⟩ := Finset.mem_Icc.mp hp
    have hp0 : 0 < p := by omega
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    have hsep := golden_separation p hp0
    have hnpos : 0 < torusNorm ((p : ℝ) * Real.goldenRatio⁻¹) :=
      (by positivity : (0 : ℝ) < 1 / (3 * (p : ℝ))).trans hsep
    have hrat : (p : ℝ) / torusNorm ((p : ℝ) * Real.goldenRatio⁻¹) ≤
        3 * (p : ℝ) ^ 2 := by
      apply (div_le_iff₀ hnpos).mpr
      have hscaled := (div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * (p : ℝ))).mp hsep
      have hmul := mul_le_mul_of_nonneg_left hscaled.le hpR.le
      nlinarith
    have hprR : (p : ℝ) ≤ r := by exact_mod_cast hpr
    have hsquare : (p : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 :=
      (sq_le_sq₀ hpR.le (Nat.cast_nonneg r)).mpr hprR
    exact hrat.trans (mul_le_mul_of_nonneg_left hsquare (by norm_num))
  have ha : 0 ≤ Real.arcsin ε / Real.pi :=
    (div_pos (Real.arcsin_pos.mpr hε) Real.pi_pos).le
  refine ⟨r, hr, hcard, ⟨S, finiteS, nonemptyS, le_rfl, e, G, h, herr⟩, ?_⟩
  calc
    (H : ℝ) < (r : ℝ) + (Real.arcsin ε / Real.pi) * Psi Real.goldenRatio⁻¹ r := hbound
    _ ≤ (r : ℝ) + (Real.arcsin ε / Real.pi) * (3 * (r : ℝ) ^ 2) := by gcongr
    _ = (r : ℝ) + 3 * (Real.arcsin ε / Real.pi) * (r : ℝ) ^ 2 := by ring

private theorem logarithm_sqrt (u : ℝ) (hu : 0 < u) :
    Real.logb 2 (Real.sqrt u) = (1 / 2 : ℝ) * Real.logb 2 u := by
  rw [Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hu]

-- This join is used only after its two exact bounds have been established for
-- the same minimum. Its hypotheses are discharged in the closed root below.
private theorem asymptotic_join (ε : ℝ) (hε : 0 < ε) (H s : ℕ)
    (hs : 1 ≤ s)
    (hlower : (H : ℝ) < (s : ℝ) + 3 * (Real.arcsin ε / Real.pi) * (s : ℝ) ^ 2)
    (hupper : (s : ℝ) < 2 * cutoff H ε) (hH : 1 ≤ H) :
    let a := Real.arcsin ε / Real.pi
    let K := 1 + 3 * a
    let B := max (max 2 (2 * Real.pi / ε)) (Real.sqrt (4 * Real.pi / ε))
    Real.sqrt (H : ℝ) / Real.sqrt K < (s : ℝ) ∧
      (s : ℝ) < 2 * B * Real.sqrt (H : ℝ) ∧
      -(1 / 2 : ℝ) * Real.logb 2 K <
        (⌈Real.logb 2 (s : ℝ)⌉ : ℝ) - (1 / 2 : ℝ) * Real.logb 2 (H : ℝ) ∧
      (⌈Real.logb 2 (s : ℝ)⌉ : ℝ) - (1 / 2 : ℝ) * Real.logb 2 (H : ℝ) <
        1 + Real.logb 2 (2 * B) := by
  let a := Real.arcsin ε / Real.pi
  let K := 1 + 3 * a
  let B := max (max 2 (2 * Real.pi / ε)) (Real.sqrt (4 * Real.pi / ε))
  have ha : 0 < a := div_pos (Real.arcsin_pos.mpr hε) Real.pi_pos
  have hK : 0 < K := by dsimp only [K]; positivity
  have hB2 : (2 : ℝ) ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB2
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hspos : (0 : ℝ) < s := by linarith
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  have hKsqrt : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hHsqrt : 0 < Real.sqrt (H : ℝ) := Real.sqrt_pos.mpr hHpos
  have hHsqrt1 : 1 ≤ Real.sqrt (H : ℝ) := by
    apply (Real.le_sqrt (by norm_num) hHpos.le).mpr
    simpa using hHR
  have hHK : (H : ℝ) < K * (s : ℝ) ^ 2 := by
    have hss : (s : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
    change (H : ℝ) < (s : ℝ) + 3 * a * (s : ℝ) ^ 2 at hlower
    dsimp only [K]
    nlinarith
  have hsqrt : Real.sqrt (H : ℝ) < Real.sqrt K * (s : ℝ) := by
    apply (Real.sqrt_lt hHpos.le (mul_nonneg hKsqrt.le hspos.le)).mpr
    calc
      (H : ℝ) < K * (s : ℝ) ^ 2 := hHK
      _ = (Real.sqrt K * (s : ℝ)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hK.le]
  have hl : Real.sqrt (H : ℝ) / Real.sqrt K < (s : ℝ) := by
    exact (div_lt_iff₀ hKsqrt).mpr (by simpa only [mul_comm] using hsqrt)
  have hBB : B ≤ B * Real.sqrt (H : ℝ) := by nlinarith
  have hT : cutoff H ε ≤ B * Real.sqrt (H : ℝ) := by
    apply max_le
    · apply max_le
      · exact hB2.trans hBB
      · exact ((le_max_right _ _).trans (le_max_left _ _)).trans hBB
    · have hfactor : Real.sqrt (4 * Real.pi * (H : ℝ) / ε) =
          Real.sqrt (4 * Real.pi / ε) * Real.sqrt (H : ℝ) := by
        rw [show 4 * Real.pi * (H : ℝ) / ε = (4 * Real.pi / ε) * (H : ℝ) by ring,
          Real.sqrt_mul (by positivity)]
      rw [hfactor]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hHsqrt.le
  have hu : (s : ℝ) < 2 * B * Real.sqrt (H : ℝ) := by
    exact hupper.trans_le (by nlinarith)
  have hcl : Real.logb 2 (s : ℝ) ≤ (⌈Real.logb 2 (s : ℝ)⌉ : ℝ) := Int.le_ceil _
  have hcu : (⌈Real.logb 2 (s : ℝ)⌉ : ℝ) < Real.logb 2 (s : ℝ) + 1 :=
    Int.ceil_lt_add_one _
  have hll := Real.logb_lt_logb (b := 2) (by norm_num)
    (div_pos hHsqrt hKsqrt) hl
  rw [Real.logb_div hHsqrt.ne' hKsqrt.ne',
    logarithm_sqrt (H : ℝ) hHpos, logarithm_sqrt K hK] at hll
  have hlu := Real.logb_lt_logb (b := 2) (by norm_num) hspos hu
  rw [Real.logb_mul (by positivity : (2 * B : ℝ) ≠ 0) hHsqrt.ne',
    logarithm_sqrt (H : ℝ) hHpos] at hlu
  exact ⟨hl, hu, by linarith, by linarith⟩

-- ONE closed target: eps is arbitrary in the original interval; a single family
-- of actual attained minima covers every natural H, including H=0. No machine
-- accuracy, approximation, feasibility, minimum, or asymptotic bridge is a premise.
theorem full_exact_application (ε : ℝ) (hε : 0 < ε) (hεh : ε < 1 / 2) :
    let a := Real.arcsin ε / Real.pi
    let K := 1 + 3 * a
    let B := max (max 2 (2 * Real.pi / ε)) (Real.sqrt (4 * Real.pi / ε))
    0 < K ∧ 0 < B ∧
      ∃ s : ℕ → ℕ, ∀ H : ℕ,
        IsLeast {k : ℕ | HasFiniteHorizonPredictor
          (fun (_ : Unit) (x : UnitAddCircle) => x + ((Real.goldenRatio⁻¹ : ℝ) : UnitAddCircle))
          (fun x => (AddCircle.toCircle (T := (1 : ℝ)) x : ℂ)) H ε k} (s H) ∧
        (∃ (S : Type) (finiteS : Fintype S), Nonempty S ∧
          @Fintype.card S finiteS = s H ∧
          ∃ (e : UnitAddCircle → S) (G : Unit → S → S) (h : S → ℂ),
            ∀ (x : UnitAddCircle) (w : List Unit), w.length ≤ H →
              dist (h (runWord G w (e x)))
                (AddCircle.toCircle (T := (1 : ℝ))
                  (runWord (fun (_ : Unit) (y : UnitAddCircle) =>
                    y + ((Real.goldenRatio⁻¹ : ℝ) : UnitAddCircle)) w x) : ℂ) ≤ ε) ∧
        1 ≤ s H ∧
        (H : ℝ) < (s H : ℝ) + 3 * a * (s H : ℝ) ^ 2 ∧
        (s H : ℝ) < 2 * max (max 2 (2 * Real.pi / ε))
          (Real.sqrt (4 * Real.pi * (H : ℝ) / ε)) ∧
        (0 ≤ (⌈Real.logb 2 (s H : ℝ)⌉ : ℝ) - Real.logb 2 (s H : ℝ) ∧
          (⌈Real.logb 2 (s H : ℝ)⌉ : ℝ) - Real.logb 2 (s H : ℝ) < 1) ∧
        (1 ≤ H →
          Real.sqrt (H : ℝ) / Real.sqrt K < (s H : ℝ) ∧
          (s H : ℝ) < 2 * B * Real.sqrt (H : ℝ) ∧
          -(1 / 2 : ℝ) * Real.logb 2 K <
            (⌈Real.logb 2 (s H : ℝ)⌉ : ℝ) - (1 / 2 : ℝ) * Real.logb 2 (H : ℝ) ∧
          (⌈Real.logb 2 (s H : ℝ)⌉ : ℝ) - (1 / 2 : ℝ) * Real.logb 2 (H : ℝ) <
            1 + Real.logb 2 (2 * B)) := by
  classical
  let a := Real.arcsin ε / Real.pi
  let K := 1 + 3 * a
  let B := max (max 2 (2 * Real.pi / ε)) (Real.sqrt (4 * Real.pi / ε))
  have ha : 0 < a := div_pos (Real.arcsin_pos.mpr hε) Real.pi_pos
  have hK : 0 < K := by dsimp only [K]; positivity
  have hB2 : (2 : ℝ) ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB2
  have feasible (H : ℕ) : ∃ k : ℕ, P H ε k := by
    obtain ⟨m, _, _, _, _, hm⟩ := fibonacci_feasible H ε hε
    exact ⟨Nat.fib m, hm⟩
  let s : ℕ → ℕ := fun H => Nat.find (feasible H)
  refine ⟨hK, hB, s, ?_⟩
  intro H
  have hp : P H ε (s H) := Nat.find_spec (feasible H)
  have least : IsLeast {k : ℕ | P H ε k} (s H) :=
    ⟨hp, fun k hk => Nat.find_min' (feasible H) hk⟩
  obtain ⟨m, _, _, _, hqbound, hqfeasible⟩ := fibonacci_feasible H ε hε
  have hsq : s H ≤ Nat.fib m := least.2 hqfeasible
  have hu : (s H : ℝ) < 2 * cutoff H ε :=
    (show (s H : ℝ) ≤ (Nat.fib m : ℝ) by exact_mod_cast hsq).trans_lt hqbound
  obtain ⟨r, hr, hrs, hrfeasible, hlr⟩ := actual_machine_lower hε hεh hp
  have hrs' : s H ≤ r := least.2 hrfeasible
  have hre : r = s H := Nat.le_antisymm hrs hrs'
  have hs : 1 ≤ s H := by simpa only [hre] using hr
  have hl : (H : ℝ) < (s H : ℝ) + 3 * a * (s H : ℝ) ^ 2 := by
    simpa only [hre, a] using hlr
  have attained : ∃ (S : Type) (finiteS : Fintype S), Nonempty S ∧
      @Fintype.card S finiteS = s H ∧
      ∃ (e : UnitAddCircle → S) (G : Unit → S → S) (h : S → ℂ),
        ∀ x w, w.length ≤ H → dist (h (runWord G w (e x))) (o (runWord F w x)) ≤ ε := by
    rcases hp with ⟨S, finiteS, nonemptyS, hcard, e, G, h, herr⟩
    have hself : P H ε (@Fintype.card S finiteS) :=
      ⟨S, finiteS, nonemptyS, le_rfl, e, G, h, herr⟩
    exact ⟨S, finiteS, nonemptyS, Nat.le_antisymm hcard (least.2 hself), e, G, h, herr⟩
  have hgap : 0 ≤ (⌈Real.logb 2 (s H : ℝ)⌉ : ℝ) - Real.logb 2 (s H : ℝ) ∧
      (⌈Real.logb 2 (s H : ℝ)⌉ : ℝ) - Real.logb 2 (s H : ℝ) < 1 := by
    constructor
    · linarith [Int.le_ceil (Real.logb 2 (s H : ℝ))]
    · linarith [Int.ceil_lt_add_one (Real.logb 2 (s H : ℝ))]
  exact ⟨least, attained, hs, hl, hu, hgap,
    fun hH => asymptotic_join ε hε H (s H) hs hl hu hH⟩

set_option pp.all true in
#check full_exact_application
#print axioms full_exact_application

end

end Original8330Literal95SourceOnly
