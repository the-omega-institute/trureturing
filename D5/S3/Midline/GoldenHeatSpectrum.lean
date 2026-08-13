/- GID: D5/S3/Midline/GoldenHeatSpectrum
   generality: I
   mirror-B: D5/B/S3/Midline/GoldenHeatSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden Euler heat spectrum: its heat abscissa and strict L2 midline thresholds. -/

import Mathlib
import D5.S3.Analytic.GoldenEulerBeta
import D5.S3.Midline.UniversalHeatTrace

/- Provenance: Native proof over pinned mathlib.
   Search receipt (2026-08-13): searched this repository's D5 tree for an existing
   golden heat spectrum (`goldenSpectrum`, `golden_heat`, `IsHeatAbscissa` applied
   to a golden length function, and `o5Beta` outside its defining module) — miss:
   `UniversalHeatTrace` carries only the generic machinery and `ZetaHeatTraceBridge`
   instantiates it at `primeAxisLogLength`, so no golden instance existed. Searched
   pinned mathlib for the prime-series criterion and the summability infrastructure —
   hits, all imported and applied rather than re-proved: `Nat.Primes.summable_rpow`
   (Mathlib/NumberTheory/SumPrimeReciprocals.lean, the exact `r < -1` criterion used
   on both the convergence and the divergence side), `Real.rpow_def_of_pos`,
   `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_rpow_of_nonpos`,
   `summable_prod_of_nonneg`, `summable_geometric_of_lt_one`, `tsum_mul_right`,
   `Equiv.prodComm`. Reused frozen repository results rather than reproving them:
   `D5.S3.Analytic.GoldenEulerBeta.{o5Beta, o5_beta_power_law, o5_beta_growth}` and
   `D5.S3.Midline.UniversalHeatTrace.{IsHeatAbscissa, heatCoefficient,
   heat_coefficient_mem_of_abscissa, not_heat_coefficient_mem_of_abscissa}`.
   Miss: no library or repository theorem gives this spectrum's abscissa, so the
   two-sided abscissa proof here is native. -/

namespace D5.S3.Midline.GoldenHeatSpectrum

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Midline.UniversalHeatTrace

noncomputable section

/-- The excited golden Euler spectrum.  The natural-number coordinate `k`
encodes the positive mode `v = k + 1`, so the vacuum mode is absent. -/
noncomputable def goldenSpectrum : Nat.Primes × Nat → Real := fun pk =>
  o5Beta (pk.2 + 1) * Real.log (pk.1 : Real)

private theorem prime_real_pos (p : Nat.Primes) : 0 < (p : Real) := by
  exact_mod_cast p.prop.pos

private theorem exp_neg_goldenSpectrum (s : Real) (pk : Nat.Primes × Nat) :
    Real.exp (-s * goldenSpectrum pk) =
      (pk.1 : Real) ^ (-s * o5Beta (pk.2 + 1)) := by
  rw [Real.rpow_def_of_pos (prime_real_pos pk.1)]
  simp only [goldenSpectrum]
  congr 1
  ring

private theorem o5Beta_succ_ge (k : Nat) :
    Real.goldenRatio ^ 2 + (k : Real) ≤ o5Beta (k + 1) := by
  rcases o5_beta_power_law with ⟨hbeta, _⟩
  cases k with
  | zero => simpa using hbeta.ge
  | succ k =>
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hk : 0 ≤ (k : Real) := by positivity
      have hprod : 0 ≤ (Real.sqrt 5 - 1) * (k : Real) :=
        mul_nonneg (by linarith) hk
      apply le_trans _ (o5_beta_growth (Nat.succ k + 1))
      rw [one_div, Real.inv_goldenRatio]
      have hsum := Real.goldenRatio_add_goldenConj
      have hdiff := Real.goldenRatio_sub_goldenConj
      have hsq := Real.goldenRatio_sq
      norm_num [Nat.cast_add, Nat.cast_succ]
      nlinarith

private theorem critical_mul_lt (s : Real)
    (hs : 1 / Real.goldenRatio ^ 2 < s) :
    1 < s * Real.goldenRatio ^ 2 := by
  have hphi : 0 < Real.goldenRatio ^ 2 := sq_pos_of_pos Real.goldenRatio_pos
  exact (div_lt_iff₀ hphi).mp (by simpa [div_eq_mul_inv] using hs)

private theorem summable_golden_rpow
    (s : Real) (hs : 1 / Real.goldenRatio ^ 2 < s) :
    Summable (fun pk : Nat.Primes × Nat =>
      (pk.1 : Real) ^ (-s * o5Beta (pk.2 + 1))) := by
  have hcritical : 1 < s * Real.goldenRatio ^ 2 := critical_mul_lt s hs
  have hspos : 0 < s := by
    have halpha : 0 < 1 / Real.goldenRatio ^ 2 := by positivity
    linarith
  let r : Real := -s * Real.goldenRatio ^ 2
  let q : Real := (2 : Real) ^ (-s)
  have hr : r < -1 := by dsimp [r]; linarith
  have hq_nonneg : 0 ≤ q := by dsimp [q]; positivity
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbase : Summable (fun p : Nat.Primes => (p : Real) ^ r) :=
    Nat.Primes.summable_rpow.mpr hr
  have hslice (k : Nat) :
      Summable (fun p : Nat.Primes =>
        (p : Real) ^ (-s * o5Beta (k + 1))) := by
    apply Nat.Primes.summable_rpow.mpr
    have hbeta := o5Beta_succ_ge k
    have hk : 0 ≤ (k : Real) := by positivity
    nlinarith
  have hterm (k : Nat) (p : Nat.Primes) :
      (p : Real) ^ (-s * o5Beta (k + 1)) ≤
        (p : Real) ^ r * q ^ k := by
    have hp_one : 1 ≤ (p : Real) := by exact_mod_cast p.prop.one_lt.le
    have hp_two : (2 : Real) ≤ (p : Real) := by exact_mod_cast p.prop.two_le
    have hbeta := o5Beta_succ_ge k
    have hk : 0 ≤ (k : Real) := by positivity
    calc
      (p : Real) ^ (-s * o5Beta (k + 1)) ≤
          (p : Real) ^ (-s * (Real.goldenRatio ^ 2 + (k : Real))) :=
        Real.rpow_le_rpow_of_exponent_le hp_one (by nlinarith)
      _ = (p : Real) ^ r * (p : Real) ^ (-s * (k : Real)) := by
        rw [← Real.rpow_add (prime_real_pos p)]
        dsimp [r]
        congr 1
        ring
      _ ≤ (p : Real) ^ r * (2 : Real) ^ (-s * (k : Real)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (z := -s * (k : Real))
            (by norm_num) hp_two
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) hk)) (by positivity)
      _ = (p : Real) ^ r * q ^ k := by
        dsimp [q]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 2)]
  have htsum (k : Nat) :
      (∑' p : Nat.Primes, (p : Real) ^ (-s * o5Beta (k + 1))) ≤
        (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k := by
    calc
      (∑' p : Nat.Primes, (p : Real) ^ (-s * o5Beta (k + 1))) ≤
          ∑' p : Nat.Primes, (p : Real) ^ r * q ^ k :=
        (hslice k).tsum_le_tsum (hterm k) (hbase.mul_right (q ^ k))
      _ = (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k :=
        tsum_mul_right
  have houter : Summable (fun k : Nat =>
      ∑' p : Nat.Primes, (p : Real) ^ (-s * o5Beta (k + 1))) :=
    ((summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left
      (∑' p : Nat.Primes, (p : Real) ^ r)).of_nonneg_of_le
        (fun _ => by positivity) htsum
  have hswapped : Summable (fun kp : Nat × Nat.Primes =>
      (kp.2 : Real) ^ (-s * o5Beta (kp.1 + 1))) :=
    (summable_prod_of_nonneg (fun _ => by positivity)).mpr ⟨hslice, houter⟩
  exact (Equiv.prodComm Nat.Primes Nat).summable_iff.mpr hswapped

/-- The excited golden Euler spectrum has heat abscissa `1 / φ²`. -/
theorem golden_heat_abscissa :
    IsHeatAbscissa goldenSpectrum (1 / Real.goldenRatio ^ 2) := by
  constructor
  · intro s hs
    simpa only [exp_neg_goldenSpectrum] using summable_golden_rpow s hs
  · intro s hs hsum
    have hsub : Summable (fun p : Nat.Primes =>
        Real.exp (-s * goldenSpectrum (p, 0))) :=
      hsum.comp_injective (fun a b hab => congrArg Prod.fst hab)
    have hbeta : o5Beta 1 = Real.goldenRatio ^ 2 := o5_beta_power_law.1
    have hrpow : Summable (fun p : Nat.Primes =>
        (p : Real) ^ (-s * Real.goldenRatio ^ 2)) := by
      simpa only [exp_neg_goldenSpectrum, Nat.zero_add, hbeta] using hsub
    have hexponent : -s * Real.goldenRatio ^ 2 < -1 :=
      Nat.Primes.summable_rpow.mp hrpow
    have hphi : 0 < Real.goldenRatio ^ 2 := sq_pos_of_pos Real.goldenRatio_pos
    have hbelow : s * Real.goldenRatio ^ 2 < 1 :=
      (lt_div_iff₀ hphi).mp (by simpa [div_eq_mul_inv] using hs)
    linarith

private theorem golden_abscissa_half :
    (1 / Real.goldenRatio ^ 2) / 2 =
      1 / (2 * Real.goldenRatio ^ 2) := by
  field_simp [ne_of_gt Real.goldenRatio_pos]

theorem golden_heat_l2_mem :
    ∀ s : Complex, 1 / (2 * Real.goldenRatio ^ 2) < s.re →
      Memℓp
        (UniversalHeatTrace.heatCoefficient
          goldenSpectrum s) 2 := by
  intro s hs
  apply UniversalHeatTrace.heat_coefficient_mem_of_abscissa
    goldenSpectrum (1 / Real.goldenRatio ^ 2)
    golden_heat_abscissa s
  rw [golden_abscissa_half]
  exact hs

theorem golden_heat_l2_not_mem :
    ∀ s : Complex, s.re < 1 / (2 * Real.goldenRatio ^ 2) →
      ¬Memℓp
        (UniversalHeatTrace.heatCoefficient
          goldenSpectrum s) 2 := by
  intro s hs
  apply UniversalHeatTrace.not_heat_coefficient_mem_of_abscissa
    goldenSpectrum (1 / Real.goldenRatio ^ 2)
    golden_heat_abscissa s
  rw [golden_abscissa_half]
  exact hs

end

end D5.S3.Midline.GoldenHeatSpectrum
