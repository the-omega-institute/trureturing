/- GID: D5/S3/Analytic/EulerGerm/GoldenGermZetaFactorization
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenGermZetaFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden germ factors through zeta with a positive normalized product. -/

import D5.S3.Analytic.EulerGerm.GermProductConvergence
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/- Search audit (2026-08-26):
   * Repository name and body-shape searches for normalized golden germ factors,
     zeta-germ products, and the `1 / phi^3` boundary found no existing D5
     declaration. The canonical `o5Beta` and `germLocalFactor` are reused.
   * Pinned Mathlib supplies `riemannZeta_eulerProduct_hasProd`,
     `multipliable_one_add_of_summable`, `Multipliable.tprod_mul`, and the
     continuous embedding rules for real products in complex scalars, but no
     theorem for this normalized exponent family. -/

namespace D5.S3.Analytic.EulerGerm.GoldenGermZetaFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GermProductConvergence

noncomputable section

private theorem prime_real_pos (p : Nat.Primes) : 0 < (p : Real) := by
  exact_mod_cast p.prop.pos

private theorem o5_beta_two_add_ge (k : Nat) :
    Real.goldenRatio ^ 3 + (k : Real) <= o5Beta (k + 2) := by
  cases k with
  | zero => simpa using o5_beta_power_law.2.1.symm.le
  | succ k =>
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hphi_inv : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
        rw [one_div, Real.inv_goldenRatio]
        linarith [Real.goldenRatio_add_goldenConj]
      have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
        calc
          Real.goldenRatio ^ 3 =
              Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
          _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
            rw [Real.goldenRatio_sq]
          _ = 2 * Real.goldenRatio + 1 := by
            nlinarith [Real.goldenRatio_sq]
      apply le_trans _ (o5_beta_growth (k + 3))
      rw [hphi_inv, hcube]
      push_cast
      have hk : 0 <= (k : Real) := by positivity
      nlinarith [Real.goldenRatio_lt_two]

private theorem second_tail_real_summable (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    Summable (fun q : Nat.Primes × Nat =>
      (q.1 : Real) ^ (-sigma * o5Beta (q.2 + 2))) := by
  have hphi : 0 < Real.goldenRatio ^ 3 := by positivity
  have hcritical : 1 < sigma * Real.goldenRatio ^ 3 :=
    (div_lt_iff₀ hphi).mp (by simpa [div_eq_mul_inv] using hsigma)
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  let r : Real := -sigma * Real.goldenRatio ^ 3
  let q : Real := (2 : Real) ^ (-sigma)
  have hr : r < -1 := by dsimp [r]; linarith
  have hq_nonneg : 0 <= q := by dsimp [q]; positivity
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hsigma_pos)
  have hbase : Summable (fun p : Nat.Primes => (p : Real) ^ r) :=
    Nat.Primes.summable_rpow.mpr hr
  have hslice (k : Nat) :
      Summable (fun p : Nat.Primes =>
        (p : Real) ^ (-sigma * o5Beta (k + 2))) := by
    apply Nat.Primes.summable_rpow.mpr
    have hbeta := o5_beta_two_add_ge k
    nlinarith
  have hterm (k : Nat) (p : Nat.Primes) :
      (p : Real) ^ (-sigma * o5Beta (k + 2)) <=
        (p : Real) ^ r * q ^ k := by
    have hp_one : 1 <= (p : Real) := by exact_mod_cast p.prop.one_lt.le
    have hp_two : (2 : Real) <= (p : Real) := by exact_mod_cast p.prop.two_le
    have hbeta := o5_beta_two_add_ge k
    have hk : 0 <= (k : Real) := by positivity
    calc
      (p : Real) ^ (-sigma * o5Beta (k + 2)) <=
          (p : Real) ^ (-sigma * (Real.goldenRatio ^ 3 + (k : Real))) :=
        Real.rpow_le_rpow_of_exponent_le hp_one (by nlinarith)
      _ = (p : Real) ^ r * (p : Real) ^ (-sigma * (k : Real)) := by
        rw [← Real.rpow_add (prime_real_pos p)]
        dsimp [r]
        congr 1
        ring
      _ <= (p : Real) ^ r * (2 : Real) ^ (-sigma * (k : Real)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (z := -sigma * (k : Real))
            (by norm_num) hp_two
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) hk)) (by positivity)
      _ = (p : Real) ^ r * q ^ k := by
        dsimp [q]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) <= 2)]
  have htsum (k : Nat) :
      (∑' p : Nat.Primes, (p : Real) ^ (-sigma * o5Beta (k + 2))) <=
        (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k := by
    calc
      (∑' p : Nat.Primes, (p : Real) ^ (-sigma * o5Beta (k + 2))) <=
          ∑' p : Nat.Primes, (p : Real) ^ r * q ^ k :=
        (hslice k).tsum_le_tsum (hterm k) (hbase.mul_right (q ^ k))
      _ = (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k := tsum_mul_right
  have houter : Summable (fun k : Nat =>
      ∑' p : Nat.Primes, (p : Real) ^ (-sigma * o5Beta (k + 2))) :=
    ((summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left
      (∑' p : Nat.Primes, (p : Real) ^ r)).of_nonneg_of_le
        (fun _ => by positivity) htsum
  have hswapped : Summable (fun kp : Nat × Nat.Primes =>
      (kp.2 : Real) ^ (-sigma * o5Beta (kp.1 + 2))) :=
    (summable_prod_of_nonneg (fun _ => by positivity)).mpr ⟨hslice, houter⟩
  exact (Equiv.prodComm Nat.Primes Nat).summable_iff.mpr hswapped

private theorem second_tail_norm_summable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) :
    Summable (fun q : Nat.Primes × Nat =>
      ‖(q.1 : Complex) ^ (-s * (o5Beta (q.2 + 2) : Complex))‖) := by
  refine (second_tail_real_summable s.re hs).congr fun q => ?_
  rw [Complex.norm_natCast_cpow_of_pos q.1.prop.pos]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem second_tail_summable_at_prime (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) (p : Nat.Primes) :
    Summable (fun k : Nat =>
      (p : Complex) ^ (-s * (o5Beta (k + 2) : Complex))) := by
  exact ((second_tail_norm_summable s hs).prod_factor p).of_norm

private theorem local_factor_eq_first_order_and_tail (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) (p : Nat.Primes) :
    germLocalFactor s p =
      1 + (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) +
        ∑' k : Nat, (p : Complex) ^ (-s * (o5Beta (k + 2) : Complex)) := by
  let f : Nat -> Complex := fun v =>
    (p : Complex) ^ (-s * (o5Beta v : Complex))
  have htail : Summable (fun k : Nat => f (k + 2)) := by
    simpa [f, Nat.add_comm] using second_tail_summable_at_prime s hs p
  have hall : Summable f := (summable_nat_add_iff 2).1 htail
  rw [germLocalFactor, show (fun v : Nat =>
      (p : Complex) ^ (-s * (o5Beta v : Complex))) = f from rfl,
    ← hall.sum_add_tsum_nat_add 2]
  simp [f, Finset.sum_range_succ, o5_beta_zero, o5_beta_power_law.1,
    Real.goldenRatio_sq, add_assoc]

private theorem first_mode_norm_le_one (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) (p : Nat.Primes) :
    ‖(p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))‖ <= 1 := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)).re =
      -s.re * Real.goldenRatio ^ 2 by norm_num]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast p.prop.one_le) (by nlinarith [sq_pos_of_pos Real.goldenRatio_pos])

private theorem first_mode_square_norm_summable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) :
    Summable (fun p : Nat.Primes =>
      ‖((p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) ^ 2‖) := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi3_lt : Real.goldenRatio ^ 3 < 2 * Real.goldenRatio ^ 2 := by
    calc
      Real.goldenRatio ^ 3 = Real.goldenRatio ^ 2 * Real.goldenRatio := by ring
      _ < Real.goldenRatio ^ 2 * 2 :=
        mul_lt_mul_of_pos_left Real.goldenRatio_lt_two hphi2
      _ = 2 * Real.goldenRatio ^ 2 := by ring
  have hcritical : 1 < s.re * Real.goldenRatio ^ 3 :=
    (div_lt_iff₀ (by positivity : 0 < Real.goldenRatio ^ 3)).mp
      (by simpa [div_eq_mul_inv] using hs)
  have hexponent : -s.re * Real.goldenRatio ^ 2 * 2 < -1 := by
    have := mul_lt_mul_of_pos_left hphi3_lt hspos
    nlinarith
  refine (Nat.Primes.summable_rpow.mpr hexponent).congr fun p => ?_
  rw [norm_pow, Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)).re =
      -s.re * Real.goldenRatio ^ 2 by norm_num]
  exact Real.rpow_mul_natCast (prime_real_pos p).le
    (-s.re * Real.goldenRatio ^ 2) 2

private theorem normalized_factor_deviation_norm_summable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) :
    Summable (fun p : Nat.Primes =>
      ‖(1 - (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
          germLocalFactor s p - 1‖) := by
  let a : Nat.Primes -> Complex := fun p =>
    (p : Complex) ^ (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
  let tail : Nat.Primes -> Complex := fun p =>
    ∑' k : Nat, (p : Complex) ^ (-s * (o5Beta (k + 2) : Complex))
  have hnorm := second_tail_norm_summable s hs
  have htailNorm : Summable (fun p : Nat.Primes => ‖tail p‖) := by
    refine hnorm.prod.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    exact norm_tsum_le_tsum_norm (hnorm.prod_factor p)
  have htail : Summable tail := htailNorm.of_norm
  have haSquareNorm : Summable (fun p : Nat.Primes => ‖a p ^ 2‖) := by
    simpa [a] using first_mode_square_norm_summable s hs
  have haSquare : Summable (fun p : Nat.Primes => a p ^ 2) :=
    haSquareNorm.of_norm
  have haTailNorm : Summable (fun p : Nat.Primes => ‖a p * tail p‖) := by
    refine htailNorm.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by
      simpa [a] using first_mode_norm_le_one s hs p)
  have haTail : Summable (fun p : Nat.Primes => a p * tail p) :=
    haTailNorm.of_norm
  have hcorrection : Summable (fun p : Nat.Primes =>
      tail p - a p ^ 2 - a p * tail p) :=
    (htail.sub haSquare).sub haTail
  refine hcorrection.norm.congr fun p => ?_
  rw [local_factor_eq_first_order_and_tail s hs p]
  dsimp [a, tail]
  congr 1
  ring

private theorem normalized_factor_multipliable (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) :
    Multipliable (fun p : Nat.Primes =>
      (1 - (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
        germLocalFactor s p) := by
  have hdev := normalized_factor_deviation_norm_summable s hs
  have hproduct := multipliable_one_add_of_summable hdev
  refine hproduct.congr fun p => ?_
  ring

private theorem first_mode_norm_lt_one (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) (p : Nat.Primes) :
    ‖(p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))‖ < 1 := by
  have hspos : 0 < s.re := lt_trans (by positivity) hs
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  rw [show (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)).re =
      -s.re * Real.goldenRatio ^ 2 by norm_num]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt)
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hspos)
      (sq_pos_of_pos Real.goldenRatio_pos))

private theorem inverse_first_mode_mul_normalized (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 3 < s.re) (p : Nat.Primes) :
    (1 - (p : Complex) ^
        (-(((Real.goldenRatio ^ 2 : Real) : Complex) * s)))⁻¹ *
      ((1 - (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
        germLocalFactor s p) = germLocalFactor s p := by
  have hpower :
      (p : Complex) ^
          (-(((Real.goldenRatio ^ 2 : Real) : Complex) * s)) =
        (p : Complex) ^
          (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) := by
    congr 1
    ring
  rw [hpower]
  have hne : 1 - (p : Complex) ^
      (-s * ((Real.goldenRatio ^ 2 : Real) : Complex)) ≠ 0 := by
    rw [sub_ne_zero]
    intro hpow
    have hnorm := first_mode_norm_lt_one s hs p
    rw [← hpow, norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

private theorem germ_product_factorization (s : Complex)
    (hs : 1 / Real.goldenRatio ^ 2 < s.re) :
    (∏' p : Nat.Primes, germLocalFactor s p) =
      riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        ∏' p : Nat.Primes,
          (1 - (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
            germLocalFactor s p := by
  have hphi2 : 0 < Real.goldenRatio ^ 2 := by positivity
  have hphi2_lt_phi3 : Real.goldenRatio ^ 2 < Real.goldenRatio ^ 3 := by
    calc
      Real.goldenRatio ^ 2 < Real.goldenRatio ^ 2 * Real.goldenRatio :=
        (lt_mul_iff_one_lt_right hphi2).mpr Real.one_lt_goldenRatio
      _ = Real.goldenRatio ^ 3 := by ring
  have hthreshold :
      1 / Real.goldenRatio ^ 3 < 1 / Real.goldenRatio ^ 2 :=
    one_div_lt_one_div_of_lt (by positivity) hphi2_lt_phi3
  have hs3 : 1 / Real.goldenRatio ^ 3 < s.re := hthreshold.trans hs
  have hzetaDomain :
      1 < ((((Real.goldenRatio ^ 2 : Real) : Complex) * s).re) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hcleared : 1 < s.re * Real.goldenRatio ^ 2 :=
      (div_lt_iff₀ hphi2).mp hs
    nlinarith
  have hzeta := riemannZeta_eulerProduct_hasProd hzetaDomain
  have hnormalized := normalized_factor_multipliable s hs3
  have hcombined := hzeta.mul hnormalized.hasProd
  have hlocal : HasProd (fun p : Nat.Primes => germLocalFactor s p)
      (riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) *
        ∏' p : Nat.Primes,
          (1 - (p : Complex) ^
              (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
            germLocalFactor s p) :=
    hcombined.congr_fun
      (fun p => (inverse_first_mode_mul_normalized s hs3 p).symm)
  exact (germLocalFactor_multipliable s hs).hasProd.unique hlocal

private theorem real_local_factor_summable (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) (p : Nat.Primes) :
    Summable (fun v : Nat => (p : Real) ^ (-sigma * o5Beta v)) := by
  have htail : Summable (fun k : Nat =>
      (p : Real) ^ (-sigma * o5Beta (k + 2))) :=
    (second_tail_real_summable sigma hsigma).prod_factor p
  exact (summable_nat_add_iff 2).1 (by
    simpa [Nat.add_comm] using htail)

private theorem real_local_factor_pos (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) (p : Nat.Primes) :
    0 < ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) := by
  have hsum := real_local_factor_summable sigma hsigma p
  refine hsum.tsum_pos (fun _ => Real.rpow_nonneg (by positivity) _) 0 ?_
  simp [o5_beta_zero]

private theorem ofReal_real_local_factor_eq (sigma : Real) (p : Nat.Primes) :
    ((∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) : Real) : Complex) =
      germLocalFactor (sigma : Complex) p := by
  rw [germLocalFactor, Complex.ofReal_tsum]
  congr 1 with v
  rw [Complex.ofReal_cpow (by positivity)]
  congr 1
  norm_num

private theorem real_normalized_factor_pos (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) (p : Nat.Primes) :
    0 < (1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
      ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) := by
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  have hfirst : (p : Real) ^ (-sigma * Real.goldenRatio ^ 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hsigma_pos)
        (sq_pos_of_pos Real.goldenRatio_pos))
  exact mul_pos (sub_pos.mpr hfirst) (real_local_factor_pos sigma hsigma p)

private theorem ofReal_real_normalized_factor_eq (sigma : Real)
    (p : Nat.Primes) :
    (((1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
        ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) : Real) : Complex) =
      (1 - (p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 2 : Real) : Complex))) *
        germLocalFactor (sigma : Complex) p := by
  rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_cpow (by positivity),
    ofReal_real_local_factor_eq sigma p]
  congr 2
  norm_num

private theorem real_normalized_factor_deviation_summable (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    Summable (fun p : Nat.Primes =>
      (1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
        ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) - 1) := by
  have hcomplex :=
    (normalized_factor_deviation_norm_summable (sigma : Complex)
      (by simpa using hsigma)).of_norm
  apply Complex.summable_ofReal.mp
  refine hcomplex.congr fun p => ?_
  rw [Complex.ofReal_sub, Complex.ofReal_one,
    ofReal_real_normalized_factor_eq sigma p]

private theorem real_normalized_factor_multipliable (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    Multipliable (fun p : Nat.Primes =>
      (1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
        ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v)) := by
  have hdev := real_normalized_factor_deviation_summable sigma hsigma
  have hproduct := Real.multipliable_one_add_of_summable hdev
  refine hproduct.congr fun p => ?_
  ring

private theorem real_normalized_product_pos (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    0 < ∏' p : Nat.Primes,
      (1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
        ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) := by
  let f : Nat.Primes -> Real := fun p =>
    (1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
      ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v)
  have hpos (p : Nat.Primes) : 0 < f p := by
    simpa [f] using real_normalized_factor_pos sigma hsigma p
  have hdev : Summable (fun p : Nat.Primes => f p - 1) := by
    simpa [f] using real_normalized_factor_deviation_summable sigma hsigma
  have hmult : Multipliable f := by
    simpa [f] using real_normalized_factor_multipliable sigma hsigma
  have hnonzeroAux :=
    tprod_one_add_ne_zero_of_summable
      (f := fun p : Nat.Primes => f p - 1)
      (fun p => by
        rw [show 1 + (f p - 1) = f p by ring]
        exact (hpos p).ne')
      hdev.norm
  have hfun : (fun p : Nat.Primes => 1 + (f p - 1)) = f := by
    funext p
    ring
  rw [hfun] at hnonzeroAux
  have hnonneg : 0 <= ∏' p : Nat.Primes, f p := by
    apply le_hasProd_of_le_prod hmult.hasProd
    intro t
    exact Finset.prod_nonneg fun p _ => (hpos p).le
  change 0 < ∏' p : Nat.Primes, f p
  exact lt_of_le_of_ne hnonneg (Ne.symm hnonzeroAux)

private theorem normalized_factor_real_axis (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 3 < sigma) :
    (∏' p : Nat.Primes,
      (1 - (p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 2 : Real) : Complex))) *
        germLocalFactor (sigma : Complex) p) =
      ((∏' p : Nat.Primes,
        (1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
          ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) : Real) : Complex) := by
  have hmap := (real_normalized_factor_multipliable sigma hsigma).map_tprod
    Complex.ofRealHom Complex.continuous_ofReal
  change (((∏' p : Nat.Primes,
      (1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
        ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) : Real) : Complex) =
    ∏' p : Nat.Primes,
      (((1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
        ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) : Real) : Complex)) at hmap
  calc
    (∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-(sigma : Complex) *
              ((Real.goldenRatio ^ 2 : Real) : Complex))) *
          germLocalFactor (sigma : Complex) p) =
        ∏' p : Nat.Primes,
          (((1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
            ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) : Real) : Complex) :=
      tprod_congr fun p =>
        (ofReal_real_normalized_factor_eq sigma p).symm
    _ = ((∏' p : Nat.Primes,
          (1 - (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)) *
            ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) : Real) : Complex) :=
      hmap.symm

/-- The golden germ prime product factors as a shifted Riemann zeta function
times its normalized Euler product. The normalized product is absolutely
convergent on `Re s > 1 / phi^3` and strictly positive on that real ray. -/
theorem golden_germ_zeta_factorization :
    let G : Complex -> Complex := fun s =>
      ∏' p : Nat.Primes,
        (1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
          germLocalFactor s p
    (∀ s : Complex, 1 / Real.goldenRatio ^ 2 < s.re ->
      (∏' p : Nat.Primes, germLocalFactor s p) =
        riemannZeta (((Real.goldenRatio ^ 2 : Real) : Complex) * s) * G s) ∧
    (∀ s : Complex, 1 / Real.goldenRatio ^ 3 < s.re ->
      Summable (fun p : Nat.Primes =>
        ‖(1 - (p : Complex) ^
            (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))) *
          germLocalFactor s p - 1‖)) ∧
    (∀ sigma : Real, 1 / Real.goldenRatio ^ 3 < sigma ->
      0 < (G (sigma : Complex)).re ∧ (G (sigma : Complex)).im = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact germ_product_factorization s hs
  · intro s hs
    exact normalized_factor_deviation_norm_summable s hs
  · intro sigma hsigma
    have haxis := normalized_factor_real_axis sigma hsigma
    have hpos := real_normalized_product_pos sigma hsigma
    constructor
    · rw [haxis, Complex.ofReal_re]
      exact hpos
    · rw [haxis, Complex.ofReal_im]

end

end D5.S3.Analytic.EulerGerm.GoldenGermZetaFactorization
