/- GID: D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRealPositivity
   generality: I
   mirror-B: D5/B/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRealPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The third normalized golden germ is strictly positive on its full positive real ray. -/

import D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
import D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRegularity

/- Library-search audit trail (2026-09-03):
   * Repository searches over `D5/**/*.lean` found no theorem asserting strict
     positivity of the third normalized golden factor on the full real ray.
     The frozen `golden_germ_third_order_factorization` supplies the required
     prime-summable deviations, and the frozen
     `golden_germ_third_normalized_factor_regularity` supplies real-point
     nonvanishing throughout the same ray.
   * The regularity theorem exposes only global real-point nonvanishing. Its
     real local-series positivity and real-to-complex transport lemmas are
     private, so the sign argument below works at the canonical definitions
     `o5Beta` and `germLocalFactor`; it does not wrap hidden local statements.
   * Pinned Mathlib supplies `Complex.ofReal_cpow`, `Complex.ofReal_tsum`,
     `Real.multipliable_one_add_of_summable`, `le_hasProd_of_le_prod`,
     `Finset.prod_nonneg`, `tprod_one_add_ne_zero_of_summable`, and
     `Multipliable.map_tprod`. The last three transfer finite-product
     nonnegativity and genuine infinite-product nonvanishing to strict
     positivity.

   This theorem is confined to positive real points strictly above the
   phi-fifth threshold. It does not assert O-5, the Riemann hypothesis,
   complex nonvanishing on the whole half-plane, or any all-order extraction. -/

namespace D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRealPositivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenGermThirdOrderFactorization
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRegularity

noncomputable section

private theorem natCast_le_o5Beta (v : Nat) : (v : Real) <= o5Beta v := by
  cases v with
  | zero => simp [o5_beta_zero]
  | succ v =>
      have hgrowth := o5_beta_growth (v + 1)
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : Real) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 <= Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hinv_pos : 0 < 1 / Real.goldenRatio :=
        one_div_pos.mpr Real.goldenRatio_pos
      push_cast at hgrowth ⊢
      nlinarith

private theorem real_local_factor_summable (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) (p : Nat.Primes) :
    Summable (fun v : Nat => (p : Real) ^ (-sigma * o5Beta v)) := by
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  let q : Real := (p : Real) ^ (-sigma)
  have hp_pos : (0 : Real) < p := by exact_mod_cast p.prop.pos
  have hq_nonneg : 0 <= q := Real.rpow_nonneg hp_pos.le _
  have hq_lt_one : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt) (neg_neg_of_pos hsigma_pos)
  have hgeom : Summable (fun v : Nat => q ^ v) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
      exact hq_lt_one)
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg hp_pos.le _)
    (fun v => ?_) hgeom
  calc
    (p : Real) ^ (-sigma * o5Beta v) <=
        (p : Real) ^ (-sigma * (v : Real)) :=
      Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast p.prop.one_lt.le)
        (by nlinarith [natCast_le_o5Beta v])
    _ = q ^ v := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]

private theorem real_local_factor_pos (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) (p : Nat.Primes) :
    0 < ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) := by
  refine (real_local_factor_summable sigma hsigma p).tsum_pos
    (fun _ => Real.rpow_nonneg (by positivity) _) 0 ?_
  simp [o5_beta_zero]

private theorem ofReal_real_local_factor_eq (sigma : Real)
    (p : Nat.Primes) :
    ((∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v) : Real) : Complex) =
      germLocalFactor (sigma : Complex) p := by
  rw [germLocalFactor, Complex.ofReal_tsum]
  congr 1 with v
  rw [Complex.ofReal_cpow (by positivity)]
  congr 1
  norm_num

private noncomputable def realThirdNormalizedFactor
    (sigma : Real) (p : Nat.Primes) : Real :=
  let x := (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)
  let y := (p : Real) ^ (-sigma * Real.goldenRatio ^ 3)
  (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
    (1 - y) * (1 + x)⁻¹ *
      ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v)

private theorem realThirdNormalizedFactor_pos (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) (p : Nat.Primes) :
    0 < realThirdNormalizedFactor sigma p := by
  have hsigma_pos : 0 < sigma := lt_trans (by positivity) hsigma
  let x : Real := (p : Real) ^ (-sigma * Real.goldenRatio ^ 2)
  let y : Real := (p : Real) ^ (-sigma * Real.goldenRatio ^ 3)
  have hx_pos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have hy_pos : 0 < y := by
    dsimp [y]
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have hx_lt_one : x < 1 := by
    dsimp [x]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hsigma_pos) (by positivity))
  have hy_lt_one : y < 1 := by
    dsimp [y]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hsigma_pos) (by positivity))
  have hy_sq_lt_one : y ^ 2 < 1 :=
    pow_lt_one₀ hy_pos.le hy_lt_one (by norm_num)
  have hx_sq_lt_one : x ^ 2 < 1 :=
    pow_lt_one₀ hx_pos.le hx_lt_one (by norm_num)
  have hx_sq_mul_y_lt_one : x ^ 2 * y < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left
      (pow_nonneg hx_pos.le 2) hx_sq_lt_one hy_lt_one.le
  have hfirst : 0 < (1 - y ^ 2)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr hy_sq_lt_one)
  have hsecond : 0 < 1 - x ^ 2 * y :=
    sub_pos.mpr hx_sq_mul_y_lt_one
  have hthird : 0 < 1 - y := sub_pos.mpr hy_lt_one
  have hfourth : 0 < (1 + x)⁻¹ := inv_pos.mpr (by linarith)
  unfold realThirdNormalizedFactor
  change 0 < (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
    (1 - y) * (1 + x)⁻¹ *
      ∑' v : Nat, (p : Real) ^ (-sigma * o5Beta v)
  exact mul_pos
    (mul_pos (mul_pos (mul_pos hfirst hsecond) hthird) hfourth)
    (real_local_factor_pos sigma hsigma p)

private theorem ofReal_realThirdNormalizedFactor_eq (sigma : Real)
    (p : Nat.Primes) :
    (realThirdNormalizedFactor sigma p : Complex) =
      (let x := (p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 2 : Real) : Complex))
       let y := (p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 3 : Real) : Complex))
       (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
         (1 - y) * (1 + x)⁻¹ * germLocalFactor (sigma : Complex) p) := by
  have hx :
      (((p : Real) ^ (-sigma * Real.goldenRatio ^ 2) : Real) : Complex) =
        (p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 2 : Real) : Complex)) := by
    rw [Complex.ofReal_cpow (by positivity)]
    congr 1
    norm_num
  have hy :
      (((p : Real) ^ (-sigma * Real.goldenRatio ^ 3) : Real) : Complex) =
        (p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 3 : Real) : Complex)) := by
    rw [Complex.ofReal_cpow (by positivity)]
    congr 1
    norm_num
  unfold realThirdNormalizedFactor
  rw [← hx, ← hy, ← ofReal_real_local_factor_eq sigma p]
  norm_num

private theorem realThirdNormalizedFactor_deviation_summable
    (sigma : Real) (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) :
    Summable (fun p : Nat.Primes => realThirdNormalizedFactor sigma p - 1) := by
  have hfactorization := golden_germ_third_order_factorization
  dsimp only at hfactorization
  have hcomplex :=
    (hfactorization.1 (sigma : Complex) (by simpa using hsigma)).of_norm
  apply Complex.summable_ofReal.mp
  refine hcomplex.congr fun p => ?_
  rw [Complex.ofReal_sub, Complex.ofReal_one,
    ofReal_realThirdNormalizedFactor_eq sigma p]

private theorem realThirdNormalizedFactor_multipliable
    (sigma : Real) (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) :
    Multipliable (fun p : Nat.Primes => realThirdNormalizedFactor sigma p) := by
  have hdev := realThirdNormalizedFactor_deviation_summable sigma hsigma
  have hproduct := Real.multipliable_one_add_of_summable hdev
  refine hproduct.congr fun p => ?_
  ring

private theorem realThirdNormalizedProduct_pos (sigma : Real)
    (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) :
    0 < ∏' p : Nat.Primes, realThirdNormalizedFactor sigma p := by
  let f : Nat.Primes -> Real := realThirdNormalizedFactor sigma
  have hpos (p : Nat.Primes) : 0 < f p := by
    simpa [f] using realThirdNormalizedFactor_pos sigma hsigma p
  have hdev : Summable (fun p : Nat.Primes => f p - 1) := by
    simpa [f] using realThirdNormalizedFactor_deviation_summable sigma hsigma
  have hmult : Multipliable f := by
    simpa [f] using realThirdNormalizedFactor_multipliable sigma hsigma
  have hregularity := golden_germ_third_normalized_factor_regularity
  dsimp only at hregularity
  have hcomplexProductNonzero := hregularity.2.2.2.1 sigma hsigma
  have hcomplexLocal (p : Nat.Primes) :
      (let x := (p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 2 : Real) : Complex))
       let y := (p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 3 : Real) : Complex))
       (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
         (1 - y) * (1 + x)⁻¹ * germLocalFactor (sigma : Complex) p) ≠ 0 := by
    intro hzero
    apply hcomplexProductNonzero
    exact tprod_of_exists_eq_zero ⟨p, hzero⟩
  have hrealLocal (p : Nat.Primes) : f p ≠ 0 := by
    intro hzero
    apply hcomplexLocal p
    rw [← ofReal_realThirdNormalizedFactor_eq sigma p]
    simp [f, hzero]
  have hnonzeroAux := tprod_one_add_ne_zero_of_summable
    (f := fun p : Nat.Primes => f p - 1)
    (fun p => by
      rw [show 1 + (f p - 1) = f p by ring]
      exact hrealLocal p) hdev.norm
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

private theorem third_normalized_factor_real_axis_positive
    (sigma : Real) (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s => ∏' p : Nat.Primes, Kp s p
    (G3 (sigma : Complex)).im = 0 ∧ 0 < (G3 (sigma : Complex)).re := by
  dsimp only
  have hmap :=
    (realThirdNormalizedFactor_multipliable sigma hsigma).map_tprod
      Complex.ofRealHom Complex.continuous_ofReal
  change ((∏' p : Nat.Primes,
      realThirdNormalizedFactor sigma p : Real) : Complex) =
        ∏' p : Nat.Primes,
          (realThirdNormalizedFactor sigma p : Complex) at hmap
  have haxis :
      (∏' p : Nat.Primes,
        let x := (p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 2 : Real) : Complex))
        let y := (p : Complex) ^
          (-(sigma : Complex) *
            ((Real.goldenRatio ^ 3 : Real) : Complex))
        (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
          (1 - y) * (1 + x)⁻¹ * germLocalFactor (sigma : Complex) p) =
        ((∏' p : Nat.Primes,
          realThirdNormalizedFactor sigma p : Real) : Complex) := by
    calc
      _ = ∏' p : Nat.Primes,
          (realThirdNormalizedFactor sigma p : Complex) :=
        tprod_congr fun p =>
          (ofReal_realThirdNormalizedFactor_eq sigma p).symm
      _ = _ := hmap.symm
  have hpos := realThirdNormalizedProduct_pos sigma hsigma
  constructor
  · rw [haxis, Complex.ofReal_im]
  · rw [haxis, Complex.ofReal_re]
    exact hpos

/-- The third normalized golden Euler factor is a strictly positive real
number at every real point above the phi-fifth threshold. -/
theorem golden_germ_third_normalized_factor_real_axis_positivity
    (sigma : Real) (hsigma : 1 / Real.goldenRatio ^ 5 < sigma) :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s => ∏' p : Nat.Primes, Kp s p
    (G3 (sigma : Complex)).im = 0 ∧ 0 < (G3 (sigma : Complex)).re := by
  fail_if_success rfl
  fail_if_success (solve | simp)
  fail_if_success (solve | trivial)
  exact third_normalized_factor_real_axis_positive sigma hsigma

private theorem one_in_third_normalized_positive_ray :
    1 / Real.goldenRatio ^ 5 < (1 : Real) := by
  rw [div_lt_one (by positivity : 0 < Real.goldenRatio ^ 5)]
  exact one_lt_pow₀ Real.one_lt_goldenRatio (by norm_num)

private theorem third_normalized_factor_positive_at_one :
    let Kp : Complex -> Nat.Primes -> Complex := fun s p =>
      let x := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 2 : Real) : Complex))
      let y := (p : Complex) ^
        (-s * ((Real.goldenRatio ^ 3 : Real) : Complex))
      (1 - y ^ 2)⁻¹ * (1 - x ^ 2 * y) *
        (1 - y) * (1 + x)⁻¹ * germLocalFactor s p
    let G3 : Complex -> Complex := fun s => ∏' p : Nat.Primes, Kp s p
    (G3 (1 : Complex)).im = 0 ∧ 0 < (G3 (1 : Complex)).re :=
  golden_germ_third_normalized_factor_real_axis_positivity 1
    one_in_third_normalized_positive_ray

#print axioms golden_germ_third_normalized_factor_real_axis_positivity

end

end D5.S3.Analytic.Regularity.GoldenGermThirdNormalizedFactorRealPositivity
