/- GID: D5/S1/Words/Patterns/Separable/OccupiedNonlinearLoss
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedNonlinearLoss
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SumIntegralComparisons]
   utility: none
   digest: Actual loss convolution is controlled by the squared logarithmic profile. -/

import D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient
import D5.S1.Words.Patterns.Separable.OccupiedComparison
import D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! A near/far split controls the coefficient-weighted square of the actual
logarithmic occupation profile. -/

open MeasureTheory

namespace D5.S1.Words.Patterns.Separable.OccupiedNonlinearLoss

open OccupiedComparison OccupiedKernelCoefficient
open D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries (discrepancyProfile)

private noncomputable def squareProfile (x : ℤ) : ℝ :=
  1 / ((2+|(x : ℝ)|) * Real.log (2+|(x : ℝ)|)^2)

private theorem denom_pos (x : ℤ) :
    0 < (2+|(x : ℝ)|) * Real.log (2+|(x : ℝ)|)^2 := by
  have h : (1:ℝ) < 2+|(x : ℝ)| := by linarith only [abs_nonneg (x : ℝ)]
  exact mul_pos (by linarith) (sq_pos_of_pos (Real.log_pos h))

private theorem squareProfile_pos (x : ℤ) : 0 < squareProfile x := one_div_pos.mpr (denom_pos x)

private theorem squareProfile_eq_square (x : ℤ) :
    squareProfile x =
      discrepancyProfile x ^ 2 := by
  rw [squareProfile, discrepancyProfile, div_pow, one_pow, mul_pow,
    Real.sq_sqrt (show 0 ≤ 2+|(x : ℝ)| by positivity)]

private theorem near_squareProfile_ratio {x y : ℤ} (h : |(x : ℝ)| / 2 ≤ |(y : ℝ)|) :
    squareProfile y ≤ 8 * squareProfile x := by
  let X := 2+|(x : ℝ)|
  let Y := 2+|(y : ℝ)|
  have hX : 2 ≤ X := by dsimp [X]; linarith only [abs_nonneg (x : ℝ)]
  have hY : 2 ≤ Y := by dsimp [Y]; linarith only [abs_nonneg (y : ℝ)]
  have hXY : X ≤ 2*Y := by dsimp [X,Y]; linarith only [h]
  have hYY : 2*Y ≤ Y^2 := by
    nlinarith only [mul_nonneg (show 0 ≤ Y by linarith) (show 0 ≤ Y-2 by linarith)]
  have hxlog := Real.log_pos (show 1 < X by linarith)
  have hylog := Real.log_pos (show 1 < Y by linarith)
  have hlog := Real.log_le_log (show 0 < X by linarith) (hXY.trans hYY)
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hlogs : Real.log X ^ 2 ≤ 4 * Real.log Y ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hlog)
      (show 0 ≤ 2*Real.log Y + Real.log X by linarith)]
  have hd := mul_le_mul hXY hlogs (sq_nonneg _) (show 0 ≤ 2*Y by linarith)
  have hh : X*Real.log X^2 ≤ 8*(Y*Real.log Y^2) := by nlinarith only [hd]
  change 1/(Y*Real.log Y^2) ≤ 8*(1/(X*Real.log X^2))
  rw [mul_one_div]
  apply (div_le_div_iff₀ (denom_pos y) (denom_pos x)).2
  simpa only [one_mul] using hh

/-- The exact discrete profile is square-summable on both integer rays. -/
private theorem squareProfile_summable : Summable squareProfile := by
  let f (t : ℝ) := t⁻¹ / Real.log t ^ 2
  have hf (x : ℝ) (hx : 1 < x) : 0 ≤ f x :=
    div_nonneg (inv_nonneg.mpr (by linarith)) (sq_nonneg _)
  have hmono {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) : f y ≤ f x := by
    have hy := hx.trans_le hxy
    have hxlog := Real.log_pos hx
    have hle := Real.log_le_log (show 0 < x by linarith) hxy
    have hs : Real.log x^2 ≤ Real.log y^2 :=
      pow_le_pow_left₀ hxlog.le hle _
    exact (div_le_div_of_nonneg_right ((inv_le_inv₀ (by linarith) (by linarith)).mpr hxy)
      (sq_nonneg _)).trans (div_le_div_of_nonneg_left (inv_nonneg.mpr (by linarith))
        (sq_pos_of_pos hxlog) hs)
  have hi := integrableOn_inv_div_log_sq_Ioi (show (1 : ℝ) < 2 by norm_num)
  have hanti : AntitoneOn f (Set.Ici (2 : ℝ)) := by
    intro x hx y _ hxy
    exact hmono (lt_of_lt_of_le (by norm_num) hx) hxy
  have hnat := hanti.summable_of_integrableOn_Ioi hi
    (fun t ht => hf t (lt_trans (by norm_num) ht))
  have hnat' : Summable (fun i : ℕ => squareProfile (i : ℤ)) := by
    apply ((summable_nat_add_iff 2).2 hnat).congr
    intro i
    unfold f squareProfile
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg i), Nat.cast_add, Nat.cast_ofNat,
      add_comm (i : ℝ) 2, div_eq_mul_inv, one_div, mul_inv]
  apply summable_int_iff_summable_nat_and_neg.mpr
  refine ⟨hnat', ?_⟩
  simpa only [squareProfile, Int.cast_neg, abs_neg] using hnat'

private theorem far_power_le_profile (x : ℤ) (hx : 1 ≤ |(x : ℝ)|) :
    (|(x : ℝ)| / 2)^(-(3 / 2:ℝ)) ≤ 384*squareProfile x := by
  let t := |(x : ℝ)|
  let X := 2+t
  have ht : 0 < t := by dsimp [t]; linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by dsimp [X]; linarith)
  have hlog' := Real.log_le_rpow_div hX.le (show (0:ℝ) < 1 / 4 by norm_num)
  have hsq : Real.log X^2 ≤ 16*X^(1 / 2:ℝ) := by
    have h := pow_le_pow_left₀ hlog hlog' 2
    have hp : (X^(1 / 4:ℝ))^2 = X^(1 / 2:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
      congr 1
      norm_num
    rw [div_pow, hp] at h
    norm_num at h
    linarith only [h]
  have hroot : X^(1 / 2:ℝ) ≤ 2*t^(1 / 2:ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have h : X ≤ 4*t := by change 1 ≤ t at hx; dsimp [X]; linarith
    exact (Real.sqrt_le_sqrt h).trans_eq (by rw [Real.sqrt_mul (by norm_num),
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num : (0:ℝ) ≤ 2)).mpr (by norm_num)])
  have hden : X * Real.log X^2 ≤ 96*t^(3 / 2:ℝ) := by
    have hXX : X ≤ 3*t := by change 1 ≤ t at hx; dsimp [X]; linarith
    have hh := mul_le_mul hXX (hsq.trans (mul_le_mul_of_nonneg_left hroot (by norm_num)))
      (sq_nonneg _) (by positivity : 0 ≤ 3*t)
    have he : t * t^(1 / 2:ℝ) = t^(3 / 2:ℝ) := by
      rw [← show (1+(1 / 2:ℝ)) = 3 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one]
    nlinarith only [hh, he]
  have hbase : t^(-(3 / 2:ℝ)) ≤ 96*squareProfile x := by
    change t^(-(3 / 2:ℝ)) ≤ 96 * (1/(X*Real.log X^2))
    rw [mul_one_div, Real.rpow_neg ht.le]
    apply (le_div_iff₀ (denom_pos x)).2
    exact (inv_mul_le_iff₀ (Real.rpow_pos_of_pos ht _)).2 (by simpa only [mul_comm] using hden)
  have hscale : (t/2)^(-(3 / 2:ℝ)) ≤ 4*t^(-(3 / 2:ℝ)) := by
    rw [Real.div_rpow ht.le (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), neg_neg, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  linarith only [hscale,hbase]

private theorem jump_dominates_distance {x y : ℤ} (j : ℝ)
    (hy : |(y : ℝ)| < |(x : ℝ)| / 2) (hj : |(x : ℝ) - (y : ℝ)| ≤ j) :
    |(x : ℝ)| / 2 ≤ j := by
  have ht := abs_add_le ((x : ℝ) - (y : ℝ)) (y : ℝ)
  rw [sub_add_cancel] at ht
  linarith

private noncomputable def lossJumps (ℓ : ℕ → ℝ) (x : ℤ) : ℝ :=
  ∑' n : ℕ, (ℓ n * squareProfile (x + (n+1 : ℤ)) + ℓ n * squareProfile (x - (n+1 : ℤ)))

/-- The paired loss convolution is uniformly bounded by a constant times the
squared profile outside the finite core. No assumption about the convolution
inequality is made. -/
private theorem loss_convolution_bound (ℓ : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hℓ : ∀ n, 0 ≤ ℓ n) (hℓs : Summable ℓ)
    (hpol : ∀ n : ℕ, ℓ n ≤ E * (((n+1 : ℕ):ℝ))^(-(3 / 2:ℝ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℤ,
      Summable (fun n : ℕ =>
        ℓ n * squareProfile (x + (n+1 : ℤ)) + ℓ n * squareProfile (x - (n+1 : ℤ))) ∧
      lossJumps ℓ x ≤ B*squareProfile x := by
  let L := ∑' n, ℓ n
  let Q := ∑' z, squareProfile z
  refine ⟨16*L+768*E*Q, by
    have hL : 0 ≤ L := tsum_nonneg hℓ
    have hQ : 0 ≤ Q := tsum_nonneg (fun z => (squareProfile_pos z).le)
    positivity, ?_⟩
  intro x
  let yp (n : ℕ) := x + (n+1 : ℤ)
  let ym (n : ℕ) := x - (n+1 : ℤ)
  have hp : Function.Injective yp := by intro i j hij; dsimp [yp] at hij; omega
  have hm : Function.Injective ym := by intro i j hij; dsimp [ym] at hij; omega
  have hps : Summable (fun n => squareProfile (yp n)) := squareProfile_summable.comp_injective hp
  have hms : Summable (fun n => squareProfile (ym n)) := squareProfile_summable.comp_injective hm
  have hpQ : (∑' n, squareProfile (yp n)) ≤ Q :=
    Summable.tsum_le_tsum_of_inj yp hp
      (fun _ _ => (squareProfile_pos _).le) (fun _ => le_rfl) hps squareProfile_summable
  have hmQ : (∑' n, squareProfile (ym n)) ≤ Q :=
    Summable.tsum_le_tsum_of_inj ym hm
      (fun _ _ => (squareProfile_pos _).le) (fun _ => le_rfl) hms squareProfile_summable
  have hterm (n : ℕ) (y : ℤ) (hj : |(x : ℝ) - (y : ℝ)| ≤ (((n+1 : ℕ):ℝ))) :
      ℓ n*squareProfile y ≤ (8*squareProfile x)*ℓ n +
        (384*E*squareProfile x)*squareProfile y := by
    by_cases hy : |(x : ℝ)| / 2 ≤ |(y : ℝ)|
    · have H := mul_le_mul_of_nonneg_left (near_squareProfile_ratio hy) (hℓ n)
      have hnn : 0 ≤ (384*E*squareProfile x)*squareProfile y :=
        mul_nonneg (mul_nonneg (by positivity) (squareProfile_pos _).le) (squareProfile_pos _).le
      nlinarith only [H,hnn]
    · have hz : x ≠ 0 := by
        intro hh
        subst x
        exact hy (by simp)
      have hx : (1 : ℝ) ≤ |(x : ℝ)| := by
        have hzz : (1 : ℤ) ≤ |x| := by
          rw [abs_eq_max_neg]
          omega
        exact_mod_cast hzz
      have hd := jump_dominates_distance (((n+1 : ℕ):ℝ)) (lt_of_not_ge hy) hj
      have hpos : 0 < |(x : ℝ)| / 2 := by linarith
      have hpow := Real.rpow_le_rpow_of_nonpos hpos hd (by norm_num : -(3 / 2:ℝ) ≤ 0)
      have hℓ' := (hpol n).trans (mul_le_mul_of_nonneg_left
        (hpow.trans (far_power_le_profile x hx)) hE)
      have ht := mul_le_mul_of_nonneg_right hℓ' (squareProfile_pos y).le
      have hnn : 0 ≤ (8*squareProfile x)*ℓ n := mul_nonneg
        (mul_nonneg (by norm_num) (squareProfile_pos _).le) (hℓ n)
      nlinarith only [ht,hnn]
  have hplus (n : ℕ) : |(x : ℝ) - (yp n:ℝ)| ≤ (((n+1 : ℕ):ℝ)) := by
    have he : (x : ℝ) - (yp n:ℝ) = -(((n+1 : ℕ):ℝ)) := by dsimp [yp]; push_cast; ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
  have hminus (n : ℕ) : |(x : ℝ) - (ym n:ℝ)| ≤ (((n+1 : ℕ):ℝ)) := by
    have he : (x : ℝ) - (ym n:ℝ) = (((n+1 : ℕ):ℝ)) := by dsimp [ym]; push_cast; ring
    rw [he, abs_of_nonneg (by positivity)]
  let A := 8*squareProfile x
  let B := 384*E*squareProfile x
  let T (n : ℕ) := ℓ n*squareProfile (yp n) + ℓ n*squareProfile (ym n)
  let U (n : ℕ) := (2*A)*ℓ n + B*squareProfile (yp n) + B*squareProfile (ym n)
  have hU : Summable U := ((hℓs.mul_left (2*A)).add (hps.mul_left B)).add (hms.mul_left B)
  have ht (n : ℕ) : T n ≤ U n := by
    dsimp [T, U, A, B]
    linarith only [hterm n _ (hplus n), hterm n _ (hminus n)]
  have hT : Summable T := Summable.of_nonneg_of_le
    (fun n => add_nonneg (mul_nonneg (hℓ n) (squareProfile_pos _).le)
      (mul_nonneg (hℓ n) (squareProfile_pos _).le)) ht hU
  refine ⟨hT, ?_⟩
  change (∑' n, T n) ≤ _
  apply (hT.tsum_le_tsum ht hU).trans
  have hBe : 0 ≤ B := mul_nonneg (by positivity) (squareProfile_pos _).le
  have hqp := mul_le_mul_of_nonneg_left hpQ hBe
  have hqm := mul_le_mul_of_nonneg_left hmQ hBe
  change (∑' n, U n) ≤ _
  dsimp only [U]
  rw [(((hℓs.mul_left (2*A)).add (hps.mul_left B)).tsum_add (hms.mul_left B)),
    ((hℓs.mul_left (2*A)).tsum_add (hps.mul_left B)), tsum_mul_left, tsum_mul_left, tsum_mul_left]
  change (2*A)*L + B*(∑' n, squareProfile (yp n)) + B*(∑' n, squareProfile (ym n)) ≤ _
  dsimp only [A,B] at hqp hqm ⊢
  linarith only [hqp,hqm]

private theorem actual_loss_weight_bounds :
    (∀ n : ℕ, 0 ≤ lossWeight n ∧ lossWeight n ≤ (3 / 2:ℝ)*kernelWeight n) := by
  intro n
  have hρ : 0 ≤ rho := by unfold rho; positivity
  have hshape : 0 ≤ shapeWeight n := by unfold shapeWeight; positivity
  unfold lossWeight kernelWeight
  split_ifs <;> constructor <;> linarith

private theorem principal_weight_rpow (A x : ℝ) (hx : 0 < x) :
    A / (x * Real.sqrt x) = A*x^(-(3 / 2:ℝ)) := by
  rw [Real.sqrt_eq_rpow]
  have he : x * x^(1 / 2:ℝ) = x^(3 / 2:ℝ) := by
    rw [← show (1+(1 / 2:ℝ)) = 3 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one]
  rw [he, Real.rpow_neg hx.le, div_eq_mul_inv]

/-- Squared-profile terms of the actual loss kernel, with its singleton correction. -/
noncomputable def lossSummand (x : ℤ) (n : ℕ) : ℝ :=
  lossWeight n * discrepancyProfile (x + (n + 1 : ℤ)) ^ 2 +
    lossWeight n * discrepancyProfile (x - (n + 1 : ℤ)) ^ 2

/-- Actual paired nonlinear-loss weight applied to the squared profile. -/
noncomputable def lossConvolution (x : ℤ) : ℝ := ∑' n, lossSummand x n

/-- Uniform bound for the actual loss convolution, including finite-core x=0. -/
theorem actual_loss_convolution_bound :
    Summable (fun x : ℤ => discrepancyProfile x ^ 2) ∧
    (∀ x : ℤ, Summable (lossSummand x)) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℤ, lossConvolution x ≤ B * discrepancyProfile x ^ 2 := by
  obtain ⟨A, hA, hrem⟩ := actual_kernel_weight_strict_remainder
  have hs : Summable lossWeight :=
    Summable.of_nonneg_of_le (fun n => (actual_loss_weight_bounds n).1)
      (fun n => (actual_loss_weight_bounds n).2) (critical_shape_masses.2.2.1.mul_left (3 / 2:ℝ))
  have hk0 : 0 ≤ kernelWeight 0 := by unfold kernelWeight shapeWeight rho; positivity
  let C := A + 21 / 16 + kernelWeight 0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpol (n : ℕ) : lossWeight n ≤ (3 / 2 * C) * (((n + 1 : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ)) := by
    have hκ : kernelWeight n ≤ C * (((n + 1 : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ)) := by
      cases n with
      | zero => simp only [zero_add, Nat.cast_one, Real.one_rpow, mul_one]; dsimp [C]; linarith
      | succ k =>
        let m := k + 1 + 1
        have hm : 2 ≤ m := by dsimp [m]; omega
        have hm0 : 0 < (m : ℝ) := by positivity
        have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
        have h1 := (le_abs_self _).trans (hrem m hm)
        have he : m - 1 = k + 1 := by simp [m]
        rw [he, principal_weight_rpow _ _ hm0] at h1
        have hden : (m : ℝ) * Real.sqrt m ≤ (m : ℝ)^2 * Real.sqrt m := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          nlinarith [mul_nonneg hm0.le (sub_nonneg.mpr hm1)]
        have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 21 / 16)
          (by positivity : 0 < (m : ℝ) * Real.sqrt m) hden
        rw [principal_weight_rpow _ _ hm0] at h2
        have h3 := mul_nonneg hk0 (Real.rpow_nonneg hm0.le (-(3 / 2 : ℝ)))
        change kernelWeight (k + 1) ≤ C * (m : ℝ) ^ (-(3 / 2 : ℝ))
        dsimp [C]
        linarith only [h1, h2, h3]
    exact (actual_loss_weight_bounds n).2.trans
      ((mul_le_mul_of_nonneg_left hκ (by norm_num : (0 : ℝ) ≤ 3 / 2)).trans_eq (by ring))
  obtain ⟨B, hB, H⟩ := loss_convolution_bound lossWeight _ (by positivity : 0 ≤ 3 / 2 * C)
    (fun n => (actual_loss_weight_bounds n).1) hs hpol
  simp only [squareProfile_eq_square, lossJumps] at H
  refine ⟨squareProfile_summable.congr squareProfile_eq_square,
    fun x => (H x).1, B, hB, fun x => (H x).2⟩

#print axioms actual_loss_convolution_bound

end D5.S1.Words.Patterns.Separable.OccupiedNonlinearLoss
