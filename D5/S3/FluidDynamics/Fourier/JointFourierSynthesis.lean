/- GID: D5/S3/FluidDynamics/Fourier/JointFourierSynthesis
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/JointFourierSynthesis
   mirror-E: none(waiver:universal-analytic-estimate)
   anchors: []
   utility: none
   digest: Weighted Fourier synthesis of grade n+2 is jointly real C^n in coefficients and position. -/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Abel
open scoped ENNReal ContDiff BigOperators
open Set Filter Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000

set_option relaxedAutoImplicit false

namespace D5.S3.FluidDynamics.Fourier.JointFourierSynthesis

/-- For every natural differentiability order, including zero, decoding arbitrary
square-summable complex vector coefficients with weight of grade n+2 yields a
jointly real C^n map on the coefficient space and the two-dimensional real
coordinate space. The series is the unordered sum over the full integer lattice. -/
theorem joint_contdiff_fourier_synthesis : (∀ n : ℕ,
  let K := ℤ × ℤ
  let V := EuclideanSpace ℂ (Fin 2)
  let H := lp (fun _ : K => V) 2
  let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
  let dec : H → K → V := fun a k =>
    ((1 + ρ k) ^ (((n+2 : ℕ) : ℝ) / 2))⁻¹ • a k
  let character : K → (Fin 2 → ℝ) → ℂ := fun k x =>
    Complex.exp (Complex.I * ((k.1 : ℝ) * x 0 + (k.2 : ℝ) * x 1))
  ContDiff ℝ n (fun z : H × (Fin 2 → ℝ) =>
    ∑' k : K, character k z.2 • dec z.1 k) : Prop) := by
  classical
  intro n
  let K := ℤ × ℤ
  let V := EuclideanSpace ℂ (Fin 2)
  let H := lp (fun _ : K => V) 2
  let X := Fin 2 → ℝ
  let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
  let w : K → ℝ := fun k => ((1 + ρ k) ^ (((n+2 : ℕ) : ℝ) / 2))⁻¹
  let character : K → X → ℂ := fun k x =>
    Complex.exp (Complex.I * ((k.1 : ℝ) * x 0 + (k.2 : ℝ) * x 1))
  change ContDiff ℝ n (fun z : H × X => ∑' k : K, character k z.2 • (w k • z.1 k))
  let L : K → X →L[ℝ] ℂ := fun k =>
    (Complex.I • Complex.ofRealCLM).comp
      ((k.1 : ℝ) • ContinuousLinearMap.proj 0 +
       (k.2 : ℝ) • ContinuousLinearMap.proj 1)
  have hchar (k : K) : character k = Complex.exp ∘ L k := by
    ext x
    change Complex.exp (Complex.I * ((k.1 : ℂ) * (x 0 : ℂ) + (k.2 : ℂ) * (x 1 : ℂ))) =
      Complex.exp (Complex.I * (((k.1 : ℝ) * x 0 + (k.2 : ℝ) * x 1 : ℝ) : ℂ))
    push_cast
    rfl
  have hcd (k : K) (j : ℕ) : ContDiff ℝ j (character k) := by
    rw [hchar]
    exact Complex.contDiff_exp.comp (L k).contDiff
  have hL (k : K) : ‖L k‖ ≤ |(k.1 : ℝ)| + |(k.2 : ℝ)| := by
    apply (L k).opNorm_le_bound (by positivity)
    intro x
    have hx0 : |x 0| ≤ ‖x‖ := norm_le_pi_norm x 0
    have hx1 : |x 1| ≤ ‖x‖ := norm_le_pi_norm x 1
    change ‖Complex.I * (((k.1 : ℝ) * x 0 + (k.2 : ℝ) * x 1 : ℝ) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |(k.1 : ℝ) * x 0 + (k.2 : ℝ) * x 1| ≤
          |(k.1 : ℝ)| * |x 0| + |(k.2 : ℝ)| * |x 1| := by
        simpa only [abs_mul] using abs_add_le ((k.1 : ℝ) * x 0) ((k.2 : ℝ) * x 1)
      _ ≤ (|(k.1 : ℝ)| + |(k.2 : ℝ)|) * ‖x‖ := by nlinarith [abs_nonneg (k.1 : ℝ), abs_nonneg (k.2 : ℝ)]
  have hjet (j : ℕ) (k : K) (x : X) :
      ‖iteratedFDeriv ℝ j (character k) x‖ ≤ (|(k.1 : ℝ)| + |(k.2 : ℝ)|)^j := by
    rw [hchar, (L k).iteratedFDeriv_comp_right (Complex.contDiff_exp (𝕜 := ℝ) (n := j)) x le_rfl]
    have he : ‖iteratedFDeriv ℝ j Complex.exp (L k x)‖ = 1 := by
      rw [← (Complex.contDiff_exp (𝕜 := ℂ) (n := j)).contDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
      simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]
      simp [L, Complex.norm_exp]
    exact ((iteratedFDeriv ℝ j Complex.exp (L k x)).norm_compContinuousLinearMap_le _).trans
      (by simpa [he] using pow_le_pow_left₀ (norm_nonneg (L k)) (hL k) j)
  let B : K → X → H →L[ℝ] V := fun k x =>
    character k x • (w k • lp.evalCLM ℝ (fun _ : K => V) 2 k)
  let T : Finset K → X → H →L[ℝ] V := fun s x => ∑ k ∈ s, B k x
  have hB (k : K) (j : ℕ) : ContDiff ℝ j (B k) := (hcd k j).smul contDiff_const
  have hT (s : Finset K) (j : ℕ) : ContDiff ℝ j (T s) := by
    exact ContDiff.sum (fun k _ => hB k j)
  have hTjet (s : Finset K) (j : ℕ) (x : X) (u : Fin j → X) (a : H) :
      (iteratedFDeriv ℝ j (T s) x u) a =
        ∑ k ∈ s, (iteratedFDeriv ℝ j (character k) x u) • (w k • a k) := by
    change (iteratedFDeriv ℝ j (fun y => ∑ k ∈ s, B k y) x u) a = _
    rw [iteratedFDeriv_fun_sum_apply (fun k _ => (hB k j).contDiffAt)]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show B k = fun y => character k y • (w k • lp.evalCLM ℝ (fun _ : K => V) 2 k) from rfl,
      iteratedFDeriv_smul_const_apply (hcd k j).contDiffAt]
    rfl
  have hwpos (k : K) : 0 < w k := by
    dsimp [w, ρ]
    positivity
  have hsum (s : Finset K) (a : H) :
      (∑ k ∈ s, ‖a k‖) ≤ Real.sqrt (s.card : ℝ) * ‖a‖ := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => ‖a k‖) (fun _ => (1 : ℝ))
    have hn := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num) a s
    norm_num only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
      ENNReal.toReal_ofNat, Real.rpow_two] at hc hn
    have hq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) s.card)
    have hmul := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg (α := ℝ) s.card)
    apply (sq_le_sq₀ (Finset.sum_nonneg (fun k _ => norm_nonneg (a k))) (by positivity)).mp
    nlinarith
  have hTbound (s : Finset K) (j : ℕ) (x : X) (b : ℝ) (hb : 0 ≤ b)
      (hkb : ∀ k ∈ s, (|(k.1 : ℝ)| + |(k.2 : ℝ)|)^j * w k ≤ b) :
      ‖iteratedFDeriv ℝ j (T s) x‖ ≤ b * Real.sqrt (s.card : ℝ) := by
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro a
    rw [hTjet]
    calc
      ‖∑ k ∈ s, (iteratedFDeriv ℝ j (character k) x u) • (w k • a k)‖ ≤
          ∑ k ∈ s, ‖(iteratedFDeriv ℝ j (character k) x u) • (w k • a k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ s, (b * ∏ i, ‖u i‖) * ‖a k‖ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (hwpos k)]
        have hj := (iteratedFDeriv ℝ j (character k) x).le_opNorm u
        have hj' := mul_le_mul_of_nonneg_right (hjet j k x) (Finset.prod_nonneg (s := Finset.univ) (fun i _ => norm_nonneg (u i)))
        have hh := mul_le_mul_of_nonneg_right (hj.trans hj') (hwpos k).le
        have hb' := mul_le_mul_of_nonneg_right (hkb k hk) (Finset.prod_nonneg (s := Finset.univ) (fun i _ => norm_nonneg (u i)))
        have : ‖iteratedFDeriv ℝ j (character k) x u‖ * w k ≤ b * ∏ i, ‖u i‖ := by nlinarith only [hh, hb']
        nlinarith [mul_le_mul_of_nonneg_right this (norm_nonneg (a k))]
      _ = (b * ∏ i, ‖u i‖) * ∑ k ∈ s, ‖a k‖ := by rw [Finset.mul_sum]
      _ ≤ (b * ∏ i, ‖u i‖) * (Real.sqrt (s.card : ℝ) * ‖a‖) := by
        exact mul_le_mul_of_nonneg_left (hsum s a) (by positivity)
      _ = (b * Real.sqrt (s.card : ℝ) * ∏ i, ‖u i‖) * ‖a‖ := by ring
  let q : K → ℕ := fun k => max k.1.natAbs k.2.natAbs
  let A : ℕ → Finset K := fun m =>
    ((Finset.Icc (-(2^(m+1) : ℤ)) (2^(m+1))).product
      (Finset.Icc (-(2^(m+1) : ℤ)) (2^(m+1)))).filter
        (fun k => 2^m ≤ q k ∧ q k < 2^(m+1))
  have hqcast (k : K) : (q k : ℝ) = max |(k.1 : ℝ)| |(k.2 : ℝ)| := by
    dsimp [q]
    rw [Nat.cast_max]
    have hc (z : ℤ) : (z.natAbs : ℝ) = |(z:ℝ)| := by
      calc
        (z.natAbs : ℝ) = ((z.natAbs : ℤ) : ℝ) := (Int.cast_natCast z.natAbs).symm
        _ = ((|z| : ℤ) : ℝ) := congrArg (fun i : ℤ => (i : ℝ)) (Int.natCast_natAbs z)
        _ = |(z : ℝ)| := Int.cast_abs
    rw [hc, hc]
  have hAmem (m : ℕ) (k : K) : k ∈ A m ↔ 2^m ≤ q k ∧ q k < 2^(m+1) := by
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · intro h
      apply Finset.mem_filter.mpr
      refine ⟨?_, h⟩
      have h1 : k.1.natAbs ≤ 2^(m+1) := (le_max_left _ _).trans h.2.le
      have h2 : k.2.natAbs ≤ 2^(m+1) := (le_max_right _ _).trans h.2.le
      have h1' : |k.1| ≤ (2 : ℤ)^(m+1) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast h1
      have h2' : |k.2| ≤ (2 : ℤ)^(m+1) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast h2
      rw [Finset.product_eq_sprod]
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp h1'), Finset.mem_Icc.mpr (abs_le.mp h2')⟩
  have hAcard (m : ℕ) : Real.sqrt ((A m).card : ℝ) ≤ 5 * (2 : ℝ)^m := by
    have hi : (Finset.Icc (-(2^(m+1) : ℤ)) (2^(m+1))).card = 2 * 2^(m+1) + 1 := by
      rw [Int.card_Icc]
      have hz : (2:ℤ)^(m+1) + 1 - (-(2^(m+1):ℤ)) = ((2 * 2^(m+1) + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hz, Int.toNat_natCast]
    have hc := Finset.card_filter_le
      ((Finset.Icc (-(2^(m+1) : ℤ)) (2^(m+1))).product
        (Finset.Icc (-(2^(m+1) : ℤ)) (2^(m+1))))
      (fun k => 2^m ≤ q k ∧ q k < 2^(m+1))
    change (A m).card ≤ _ at hc
    rw [Finset.product_eq_sprod, Finset.card_product, hi] at hc
    have hc' : ((A m).card : ℝ) ≤ (2 * (2:ℝ)^(m+1) + 1)^2 := by
      rw [pow_two]
      exact_mod_cast hc
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hpow : 1 ≤ (2:ℝ)^m := one_le_pow₀ (by norm_num)
    rw [pow_succ (2:ℝ) m] at hc'
    nlinarith
  have hweight (m j : ℕ) (hj : j ≤ n) (k : K) (hk : k ∈ A m) :
      (|(k.1 : ℝ)| + |(k.2 : ℝ)|)^j * w k ≤ (4:ℝ)^n / ((2:ℝ)^m)^2 := by
    have hr : 0 < (2:ℝ)^m := by positivity
    have hr1 : 1 ≤ (2:ℝ)^m := one_le_pow₀ (by norm_num)
    have hlo : (2:ℝ)^m ≤ max |(k.1:ℝ)| |(k.2:ℝ)| := by
      rw [← hqcast]
      exact_mod_cast ((hAmem m k).mp hk).1
    have hhi : max |(k.1:ℝ)| |(k.2:ℝ)| ≤ 2 * (2:ℝ)^m := by
      rw [← hqcast, mul_comm 2, ← pow_succ]
      exact_mod_cast ((hAmem m k).mp hk).2.le
    have hab : |(k.1:ℝ)| + |(k.2:ℝ)| ≤ 4 * (2:ℝ)^m := by
      have h1 := (le_max_left |(k.1:ℝ)| |(k.2:ℝ)|).trans hhi
      have h2 := (le_max_right |(k.1:ℝ)| |(k.2:ℝ)|).trans hhi
      linarith
    have hrho : ((2:ℝ)^m)^2 ≤ 1 + ρ k := by
      dsimp [ρ]
      rcases le_max_iff.mp hlo with h | h
      · nlinarith [sq_abs (k.1:ℝ), sq_nonneg (k.2:ℝ), abs_nonneg (k.1:ℝ)]
      · nlinarith [sq_abs (k.2:ℝ), sq_nonneg (k.1:ℝ), abs_nonneg (k.2:ℝ)]
    have hw : w k ≤ (((2:ℝ)^m)^(n+2))⁻¹ := by
      apply inv_anti₀ (by positivity)
      have heq : (((2:ℝ)^m)^2) ^ (((n+2:ℕ):ℝ)/2) = ((2:ℝ)^m)^(n+2) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hr.le]
        rw [← Real.rpow_natCast _ (n+2)]
        congr 1
        push_cast
        ring
      rw [← heq]
      exact Real.rpow_le_rpow (by positivity) hrho (by positivity)
    have hjpow : (4:ℝ)^j ≤ (4:ℝ)^n := pow_le_pow_right₀ (by norm_num) hj
    have hjR : ((2:ℝ)^m)^j ≤ ((2:ℝ)^m)^n := pow_le_pow_right₀ hr1 hj
    calc
      (|(k.1 : ℝ)| + |(k.2 : ℝ)|)^j * w k ≤
          (4 * (2:ℝ)^m)^j * (((2:ℝ)^m)^(n+2))⁻¹ := by gcongr
      _ ≤ ((4:ℝ)^n * ((2:ℝ)^m)^n) * (((2:ℝ)^m)^(n+2))⁻¹ := by
        rw [mul_pow]
        gcongr
      _ = (4:ℝ)^n / ((2:ℝ)^m)^2 := by
        rw [pow_add]
        field_simp
  have hAbound (j : ℕ) (hj : j ≤ n) (m : ℕ) (x : X) :
      ‖iteratedFDeriv ℝ j (T (A m)) x‖ ≤ (5 * (4:ℝ)^n) * (1/2:ℝ)^m := by
    calc
      ‖iteratedFDeriv ℝ j (T (A m)) x‖ ≤
          ((4:ℝ)^n / ((2:ℝ)^m)^2) * Real.sqrt ((A m).card : ℝ) :=
        hTbound (A m) j x _ (by positivity) (hweight m j hj)
      _ ≤ ((4:ℝ)^n / ((2:ℝ)^m)^2) * (5 * (2:ℝ)^m) := by gcongr; exact hAcard m
      _ = (5 * (4:ℝ)^n) * (1/2:ℝ)^m := by
        rw [div_pow, one_pow]
        field_simp
        <;> ring
  have hgeom : Summable (fun m : ℕ => (5 * (4:ℝ)^n) * (1/2:ℝ)^m) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left _
  let S : X → H →L[ℝ] V := fun x => B 0 x + ∑' m : ℕ, T (A m) x
  have hS : ContDiff ℝ n S := by
    apply (hB 0 n).add
    apply contDiff_tsum (N := (n : ℕ∞)) (v := fun _ m => (5 * (4:ℝ)^n) * (1/2:ℝ)^m)
      (fun m => hT (A m) n) (fun _ _ => hgeom)
    intro j m x hj
    exact hAbound j (by exact_mod_cast hj) m x
  have hBsum (x : X) : Summable (fun m : ℕ => T (A m) x) := by
    apply Summable.of_norm_bounded hgeom
    intro m
    simpa only [norm_iteratedFDeriv_zero] using hAbound 0 (Nat.zero_le _) m x
  have hW (k : K) : 0 < 1 + ρ k := by dsimp [ρ]; positivity
  have hW1 (k : K) : 1 ≤ 1 + ρ k := by
    dsimp [ρ]
    nlinarith [sq_nonneg (k.1:ℝ), sq_nonneg (k.2:ℝ)]
  have hwle (k : K) : w k ≤ (1 + ρ k)⁻¹ := by
    dsimp [w]
    apply inv_anti₀ (hW k)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (hW1 k) (show (1:ℝ) ≤ ((n+2:ℕ):ℝ)/2 by push_cast; have := Nat.cast_nonneg (α := ℝ) n; linarith)
  let g : ℤ → ℝ := fun z => (1 + (z:ℝ)^2)⁻¹
  have hg : Summable g := by
    have hp := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
    have hh := (hasSum_ite_eq (0:ℤ) (1:ℝ)).summable.add hp
    apply hh.of_nonneg_of_le (fun _ => by dsimp [g]; positivity)
    intro z
    by_cases hz : z = 0
    · simp [g, hz]
    · simp only [if_neg hz, zero_add, one_div]
      exact inv_anti₀ (sq_pos_of_ne_zero (by exact_mod_cast hz)) (by linarith)
  have hsquare : Summable (fun k : K => w k ^ 2) := by
    have hh := hg.mul_of_nonneg hg (fun z => by dsimp [g]; positivity)
      (fun z => by dsimp [g]; positivity)
    apply hh.of_nonneg_of_le (fun _ => sq_nonneg _)
    intro k
    apply (pow_le_pow_left₀ (hwpos k).le (hwle k) 2).trans
    dsimp [g]
    rw [inv_pow, ← mul_inv_rev]
    apply inv_anti₀ (by positivity)
    dsimp [ρ]
    nlinarith [sq_nonneg (k.1:ℝ), sq_nonneg (k.2:ℝ),
      sq_nonneg ((k.1:ℝ)^2), sq_nonneg ((k.2:ℝ)^2),
      mul_nonneg (sq_nonneg (k.1:ℝ)) (sq_nonneg (k.2:ℝ))]
  have hmodeNorm (a : H) (x : X) (k : K) :
      ‖character k x • (w k • a k)‖ = ‖a k‖ * w k := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (hwpos k)]
    have hc : ‖character k x‖ = 1 := by simp [character, Complex.norm_exp]
    rw [hc, one_mul, mul_comm]
  have hfull (a : H) (x : X) : Summable (fun k : K => character k x • (w k • a k)) := by
    have ha : Summable (fun k : K => ‖a k‖ ^ (2:ℝ)) := by
      simpa using (lp.memℓp a).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    have hc := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
      Real.HolderConjugate.two_two (fun k => norm_nonneg (a k)) (fun k => (hwpos k).le)
      ha (by simpa only [Real.rpow_two] using hsquare)
    exact Summable.of_norm (hc.1.congr (fun k => (hmodeNorm a x k).symm))
  let C : ℕ → Finset K := fun r => match r with
    | 0 => {0}
    | m+1 => A m
  have hqzero (k : K) : q k = 0 ↔ k = 0 := by
    rcases k with ⟨k₁, k₂⟩
    change max k₁.natAbs k₂.natAbs = 0 ↔ (k₁,k₂) = ((0:ℤ),0)
    simp
  have hpartition : ∀ k : K, ∃! r : ℕ, k ∈ C r := by
    intro k
    by_cases hk : k = 0
    · subst k
      refine ⟨0, by simp [C], ?_⟩
      intro r hr
      cases r with
      | zero => rfl
      | succ m =>
        have hh := ((hAmem m 0).mp hr).1
        have hp : 0 < (2:ℕ)^m := by positivity
        simp only [q, Prod.fst_zero, Prod.snd_zero, Int.natAbs_zero, max_self] at hh
        omega
    · have hq : q k ≠ 0 := fun h => hk ((hqzero k).mp h)
      refine ⟨Nat.log 2 (q k) + 1, ?_, ?_⟩
      · exact (hAmem _ k).mpr ⟨Nat.pow_log_le_self 2 hq,
          Nat.lt_pow_succ_log_self (by norm_num) (q k)⟩
      · intro r hr
        cases r with
        | zero => simp [C, hk] at hr
        | succ m =>
          have hh := (hAmem m k).mp hr
          have he := Nat.log_eq_of_pow_le_of_lt_pow hh.1 hh.2
          exact congrArg (· + 1) he.symm
  have hgroup (a : H) (x : X) :
      HasSum (fun r : ℕ => ∑ k ∈ C r, character k x • (w k • a k))
        (∑' k : K, character k x • (w k • a k)) := by
    let e := Set.sigmaEquiv (fun r : ℕ => (C r : Set K)) hpartition
    have hh := (e.hasSum_iff).mpr (hfull a x).hasSum
    exact hh.sigma (fun r => (C r).hasSum (fun k => character k x • (w k • a k)))
  have heq (a : H) (x : X) : S x a = ∑' k : K, character k x • (w k • a k) := by
    have hs : HasSum (fun r : ℕ => ∑ k ∈ C r, character k x • (w k • a k)) (S x a) := by
      have hh := ((ContinuousLinearMap.apply ℝ V a).hasSum (hBsum x).hasSum)
      have he : ∀ m : ℕ, (T (A m) x) a = ∑ k ∈ A m, character k x • (w k • a k) := by
        intro m
        simp only [T, B, sum_apply, smul_apply]
        rfl
      have hh' : HasSum (fun m : ℕ => ∑ k ∈ A m, character k x • (w k • a k))
          ((∑' m : ℕ, T (A m) x) a) := hh.congr_fun (fun m => (he m).symm)
      have hh'' : HasSum (fun m : ℕ => ∑ k ∈ C (m+1), character k x • (w k • a k))
          ((∑' m : ℕ, T (A m) x) a) := hh'
      have hz := HasSum.zero_add
        (f := fun r : ℕ => ∑ k ∈ C r, character k x • (w k • a k)) hh''
      have hzero : (B 0 x) a = character 0 x • (w 0 • a 0) := rfl
      simpa only [C, Finset.sum_singleton, S, add_apply, hzero] using hz
    exact hs.unique (hgroup a x)
  have hjoint : ContDiff ℝ n (fun z : H × X => S z.2 z.1) :=
    (hS.comp contDiff_snd).clm_apply contDiff_fst
  convert hjoint using 1
  funext z
  exact (heq z.1 z.2).symm

end D5.S3.FluidDynamics.Fourier.JointFourierSynthesis
