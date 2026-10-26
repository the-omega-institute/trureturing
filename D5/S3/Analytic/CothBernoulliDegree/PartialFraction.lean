/- GID: D5/S3/Analytic/CothBernoulliDegree/PartialFraction
   generality: G
   mirror-B: D5/B/S3/Analytic/CothBernoulliDegree/PartialFraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.ZPow, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent, mathlib/module/Mathlib.NumberTheory.ZetaValues, mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries, mathlib/module/Mathlib.Analysis.Complex.RealDeriv]
   utility: none
   digest: Partial fractions and local differentiation of the signed hyperbolic cotangent remainder. -/

import Mathlib.Analysis.Calculus.Deriv.ZPow
import D5.S3.Analytic.CothBernoulliDegree.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.RealDeriv

open scoped BigOperators Topology
open Filter
namespace D5.S3.Analytic.CothBernoulliDegree.PartialFraction

private lemma coth_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => 2 / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2))
      (Real.cosh t / Real.sinh t / t - t ^ (-2 : ℤ)) := by
  let z : ℂ := (t : ℂ) * Complex.I / Real.pi
  have hz : z ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have hi := congrArg Complex.im hn
    simp [z, Complex.div_ofReal_im] at hi
    have : t / Real.pi > 0 := div_pos ht Real.pi_pos
    linarith
  have h := (summable_cotTerm hz).hasSum
  have he := cot_series_rep' hz
  have hs := h.congr_fun (fun k => (cotTerm_identity hz k).symm)
  rw [← he] at hs
  have hc : (Real.pi : ℂ) * Complex.cot (Real.pi * z) - 1 / z =
      ((Real.cosh t / Real.sinh t / t - t ^ (-2 : ℤ) : ℝ) : ℂ) *
        (-((Real.pi : ℂ) * (t : ℂ) * Complex.I)) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hsh : (Real.sinh t : ℂ) ≠ 0 := by exact_mod_cast (Real.sinh_pos_iff.mpr ht).ne'
    have hpiz : (Real.pi : ℂ) * z = (t : ℂ) * Complex.I := by dsimp [z]; field_simp
    rw [hpiz, Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    push_cast
    simp only [zpow_neg, zpow_ofNat]
    dsimp [z]
    field_simp
    simp [Complex.I_sq]
    <;> ring
  have hd : -((Real.pi : ℂ) * (t : ℂ) * Complex.I) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast ht.ne')) Complex.I_ne_zero)
  have hf (k : ℕ) :
      2 * z * (1 / ((z + (k + 1)) * (z - (k + 1)))) /
          (-((Real.pi : ℂ) * (t : ℂ) * Complex.I)) =
        ((2 / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2) : ℝ) : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hden : (t : ℂ) ^ 2 + ((Real.pi : ℂ) * ((k : ℂ) + 1)) ^ 2 ≠ 0 := by
      exact_mod_cast (show t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2 ≠ 0 by positivity)
    have hprod : (z + (k + 1)) * (z - (k + 1)) =
        -((t : ℂ) ^ 2 + ((Real.pi : ℂ) * ((k : ℂ) + 1)) ^ 2) / (Real.pi : ℂ) ^ 2 := by
      dsimp [z]
      field_simp
      <;> ring_nf
      <;> simp [Complex.I_sq]
    rw [hprod]
    push_cast
    dsimp [z]
    field_simp
    <;> ring
  have hres := (hs.div_const (-((Real.pi : ℂ) * (t : ℂ) * Complex.I))).congr_fun (fun k => (hf k).symm)
  rw [hc, mul_div_cancel_right₀ _ hd] at hres
  simpa only [Complex.ofReal_re] using Complex.hasSum_re hres

private lemma scaled_zeta_hasSum {r : ℕ} (hr : r ≠ 0) :
    HasSum (fun k : ℕ => 1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * r))
      ((-1 : ℝ) ^ (r + 1) * 2 ^ (2 * r - 1) *
        (bernoulli (2 * r) : ℝ) / (2 * r).factorial) := by
  have h0 := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat hr)
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by omega : 2 * r ≠ 0),
    div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h0
  convert h0.div_const (Real.pi ^ (2 * r)) using 1
  · ext k
    rw [mul_pow]
    ring
  · have hp : Real.pi ^ (2 * r) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
    field_simp
    <;> ring



open D5.S3.Analytic.CothBernoulliDegree.Defs

private lemma remainder_hasSum (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ =>
      2 * (-1 : ℝ) ^ n * t ^ (2 * n) /
        ((Real.pi * ((k : ℝ) + 1)) ^ (2 * n) *
          (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2))) (p n t) := by
  induction n with
  | zero => simpa [p] using coth_hasSum ht
  | succ n ih =>
    let c : ℝ := (2 : ℝ) ^ (2 * (n + 1)) * (bernoulli (2 * (n + 1)) : ℝ) /
      (2 * (n + 1)).factorial
    have hcoeff : HasSum (fun k : ℕ =>
        2 * (-1 : ℝ) ^ n * t ^ (2 * n) /
          (Real.pi * ((k : ℝ) + 1)) ^ (2 * (n + 1))) (c * t ^ (2 * n)) := by
      have h := (scaled_zeta_hasSum (r := n + 1) (by omega)).mul_left
        (2 * (-1 : ℝ) ^ n * t ^ (2 * n))
      convert h using 1
      · ext k
        ring
      · dsimp [c]
        have he : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        have hs : (-1 : ℝ) ^ n * (-1) ^ (n + 1 + 1) = 1 := by
          rw [← pow_add, show n + (n + 1 + 1) = 2 * (n + 1) by omega, pow_mul]
          norm_num
        rw [he, pow_succ (2 : ℝ), show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
          pow_succ (2 : ℝ)]
        have hf : (2 * (n + 1)).factorial ≠ 0 := Nat.factorial_ne_zero _
        field_simp
        rw [pow_succ (2 : ℝ)]
        linear_combination -(2 * (bernoulli (2 * n + 1 + 1) : ℝ) * 2 ^ (2 * n)) * hs
    have hp : p (n + 1) t = p n t - c * t ^ (2 * n) := by
      have he : (2 * ((n : ℤ) + 1)) - 2 = ((2 * n : ℕ) : ℤ) := by omega
      simp only [p]
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one, he, zpow_natCast]
      dsimp [c]
      ring
    rw [hp]
    apply (ih.sub hcoeff).congr_fun
    intro k
    have ha : Real.pi * ((k : ℝ) + 1) ≠ 0 := by positivity
    have hd : t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2 ≠ 0 := by positivity
    simp only [Nat.succ_eq_add_one, pow_succ (-1 : ℝ),
      show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    field_simp
    <;> ring

/-- The signed remainder is a positive-weighted rational-kernel series. -/
theorem P_eq_tsum (m n : ℕ) {t : ℝ} (ht : 0 < t) :
    P m n t = 2 * ∑' k : ℕ,
      (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
        (t ^ (m + 2 * n) / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2)) := by
  have h := (remainder_hasSum n ht).mul_left ((-1 : ℝ) ^ n * t ^ m / 2)
  have hsum : HasSum (fun k : ℕ =>
      (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
        (t ^ (m + 2 * n) / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2)))
      (P m n t / 2) := by
    convert h using 1
    · ext k
      have hs : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      rw [pow_add]
      field_simp
      nlinarith [hs]
    · dsimp [P]
      ring
  have he := hsum.tsum_eq
  linarith



private lemma inv_quad_formula {a : ℝ} (ha : 0 < a) (j : ℕ) (s : ℝ) :
    iteratedDeriv j (fun x : ℝ => 1 / (x ^ 2 + a ^ 2)) s =
      (iteratedDeriv j (fun z : ℂ => (z - (a : ℂ) * Complex.I)⁻¹) s).im / a := by
  induction j generalizing s with
  | zero =>
    simp only [iteratedDeriv_zero]
    simp [Complex.inv_im, Complex.normSq_apply, pow_two]
    field_simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv j (fun x : ℝ => 1 / (x ^ 2 + a ^ 2)) =
        fun s : ℝ =>
          (iteratedDeriv j (fun z : ℂ => (z - (a : ℂ) * Complex.I)⁻¹) s).im / a :=
      funext ih
    rw [he]
    have hz : (s : ℂ) - (a : ℂ) * Complex.I ≠ 0 := by
      intro hz
      have hi := congrArg Complex.im hz
      simp at hi
      linarith
    have hdiff : DifferentiableAt ℂ
        (iteratedDeriv j (fun z : ℂ => (z - (a : ℂ) * Complex.I)⁻¹)) (s : ℂ) := by
      have hf : (fun z : ℂ => (z - (a : ℂ) * Complex.I)⁻¹) =
          (fun z : ℂ => (1 * z - (a : ℂ) * Complex.I)⁻¹) := by simp
      rw [hf, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
      simp only [one_pow, one_mul, mul_one]
      exact ((differentiableAt_id.sub_const ((a : ℂ) * Complex.I)).zpow
        (Or.inl hz)).const_mul _
    have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hdiff.hasDerivAt.comp_ofReal
    simpa only [← iteratedDeriv_succ, Function.comp_def, Complex.imCLM_apply] using (him.div_const a).deriv

private lemma inv_quad_deriv_bound {a : ℝ} (ha : 0 < a) (j : ℕ) (s : ℝ) :
    ‖iteratedDeriv j (fun x : ℝ => 1 / (x ^ 2 + a ^ 2)) s‖ ≤
      j.factorial / a ^ (j + 2) := by
  rw [inv_quad_formula ha]
  have hf : (fun z : ℂ => (z - (a : ℂ) * Complex.I)⁻¹) =
      (fun z : ℂ => (1 * z - (a : ℂ) * Complex.I)⁻¹) := by simp
  rw [hf, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
  simp only [one_pow, one_mul, mul_one]
  have hn : a ≤ ‖(s : ℂ) - (a : ℂ) * Complex.I‖ := by
    simpa [abs_of_pos ha] using Complex.abs_im_le_norm ((s : ℂ) - (a : ℂ) * Complex.I)
  calc
    ‖(((-1 : ℂ) ^ j * (j.factorial : ℂ) *
        ((s : ℂ) - (a : ℂ) * Complex.I) ^ (-1 - (j : ℤ))).im) / a‖
        ≤ ‖(-1 : ℂ) ^ j * (j.factorial : ℂ) *
          ((s : ℂ) - (a : ℂ) * Complex.I) ^ (-1 - (j : ℤ))‖ / a := by
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha]
      exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) ha.le
    _ = (j.factorial : ℝ) / ‖(s : ℂ) - (a : ℂ) * Complex.I‖ ^ (j + 1) / a := by
      rw [show (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) by omega]
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast,
        one_mul, zpow_neg, zpow_natCast, norm_inv, norm_pow, div_eq_mul_inv]
    _ ≤ (j.factorial : ℝ) / a ^ (j + 1) / a := by
      gcongr
    _ = (j.factorial : ℝ) / a ^ (j + 2) := by
      rw [div_div]
      congr 1



private lemma kernel_smooth {a : ℝ} (ha : 0 < a) (M : ℕ) :
    ContDiff ℝ ⊤ (fun s : ℝ => s ^ M / (s ^ 2 + a ^ 2)) :=
  (contDiff_id.pow M).div ((contDiff_id.pow 2).add contDiff_const)
    (fun s => by positivity)

private lemma kernel_deriv_bounded (M r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∀ a : ℝ, 1 ≤ a → ∀ s : ℝ, |s| ≤ R →
      ‖iteratedDeriv r (fun x : ℝ => x ^ M / (x ^ 2 + a ^ 2)) s‖ ≤ C / a ^ 2 := by
  let C : ℝ := ∑ i ∈ Finset.range (r + 1),
    (r.choose i : ℝ) * (M.descFactorial i : ℝ) * R ^ (M - i) * ((r - i).factorial : ℝ)
  refine ⟨C, ?_⟩
  intro a ha s hs
  have ha0 : 0 < a := by linarith
  have hrec : ContDiff ℝ ⊤ (fun x : ℝ => 1 / (x ^ 2 + a ^ 2)) :=
    contDiff_const.div ((contDiff_id.pow 2).add contDiff_const) (fun x => by positivity)
  have he : (fun x : ℝ => x ^ M / (x ^ 2 + a ^ 2)) =
      (fun x : ℝ => x ^ M) * (fun x : ℝ => 1 / (x ^ 2 + a ^ 2)) := by
    ext x
    simp [div_eq_mul_inv]
  rw [he, iteratedDeriv_mul (by fun_prop) (hrec.of_le (by simp)).contDiffAt]
  calc
    ‖∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℝ) * iteratedDeriv i (fun x : ℝ => x ^ M) s *
          iteratedDeriv (r - i) (fun x : ℝ => 1 / (x ^ 2 + a ^ 2)) s‖
        ≤ ∑ i ∈ Finset.range (r + 1),
          ‖(r.choose i : ℝ) * iteratedDeriv i (fun x : ℝ => x ^ M) s *
            iteratedDeriv (r - i) (fun x : ℝ => 1 / (x ^ 2 + a ^ 2)) s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (r + 1),
        ((r.choose i : ℝ) * (M.descFactorial i : ℝ) * R ^ (M - i) *
          ((r - i).factorial : ℝ)) / a ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [iteratedDeriv_pow]
      simp only [norm_mul, norm_natCast, norm_pow, Real.norm_eq_abs, ← mul_assoc]
      have hb : ‖iteratedDeriv (r - i) (fun x : ℝ => 1 / (x ^ 2 + a ^ 2)) s‖ ≤
          ((r - i).factorial : ℝ) / a ^ 2 := by
        apply (inv_quad_deriv_bound ha0 (r - i) s).trans
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        rw [show r - i + 2 = 2 + (r - i) by omega, pow_add]
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ ha)
      calc
        (r.choose i : ℝ) * (M.descFactorial i : ℝ) * |s| ^ (M - i) *
            |iteratedDeriv (r - i) (fun x : ℝ => 1 / (x ^ 2 + a ^ 2)) s|
            ≤ (r.choose i : ℝ) * (M.descFactorial i : ℝ) * R ^ (M - i) *
                (((r - i).factorial : ℝ) / a ^ 2) := by
          simp only [Real.norm_eq_abs] at hb
          gcongr
        _ = _ := by ring
    _ = C / a ^ 2 := by rw [Finset.sum_div]


private noncomputable def weightedKernel (M n k : ℕ) : ℝ → ℝ := fun s =>
  (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
    (s ^ M / (s ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2))

private lemma weighted_smooth (M n k : ℕ) : ContDiff ℝ ⊤ (weightedKernel M n k) := by
  unfold weightedKernel
  exact contDiff_const.mul (kernel_smooth (a := Real.pi * ((k : ℝ) + 1)) (by positivity) M)

private lemma weighted_deriv_bounded (M n r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∀ k : ℕ, ∀ s : ℝ, |s| ≤ R →
      ‖iteratedDeriv r (weightedKernel M n k) s‖ ≤
        C / (Real.pi * ((k : ℝ) + 1)) ^ 2 := by
  obtain ⟨C, hC⟩ := kernel_deriv_bounded M r hR
  refine ⟨C, ?_⟩
  intro k s hs
  have ha : 1 ≤ Real.pi * ((k : ℝ) + 1) :=
    one_le_mul_of_one_le_of_one_le
      (show 1 ≤ Real.pi from by linarith [Real.one_le_pi_div_two])
      (show (1 : ℝ) ≤ (k : ℝ) + 1 from by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hw : ‖1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ ha)
  unfold weightedKernel
  rw [iteratedDeriv_const_mul_field, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans (hC _ ha s hs)

private lemma summable_majorant (C : ℝ) :
    Summable (fun k : ℕ => C / (Real.pi * ((k : ℝ) + 1)) ^ 2) := by
  simpa only [mul_one, mul_one_div, Nat.mul_one] using
    (scaled_zeta_hasSum (r := 1) one_ne_zero).summable.mul_left C

private lemma summable_series_deriv (M n r : ℕ) (t : ℝ) :
    Summable (fun k : ℕ => iteratedDeriv r (weightedKernel M n k) t) := by
  obtain ⟨C, hC⟩ := weighted_deriv_bounded M n r (abs_nonneg t)
  exact .of_norm_bounded (summable_majorant C) (fun k => hC k t le_rfl)

private lemma series_iteratedDeriv (M n r : ℕ) (t : ℝ) :
    iteratedDeriv r (fun s : ℝ => ∑' k : ℕ, weightedKernel M n k s) t =
      ∑' k : ℕ, iteratedDeriv r (weightedKernel M n k) t := by
  induction r generalizing t with
  | zero => simp
  | succ r ih =>
    have he : iteratedDeriv r (fun s : ℝ => ∑' k : ℕ, weightedKernel M n k s) =
        fun s : ℝ => ∑' k : ℕ, iteratedDeriv r (weightedKernel M n k) s := funext ih
    rw [iteratedDeriv_succ, he]
    let R : ℝ := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    obtain ⟨C, hC⟩ := weighted_deriv_bounded M n (r + 1) hR.le
    have hd (k : ℕ) (x : ℝ) (_ : x ∈ Set.Ioo (-R) R) :
        HasDerivAt (iteratedDeriv r (weightedKernel M n k))
          (iteratedDeriv (r + 1) (weightedKernel M n k) x) x := by
      simpa only [iteratedDeriv_succ] using
        ((weighted_smooth M n k).differentiable_iteratedDeriv r (by simp) x).hasDerivAt
    have hb (k : ℕ) (x : ℝ) (hx : x ∈ Set.Ioo (-R) R) :
        ‖iteratedDeriv (r + 1) (weightedKernel M n k) x‖ ≤
          C / (Real.pi * ((k : ℝ) + 1)) ^ 2 :=
      hC k x (abs_le.mpr ⟨by linarith [hx.1], hx.2.le⟩)
    have hx0 : (0 : ℝ) ∈ Set.Ioo (-R) R := ⟨by linarith, hR⟩
    have hxt : t ∈ Set.Ioo (-R) R := by
      dsimp [R]
      constructor <;> linarith [le_abs_self t, neg_abs_le t]
    exact (hasDerivAt_tsum_of_isPreconnected (summable_majorant C) isOpen_Ioo
      (convex_Ioo (-R) R).isPreconnected hd hb hx0
      (summable_series_deriv M n r 0) hxt).deriv

/-- The rational-kernel derivative series converges to half the derivative of `P`. -/
theorem hasSum_iteratedDeriv_P (m n r : ℕ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
      iteratedDeriv r (fun s : ℝ =>
        s ^ (m + 2 * n) / (s ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2)) t)
      (iteratedDeriv r (P m n) t / 2) := by
  have he : P m n =ᶠ[𝓝 t]
      (fun s : ℝ => 2 * ∑' k : ℕ, weightedKernel (m + 2 * n) n k s) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact P_eq_tsum m n hs
  have hd := he.iteratedDeriv_eq r
  rw [iteratedDeriv_const_mul_field, series_iteratedDeriv] at hd
  have hs := (summable_series_deriv (m + 2 * n) n r t).hasSum
  unfold weightedKernel at hs hd
  simp only [iteratedDeriv_const_mul_field] at hs hd
  convert hs using 1
  linarith

/-- Iterated differentiation commutes with the rational-kernel representation on the positive ray. -/
theorem iteratedDeriv_P (m n r : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv r (P m n) t = 2 * ∑' k : ℕ,
      (1 / (Real.pi * ((k : ℝ) + 1)) ^ (2 * n)) *
        iteratedDeriv r (fun s : ℝ =>
          s ^ (m + 2 * n) / (s ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2)) t := by
  have h := (hasSum_iteratedDeriv_P m n r ht).tsum_eq
  linarith

end D5.S3.Analytic.CothBernoulliDegree.PartialFraction
