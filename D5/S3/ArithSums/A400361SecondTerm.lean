/- GID: D5/S3/ArithSums/A400361SecondTerm
   generality: G
   mirror-B: D5/B/S3/ArithSums/A400361SecondTerm
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The exact second-order summatory assertion for the Pillai minus floor-gcd sequence. -/

import D5.S3.ArithSums.A400361PillaiMean
import D5.S3.Weil.ZetaGamma.GammaSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter Topology Finset
open scoped BigOperators Asymptotics

open D5.S3.ArithSums.A400361PillaiMean

namespace D5.S3.ArithSums.A400361SecondTerm

/-- The source floor-gcd function, with the positive source range. -/
def floorGcd (n : ℕ) : ℕ := ∑ k ∈ Icc 1 n, Nat.gcd n (n / k)

/-- Signed subtraction precedes all conversion to the reals. -/
def a (n : ℕ) : ℤ :=
  (D5.S3.Factorization.AlternatingGcdSumPillai.pillai n : ℤ) - (floorGcd n : ℤ)

/-- The real sum of the signed source values over every positive index up to N. -/
def S (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (a n : ℝ)

/-- The logarithmic derivative of the real Gamma function. -/
noncomputable def realDigamma (x : ℝ) : ℝ := deriv Real.Gamma x / Real.Gamma x

/-- The summand of the literal positive-index totient/digamma coefficient. -/
noncomputable def coefficientTerm (d : ℕ) : ℝ :=
  (Nat.totient d : ℝ) * (realDigamma (1 + 1 / (d : ℝ)) +
    Real.eulerMascheroniConstant) / (d : ℝ)^2

/-- The literal constant of OEIS A400361 revision 17. -/
noncomputable def C : ℝ :=
  (3 / Real.pi^2) * (-1 / 2 + 2 * Real.eulerMascheroniConstant -
    6 * deriv realZeta 2 / Real.pi^2) - Real.pi^2 / 12 -
      (1 / 2) * ∑' j : ℕ, coefficientTerm (j + 1)

/-- The exact error after subtracting the two terms specified in the source. -/
noncomputable def residual (N : ℕ) : ℝ :=
  S N - (3 / Real.pi^2) * (N : ℝ)^2 * Real.log N - C * (N : ℝ)^2

/-- The source's unrestricted second-order claim, including convergence of its constant. -/
def originalClaim : Prop :=
  Summable (fun j : ℕ => coefficientTerm (j + 1)) ∧
    (fun N : ℕ => residual N) =o[atTop] (fun N : ℕ => (N : ℝ)^2)

private lemma normalized_iff_littleO :
    (fun N : ℕ => residual N) =o[atTop] (fun N : ℕ => (N : ℝ)^2) ↔
      Tendsto (fun N : ℕ => residual N / (N : ℝ)^2) atTop (𝓝 0) := by
  apply Asymptotics.isLittleO_iff_tendsto'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have h : (N : ℝ)^2 ≠ 0 := by positivity
  exact fun hzero => False.elim (h hzero)

private lemma realDigamma_eq_complex {x : ℝ} (hx : 0 < x) :
    (realDigamma x : ℂ) = Complex.digamma (x : ℂ) := by
  have hc : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    (Complex.hasDerivAt_Gamma_of_re_pos (by simpa using hx)).differentiableAt
  have hr : DifferentiableAt ℝ Real.Gamma x :=
    (Real.hasDerivAt_Gamma_of_pos hx).differentiableAt
  have hco := hc.hasDerivAt.comp_ofReal
  have hro := hr.hasDerivAt.ofReal_comp
  have heq : (fun y : ℝ => Complex.Gamma (y : ℂ)) =
      (fun y : ℝ => (Real.Gamma y : ℂ)) := by
    funext y
    exact Complex.Gamma_ofReal y
  rw [heq] at hco
  have hd := hco.unique hro
  simp only [realDigamma, Complex.ofReal_div, Complex.digamma, logDeriv_apply,
    Complex.Gamma_ofReal, hd]

/-- A quotient fiber, including the exact lower edge and strict upper edge. -/
private lemma quotient_fiber (d m k ell : ℕ) (hd : 0 < d) (hk : 0 < k) :
    d * m / k = d * ell ↔ ∃ r : ℕ, m = k * ell + r ∧ d * r < k := by
  constructor
  · intro h
    have hlo : k * (d * ell) ≤ d * m := by
      rw [← h]
      exact Nat.mul_div_le _ _
    have hhi : d * m < k * (d * ell + 1) := by
      rw [← h]
      exact Nat.lt_mul_div_succ _ hk
    have hm : k * ell ≤ m := by nlinarith
    refine ⟨m - k * ell, (Nat.add_sub_of_le hm).symm, ?_⟩
    have he := Nat.sub_add_cancel hm
    nlinarith
  · rintro ⟨r, rfl, hr⟩
    apply Nat.div_eq_of_lt_le <;> nlinarith


private lemma hasSum_digamma_kernel (d : ℕ) (hd : 0 < d) :
    HasSum (fun j : ℕ => 1 / (((j : ℝ) + 1) * ((d : ℝ) * ((j : ℝ) + 1) + 1)))
      (realDigamma (1 + 1 / (d : ℝ)) + Real.eulerMascheroniConstant) := by
  by_cases hd1 : d = 1
  · subst d
    have hval : realDigamma 2 + Real.eulerMascheroniConstant = 1 := by
      have h : Complex.digamma (2 : ℂ) = 1 - (Real.eulerMascheroniConstant : ℂ) := by
        convert Complex.digamma_nat_add_one 1 using 1 <;> norm_num
      have hc := realDigamma_eq_complex (by norm_num : (0 : ℝ) < 2)
      norm_num only [Complex.ofReal_ofNat] at hc
      rw [← hc] at h
      have hh := congrArg Complex.re h
      norm_num at hh
      linarith
    convert hasSum_kernel_one using 1
    · funext j
      congr 1
      ring
    · convert hval using 1 <;> norm_num
  have hdr : 1 < (d : ℝ) := by exact_mod_cast (show 1 < d by omega)
  have hzpos : 0 < 1 / (d : ℝ) := by positivity
  have hzlt : 1 / (d : ℝ) < 1 := by exact (div_lt_one (by positivity)).mpr hdr
  have hz : ((1 / (d : ℝ) : ℝ) : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨j, hj⟩
    have hr := congrArg Complex.re hj
    norm_num at hr
    simp only [one_div] at hzpos hzlt
    have h0 : (0 : ℝ) < (j : ℝ) := by linarith
    have h1 : (j : ℝ) < 1 := by linarith
    have : (0 : ℤ) < j := by exact_mod_cast h0
    have : j < (1 : ℤ) := by exact_mod_cast h1
    omega
  have hc := Zeta23.DigammaSeries.hasSum_digamma_series hz
  have hnot (m : ℕ) : ((1 / (d : ℝ) : ℝ) : ℂ) ≠ -(m : ℂ) := by
    intro he
    have hre := congrArg Complex.re he
    norm_num at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp only [one_div] at hzpos
    linarith
  have hv : Complex.digamma (((1 / (d : ℝ) : ℝ) : ℂ)) +
      (Real.eulerMascheroniConstant : ℂ) + 1 / (((1 / (d : ℝ) : ℝ) : ℂ)) =
      ((realDigamma (1 + 1 / (d : ℝ)) + Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, realDigamma_eq_complex (by positivity)]
    rw [show ((1 + 1 / (d : ℝ) : ℝ) : ℂ) =
      (((1 / (d : ℝ) : ℝ) : ℂ)) + 1 by push_cast; ring,
      Complex.digamma_apply_add_one _ hnot]
    simp only [one_div]
    ring
  rw [hv] at hc
  have hr := Complex.hasSum_re hc
  convert hr using 1
  · funext j
    have he : 1 / ((j : ℂ) + 1) -
        1 / (((1 / (d : ℝ) : ℝ) : ℂ) + j + 1) =
        ((1 / (((j : ℝ) + 1) * ((d : ℝ) * ((j : ℝ) + 1) + 1)) : ℝ) : ℂ) := by
      push_cast
      have hj : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast (by positivity : (j : ℝ) + 1 ≠ 0)
      have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      have hjd : (d : ℂ) * ((j : ℂ) + 1) + 1 ≠ 0 := by
        exact_mod_cast (by positivity : (d : ℝ) * ((j : ℝ) + 1) + 1 ≠ 0)
      field_simp [hd0, hj, hjd]
      have hnew : 1 + (j : ℂ) * d + d ≠ 0 := by
        convert hjd using 1 <;> ring
      linear_combination -(mul_inv_cancel₀ hnew)
    rw [he, Complex.ofReal_re]

private lemma digamma_coefficient_bound (d : ℕ) (hd : 0 < d) :
    0 ≤ realDigamma (1 + 1 / (d : ℝ)) + Real.eulerMascheroniConstant ∧
      realDigamma (1 + 1 / (d : ℝ)) + Real.eulerMascheroniConstant ≤
        (Real.pi^2 / 6) / d := by
  have hsum := hasSum_digamma_kernel d hd
  constructor
  · exact hsum.nonneg (fun j => by positivity)
  · have hz : HasSum (fun j : ℕ => (1 : ℝ) / ((j + 1 : ℕ) : ℝ)^2)
        (Real.pi^2 / 6) := by
      simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    have hmajor := hz.div_const (d : ℝ)
    apply hasSum_le (fun j => ?_) hsum hmajor
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd
    push_cast
    have hp : 0 < (j : ℝ) + 1 := by positivity
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith

private lemma coefficient_summable : Summable (fun j : ℕ => coefficientTerm (j + 1)) := by
  have hp : Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ)^2) := by
    simpa using (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
  apply (hp.mul_left (Real.pi^2 / 6)).of_nonneg_of_le
  · intro j
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (digamma_coefficient_bound _ (by omega)).1)
      (sq_nonneg _)
  · intro j
    dsimp [coefficientTerm]
    have hd : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    have hphi : (Nat.totient (j + 1) : ℝ) ≤ (j + 1 : ℕ) := by
      exact_mod_cast Nat.totient_le (j + 1)
    have hb := digamma_coefficient_bound (j + 1) (by omega)
    have hpi : 0 ≤ Real.pi^2 / 6 := by positivity
    calc
      _ ≤ ((j + 1 : ℕ) : ℝ) * ((Real.pi^2 / 6) / (j + 1 : ℕ)) /
          ((j + 1 : ℕ) : ℝ)^2 := by
            apply div_le_div_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul hphi hb.2 hb.1 (by positivity)
      _ = _ := by field_simp


/-- Positive lattice points under the line A*r+B*j=N. -/
private def triangle (A B N : ℕ) : ℝ :=
  ∑ r ∈ Icc 1 (N / A), (((N - A * r) / B : ℕ) : ℝ)

private lemma triangle_bounds (A B N : ℕ) (hB : 0 < B) :
    0 ≤ ((N : ℝ) * (N / A : ℕ) -
      (A : ℝ) * (N / A : ℕ) * ((N / A : ℕ) + 1) / 2) / B - triangle A B N ∧
    ((N : ℝ) * (N / A : ℕ) -
      (A : ℝ) * (N / A : ℕ) * ((N / A : ℕ) + 1) / 2) / B - triangle A B N ≤ (N / A : ℕ) := by
  have hlinear : (∑ r ∈ Icc 1 (N / A), ((N : ℝ) - (A : ℝ) * r)) =
      (N : ℝ) * (N / A : ℕ) -
        (A : ℝ) * (N / A : ℕ) * ((N / A : ℕ) + 1) / 2 := by
    rw [sum_sub_distrib, sum_const, ← mul_sum, sum_Icc_cast]
    simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  have hpoint (r : ℕ) (hr : r ∈ Icc 1 (N / A)) :
      (B : ℝ) * (((N - A * r) / B : ℕ) : ℝ) ≤ (N : ℝ) - (A : ℝ) * r ∧
      (N : ℝ) - (A : ℝ) * r ≤
        (B : ℝ) * (((N - A * r) / B : ℕ) : ℝ) + B := by
    have har : A * r ≤ N := by
      calc A * r ≤ A * (N / A) := Nat.mul_le_mul_left _ (mem_Icc.mp hr).2
           _ ≤ N := Nat.mul_div_le _ _
    have hlo := Nat.mul_div_le (N - A * r) B
    have hhi := Nat.lt_mul_div_succ (N - A * r) hB
    have hlo' : (B : ℝ) * (((N - A * r) / B : ℕ) : ℝ) ≤
        (N : ℝ) - (A : ℝ) * r := by exact_mod_cast hlo
    have hhi' : (N : ℝ) - (A : ℝ) * r <
        (B : ℝ) * ((((N - A * r) / B : ℕ) : ℝ) + 1) := by
      exact_mod_cast hhi
    constructor
    · exact hlo'
    · linarith
  have hlo := sum_le_sum (fun r hr => (hpoint r hr).1)
  have hhi := sum_le_sum (fun r hr => (hpoint r hr).2)
  rw [← mul_sum, hlinear] at hlo
  rw [hlinear, sum_add_distrib, ← mul_sum, sum_const] at hhi
  simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hhi
  change (B : ℝ) * triangle A B N ≤ _ at hlo
  change _ ≤ (B : ℝ) * triangle A B N + (N / A : ℕ) * B at hhi
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hBp).mpr
    nlinarith
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hBp).mpr
    nlinarith


private lemma triangle_limit (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun N : ℕ => triangle A B N / (N : ℝ)^2) atTop
      (𝓝 (1 / (2 * (A : ℝ) * B))) := by
  have hq := quotient_ratio_limit A
  have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  let U : ℕ → ℝ := fun N => ((N : ℝ) * (N / A : ℕ) -
      (A : ℝ) * (N / A : ℕ) * ((N / A : ℕ) + 1) / 2) / B / (N : ℝ)^2
  have hU : Tendsto U atTop (𝓝 (1 / (2 * (A : ℝ) * B))) := by
    have h := ((hq.sub ((hq.pow 2).const_mul ((A : ℝ) / 2))).sub
      ((hq.mul hi).const_mul ((A : ℝ) / 2))).div_const (B : ℝ)
    have hAp : (A : ℝ) ≠ 0 := by positivity
    have hBp : (B : ℝ) ≠ 0 := by positivity
    have heval : (1 / (A : ℝ) - (A : ℝ) / 2 * (1 / (A : ℝ))^2 -
      (A : ℝ) / 2 * (1 / (A : ℝ) * 0)) / B = 1 / (2 * (A : ℝ) * B) := by
      field_simp
      <;> ring
    rw [heval] at h
    apply Tendsto.congr' (f₁ := fun N : ℕ =>
      (((N / A : ℕ) : ℝ) / N - (A : ℝ) / 2 * (((N / A : ℕ) : ℝ) / N)^2 -
        (A : ℝ) / 2 * ((((N / A : ℕ) : ℝ) / N) * (1 / (N : ℝ)))) / B) _ h
    filter_upwards [eventually_ge_atTop 1] with N hN
    dsimp [U]
    have hNr : (N : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring
  let E : ℕ → ℝ := fun N => U N - triangle A B N / (N : ℝ)^2
  have hE : Tendsto E atTop (𝓝 0) := by
    have htop : Tendsto (fun N : ℕ => (((N / A : ℕ) : ℝ) / N) * (1 / (N : ℝ)))
        atTop (𝓝 0) := by simpa using hq.mul hi
    apply squeeze_zero' _ _ htop
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hb := (triangle_bounds A B N hB).1
      dsimp [E, U]
      rw [← sub_div]
      exact div_nonneg hb (sq_nonneg _)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hb := (triangle_bounds A B N hB).2
      have hNr : (N : ℝ) ≠ 0 := by positivity
      dsimp [E, U]
      rw [← sub_div]
      calc
        _ ≤ ((N / A : ℕ) : ℝ) / (N : ℝ)^2 :=
          div_le_div_of_nonneg_right hb (sq_nonneg _)
        _ = _ := by field_simp
  convert hU.sub hE using 1
  · funext N
    dsimp [E]
    ring
  · simp

private lemma triangle_majorant (A B N : ℕ) (hA : 0 < A) (hB : 0 < B) :
    0 ≤ triangle A B N ∧ triangle A B N ≤ (N : ℝ)^2 / ((A : ℝ) * B) := by
  have hAp : (0 : ℝ) < A := by exact_mod_cast hA
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  constructor
  · exact sum_nonneg (fun r _ => Nat.cast_nonneg _)
  · have hq : ((N / A : ℕ) : ℝ) ≤ (N : ℝ) / A := by
      apply (le_div_iff₀ hAp).mpr
      exact_mod_cast Nat.div_mul_le_self N A
    calc
      triangle A B N ≤ ∑ r ∈ Icc 1 (N / A), (N : ℝ) / B := by
        apply sum_le_sum
        intro r hr
        apply (le_div_iff₀ hBp).mpr
        have h := (Nat.div_mul_le_self (N - A * r) B).trans (Nat.sub_le N (A * r))
        exact_mod_cast h
      _ = ((N / A : ℕ) : ℝ) * ((N : ℝ) / B) := by simp [nsmul_eq_mul]
      _ ≤ ((N : ℝ) / A) * ((N : ℝ) / B) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
      _ = _ := by ring

private lemma triangle_eq_card (A B X : ℕ) (hA : 0 < A) (hB : 0 < B) :
    triangle A B X =
      ((((Icc 1 X) ×ˢ (Icc 1 X)).filter
        (fun p : ℕ × ℕ => A * p.1 + B * p.2 ≤ X)).card : ℝ) := by
  have he (r : ℕ) : (Icc 1 X).filter (fun j => A * r + B * j ≤ X) =
      Icc 1 ((X - A * r) / B) := by
    ext j
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hj, hjX⟩, h⟩
      refine ⟨hj, (Nat.le_div_iff_mul_le hB).mpr ?_⟩
      nlinarith [Nat.sub_add_cancel (show A * r ≤ X by omega)]
    · rintro ⟨hj, h⟩
      have hh := (Nat.le_div_iff_mul_le hB).mp h
      have hr : A * r ≤ X := by
        by_contra hnot
        have : X - A * r = 0 := by omega
        rw [this] at hh
        nlinarith
      have hle : A * r + B * j ≤ X := by nlinarith [Nat.sub_add_cancel hr]
      refine ⟨⟨hj, ?_⟩, hle⟩
      nlinarith
  have hsum : (∑ r ∈ Icc 1 (X / A), (((X - A * r) / B : ℕ) : ℝ)) =
      ∑ r ∈ Icc 1 X, (((X - A * r) / B : ℕ) : ℝ) := by
    apply sum_subset
    · intro r hr
      exact mem_Icc.mpr ⟨(mem_Icc.mp hr).1,
        (mem_Icc.mp hr).2.trans (Nat.div_le_self X A)⟩
    · intro r hr hnot
      have hlt : X < A * r := by
        have hnr : ¬ r ≤ X / A := by
          intro h
          exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hr).1, h⟩)
        have := (Nat.le_div_iff_mul_le hA).not.mp hnr
        simpa [mul_comm] using this
      simp [Nat.sub_eq_zero_of_le hlt.le]
  rw [triangle, hsum]
  have hcard (r : ℕ) : (X - A * r) / B =
      ((Icc 1 X).filter (fun j => A * r + B * j ≤ X)).card := by
    rw [he]
    simp
  simp_rw [hcard]
  simp only [card_eq_sum_ones, sum_filter, sum_product, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

private lemma quotient_fiber_count (d ell X : ℕ) (hd : 0 < d) (hl : 0 < ell) :
    ((((Icc 1 X) ×ˢ (Icc 1 X)).filter
      (fun p : ℕ × ℕ => d * p.1 / p.2 = d * ell)).card : ℝ) =
      ((X / ell : ℕ) : ℝ) + triangle (d * ell + 1) ell X := by
  classical
  let T := (((Icc 1 X) ×ˢ (Icc 1 X)).filter
    (fun p : ℕ × ℕ => d * p.1 / p.2 = d * ell))
  let U := (((Icc 1 X) ×ˢ (Icc 1 X)).filter
    (fun p : ℕ × ℕ => (d * ell + 1) * p.1 + ell * p.2 ≤ X))
  have hboundary : (T.filter (fun p => p.1 = p.2 * ell)).card = X / ell := by
    have heq : (T.filter (fun p => p.1 = p.2 * ell)).card = (Icc 1 (X / ell)).card := by
      apply card_bij (fun p _ => p.2)
      · intro p hp
        simp only [mem_filter, mem_product, mem_Icc, T] at hp
        apply mem_Icc.mpr
        exact ⟨hp.1.1.2.1, (Nat.le_div_iff_mul_le hl).mpr (by omega)⟩
      · intro p hp q hq he
        simp only [mem_filter, T] at hp hq
        exact Prod.ext (hp.2.trans ((congrArg (fun t => t * ell) he).trans hq.2.symm)) he
      · intro k hk
        have hkk := mem_Icc.mp hk
        have hb := (Nat.le_div_iff_mul_le hl).mp hkk.2
        refine ⟨(k * ell, k), ?_, rfl⟩
        simp only [mem_filter, mem_product, mem_Icc, T]
        refine ⟨⟨⟨⟨by nlinarith, hb⟩, ⟨hkk.1, by nlinarith⟩⟩, ?_⟩, trivial⟩
        apply (quotient_fiber d (k * ell) k ell hd (by omega)).mpr
        exact ⟨0, by omega, by simp; omega⟩
    simpa using heq
  have hoff : (T.filter (fun p => ¬ p.1 = p.2 * ell)).card = U.card := by
    apply card_bij (fun p _ => (p.1 - p.2 * ell, p.2 - d * (p.1 - p.2 * ell)))
    · intro p hp
      simp only [mem_filter, mem_product, mem_Icc, T] at hp
      obtain ⟨r, hm, hr⟩ := (quotient_fiber d p.1 p.2 ell hd (by omega)).mp hp.1.2
      have her : p.1 - p.2 * ell = r := by omega
      have hsub := Nat.sub_add_cancel (by omega : d * r ≤ p.2)
      simp only [U, mem_filter, mem_product, mem_Icc, her]
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, ?_⟩
      nlinarith
    · intro p hp q hq he
      simp only [mem_filter, mem_product, mem_Icc, T] at hp hq
      obtain ⟨r, hmr, hkr⟩ := (quotient_fiber d p.1 p.2 ell hd (by omega)).mp hp.1.2
      obtain ⟨s, hms, hks⟩ := (quotient_fiber d q.1 q.2 ell hd (by omega)).mp hq.1.2
      have hr : p.1 - p.2 * ell = r := by omega
      have hs : q.1 - q.2 * ell = s := by omega
      have he1 := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      dsimp at he1 he2
      rw [hr, hs] at he1 he2
      have hrs : r = s := by omega
      have hmul := congrArg (fun t => d * t) hrs
      have hpeq : p.2 = q.2 := by omega
      apply Prod.ext
      · nlinarith
      · exact hpeq
    · intro p hp
      simp only [U, mem_filter, mem_product, mem_Icc] at hp
      let k := d * p.1 + p.2
      let m := k * ell + p.1
      have hmX : m ≤ X := by dsimp [m, k]; nlinarith
      have hkX : k ≤ X := by dsimp [m] at hmX; nlinarith
      refine ⟨(m, k), ?_, ?_⟩
      · simp only [T, mem_filter, mem_product, mem_Icc]
        refine ⟨⟨⟨⟨by dsimp [m]; nlinarith, hmX⟩,
          ⟨by dsimp [k]; nlinarith, hkX⟩⟩, ?_⟩, ?_⟩
        · apply (quotient_fiber d m k ell hd (by dsimp [k]; nlinarith)).mpr
          exact ⟨p.1, rfl, by dsimp [k]; omega⟩
        · dsimp [m]
          omega
      · apply Prod.ext <;> simp [m, k]
  have hsplit := card_filter_add_card_filter_not (s := T) (p := fun p => p.1 = p.2 * ell)
  rw [hboundary, hoff] at hsplit
  rw [triangle_eq_card (d * ell + 1) ell X (by omega) hl]
  exact_mod_cast hsplit.symm

private lemma divisor_prefix (f : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, f d (n / d)) =
      ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), f d m := by
  classical
  have hI : Ioc 0 N = Icc 1 N := by ext k; simp only [mem_Ioc, mem_Icc]; omega
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N),
        if p.1 * p.2 = n then f p.1 p.2 else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [← Nat.sum_divisorsAntidiagonal f]
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le
        (by have := (mem_Icc.mp hn).1; omega) (mem_Icc.mp hn).2, hI, sum_filter]
    _ = ∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N),
        if p.1 * p.2 ≤ N then f p.1 p.2 else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      have hpos : 1 ≤ p.1 * p.2 := by
        have := mem_product.mp hp
        have := (mem_Icc.mp this.1).1
        have := (mem_Icc.mp (mem_product.mp hp).2).1
        nlinarith
      simp [hpos]
    _ = _ := by
      rw [sum_product]
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter]
      congr 1
      ext m
      simp only [mem_filter, mem_Icc]
      have hdp : 0 < d := by have := (mem_Icc.mp hd).1; omega
      constructor
      · rintro ⟨hm, h⟩
        exact ⟨hm.1, (Nat.le_div_iff_mul_le hdp).mpr (by nlinarith)⟩
      · rintro ⟨hm, h⟩
        have hh := (Nat.le_div_iff_mul_le hdp).mp h
        exact ⟨⟨hm, h.trans (Nat.div_le_self N d)⟩, by nlinarith⟩

private lemma floorGcd_divisors (n : ℕ) (hn : 0 < n) :
    floorGcd n = ∑ d ∈ n.divisors, Nat.totient d *
      ((Icc 1 (n / d)).filter (fun k => d ∣ n / k)).card := by
  classical
  have he (k : ℕ) : Nat.gcd n (n / k) =
      ∑ d ∈ n.divisors, if d ∣ n / k then Nat.totient d else 0 := by
    have hset : (Nat.gcd n (n / k)).divisors = n.divisors.filter (fun d => d ∣ n / k) := by
      ext d
      simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hdn, hdq⟩, _⟩
        exact ⟨⟨hdn, hn.ne'⟩, hdq⟩
      · rintro ⟨⟨hdn, _⟩, hdq⟩
        exact ⟨⟨hdn, hdq⟩, Nat.gcd_ne_zero_left hn.ne'⟩
    rw [← Nat.sum_totient (Nat.gcd n (n / k)), hset, sum_filter]
  unfold floorGcd
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  apply congrArg (fun s : Finset ℕ => Nat.totient d * s.card)
  ext k
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hk, hkn⟩, hdk⟩
    refine ⟨⟨hk, ?_⟩, hdk⟩
    have hkpos : 0 < k := by omega
    have hqpos : 0 < n / k := by
      have h : 1 ≤ n / k := (Nat.le_div_iff_mul_le hkpos).mpr (by simpa using hkn)
      omega
    have hdq := Nat.le_of_dvd hqpos hdk
    have hmul := Nat.div_mul_le_self n k
    have hdp : 0 < d := Nat.pos_of_mem_divisors hd
    apply (Nat.le_div_iff_mul_le hdp).mpr
    nlinarith
  · rintro ⟨⟨hk, hkd⟩, hdk⟩
    exact ⟨⟨hk, hkd.trans (Nat.div_le_self n d)⟩, hdk⟩

private lemma floorGcd_prefix_divisors (N : ℕ) :
    (∑ n ∈ Icc 1 N, (floorGcd n : ℝ)) =
      ∑ d ∈ Icc 1 N, (Nat.totient d : ℝ) *
        ∑ m ∈ Icc 1 (N / d),
          (((Icc 1 m).filter (fun k => d ∣ d * m / k)).card : ℝ) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (Nat.totient d : ℝ) *
        (((Icc 1 (n / d)).filter (fun k => d ∣ d * (n / d) / k)).card : ℝ) := by
      apply sum_congr rfl
      intro n hn
      rw [floorGcd_divisors n (by have := (mem_Icc.mp hn).1; omega), Nat.cast_sum]
      apply sum_congr rfl
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), Nat.cast_mul]
    _ = _ := by
      rw [divisor_prefix (fun d m => (Nat.totient d : ℝ) *
        (((Icc 1 m).filter (fun k => d ∣ d * m / k)).card : ℝ)) N]
      simp_rw [mul_sum]

private lemma floor_fibers (d X : ℕ) (hd : 0 < d) :
    (∑ m ∈ Icc 1 X, (((Icc 1 m).filter (fun k => d ∣ d * m / k)).card : ℝ)) =
      ∑ ell ∈ Icc 1 X, (((X / ell : ℕ) : ℝ) + triangle (d * ell + 1) ell X) := by
  classical
  let T := (((Icc 1 X) ×ˢ (Icc 1 X)).filter
    (fun p : ℕ × ℕ => p.2 ≤ p.1 ∧ d ∣ d * p.1 / p.2))
  have hleft : (∑ m ∈ Icc 1 X,
      (((Icc 1 m).filter (fun k => d ∣ d * m / k)).card : ℝ)) = (T.card : ℝ) := by
    simp only [T, card_eq_sum_ones, sum_filter, sum_product, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply sum_congr rfl
    intro m hm
    have he : (Icc 1 X).filter (fun k => k ≤ m) = Icc 1 m := by
      ext k
      simp only [mem_filter, mem_Icc]
      have := (mem_Icc.mp hm).2
      omega
    rw [← he, sum_filter]
    apply sum_congr rfl
    intro k hk
    split_ifs <;> simp_all
  have hmap (p : ℕ × ℕ) (hp : p ∈ T) : (d * p.1 / p.2) / d ∈ Icc 1 X := by
    simp only [T, mem_filter, mem_product, mem_Icc] at hp
    have hk : 0 < p.2 := by omega
    have hq : d ≤ d * p.1 / p.2 :=
      (Nat.le_div_iff_mul_le hk).mpr (by nlinarith)
    have hlo : 1 ≤ (d * p.1 / p.2) / d :=
      (Nat.le_div_iff_mul_le hd).mpr (by simpa using hq)
    have hhi : (d * p.1 / p.2) / d ≤ p.1 := by
      have h := Nat.div_le_div_right (Nat.div_le_self (d * p.1) p.2) (c := d)
      simpa [Nat.mul_div_cancel_left _ hd] using h
    exact mem_Icc.mpr ⟨hlo, hhi.trans hp.1.1.2⟩
  have hfiber (ell : ℕ) (hl : ell ∈ Icc 1 X) :
      T.filter (fun p => (d * p.1 / p.2) / d = ell) =
        (((Icc 1 X) ×ˢ (Icc 1 X)).filter
          (fun p : ℕ × ℕ => d * p.1 / p.2 = d * ell)) := by
    ext p
    simp only [T, mem_filter]
    constructor
    · rintro ⟨⟨hp, hk, hdiv⟩, he⟩
      refine ⟨hp, ?_⟩
      rw [← he, Nat.mul_div_cancel' hdiv]
    · rintro ⟨hp, he⟩
      have hp' := mem_product.mp hp
      have hkp : 0 < p.2 := by have := (mem_Icc.mp hp'.2).1; omega
      have hqbound := Nat.div_mul_le_self (d * p.1) p.2
      rw [he] at hqbound
      have hmul : d * p.2 ≤ (d * ell) * p.2 := by
        have h := Nat.mul_le_mul_right p.2 (Nat.mul_le_mul_left d (mem_Icc.mp hl).1)
        simpa using h
      have hkm : p.2 ≤ p.1 := by nlinarith
      refine ⟨⟨hp, hkm, ?_⟩, ?_⟩
      · rw [he]
        exact dvd_mul_right d ell
      · rw [he, Nat.mul_div_cancel_left _ hd]
  have hcount := card_eq_sum_card_fiberwise hmap
  rw [hleft]
  rw [hcount, Nat.cast_sum]
  apply sum_congr rfl
  intro ell hl
  rw [hfiber ell hl]
  exact quotient_fiber_count d ell X hd (by have := (mem_Icc.mp hl).1; omega)

private lemma floorGcd_prefix_lattices (N : ℕ) :
    (∑ n ∈ Icc 1 N, (floorGcd n : ℝ)) =
      ∑ d ∈ Icc 1 N, (Nat.totient d : ℝ) *
        ∑ ell ∈ Icc 1 (N / d),
          ((((N / d) / ell : ℕ) : ℝ) + triangle (d * ell + 1) ell (N / d)) := by
  rw [floorGcd_prefix_divisors]
  apply sum_congr rfl
  intro d hd
  rw [floor_fibers d (N / d) (by have := (mem_Icc.mp hd).1; omega)]

private noncomputable def sigmaPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d : ℝ)

private lemma sigmaPrefix_eq (N : ℕ) :
    sigmaPrefix N = ∑ q ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / q), (m : ℝ) := by
  unfold sigmaPrefix
  have hs (n : ℕ) : (∑ d ∈ n.divisors, (d : ℝ)) =
      ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) := by
    exact (Nat.sum_div_divisors n (fun d => (d : ℝ))).symm
  simp_rw [hs]
  exact divisor_prefix (fun _ m => (m : ℝ)) N

private lemma boundary_eq_sigma (N : ℕ) :
    (∑ d ∈ Icc 1 N, (Nat.totient d : ℝ) *
      ∑ ell ∈ Icc 1 (N / d), (((N / d) / ell : ℕ) : ℝ)) = sigmaPrefix N := by
  calc
    _ = ∑ d ∈ Icc 1 N, ∑ ell ∈ Icc 1 (N / d),
        (Nat.totient d : ℝ) * ((N / (d * ell) : ℕ) : ℝ) := by
      simp only [mul_sum, Nat.div_div_eq_div_mul]
    _ = ∑ n ∈ Icc 1 N, (n : ℝ) * ((N / n : ℕ) : ℝ) := by
      rw [← divisor_prefix (fun d ell =>
        (Nat.totient d : ℝ) * ((N / (d * ell) : ℕ) : ℝ)) N]
      apply sum_congr rfl
      intro n hn
      have he (d : ℕ) (hd : d ∈ n.divisors) :
          (Nat.totient d : ℝ) * ((N / (d * (n / d)) : ℕ) : ℝ) =
            (Nat.totient d : ℝ) * ((N / n : ℕ) : ℝ) := by
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
      rw [sum_congr rfl he, ← sum_mul, ← Nat.cast_sum, Nat.sum_totient]
    _ = _ := by
      unfold sigmaPrefix
      rw [divisor_prefix (fun d _ => (d : ℝ)) N]
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      apply sum_congr rfl
      intro d hd
      ring

private lemma sigmaPrefix_limit :
    Tendsto (fun N : ℕ => sigmaPrefix N / (N : ℝ)^2) atTop (𝓝 (Real.pi^2 / 12)) := by
  let F : ℕ → ℕ → ℝ := fun N j =>
    (∑ m ∈ Icc 1 (N / (j + 1)), (m : ℝ)) / (N : ℝ)^2
  let L : ℕ → ℝ := fun j => (1 / ((j + 1 : ℕ) : ℝ)^2) / 2
  have hp : Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ)^2) := by
    simpa using (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
  have hpoint (j : ℕ) : Tendsto (fun N => F N j) atTop (𝓝 (L j)) := by
    have hq := quotient_ratio_limit (j + 1)
    have hi := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have ht := ((hq.pow 2).add (hq.mul hi)).div_const 2
    apply Tendsto.congr' (f₁ := fun N : ℕ =>
      ((((N / (j + 1) : ℕ) : ℝ) / N)^2 +
        (((N / (j + 1) : ℕ) : ℝ) / N) * (1 / (N : ℝ))) / 2) _
        (show Tendsto _ atTop (𝓝 (L j)) from ?_)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNr : (N : ℝ) ≠ 0 := by positivity
      dsimp [F]
      rw [sum_Icc_cast]
      field_simp
      <;> ring
    · simpa [L, div_pow] using ht
  have hbound (N j : ℕ) : ‖F N j‖ ≤ 1 / ((j + 1 : ℕ) : ℝ)^2 := by
    have hnonneg : 0 ≤ F N j := by dsimp [F]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    by_cases hN : N = 0
    · simp [F, hN]
      positivity
    have hNr : (0 : ℝ) < N := by positivity
    have hqr : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    have hq : ((N / (j + 1) : ℕ) : ℝ) / N ≤ 1 / ((j + 1 : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hNr hqr).mpr
      simp only [one_mul]
      exact_mod_cast Nat.div_mul_le_self N (j + 1)
    have hJ : (∑ m ∈ Icc 1 (N / (j + 1)), (m : ℝ)) ≤
        ((N / (j + 1) : ℕ) : ℝ)^2 := by
      rw [sum_Icc_cast]
      by_cases hz : N / (j + 1) = 0
      · simp [hz]
      · have h1 : (1 : ℝ) ≤ ((N / (j + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
        nlinarith
    calc
      F N j ≤ ((N / (j + 1) : ℕ) : ℝ)^2 / (N : ℝ)^2 :=
        div_le_div_of_nonneg_right hJ (sq_nonneg _)
      _ = (((N / (j + 1) : ℕ) : ℝ) / N)^2 := (div_pow _ _ _).symm
      _ ≤ (1 / ((j + 1 : ℕ) : ℝ))^2 := pow_le_pow_left₀ (by positivity) hq 2
      _ = _ := by simp
  have ht := tendsto_tsum_of_dominated_convergence hp hpoint
    (Eventually.of_forall (fun N j => hbound N j))
  have heq (N : ℕ) : (∑' j : ℕ, F N j) = sigmaPrefix N / (N : ℝ)^2 := by
    rw [tsum_eq_sum (s := range N)]
    · rw [sigmaPrefix_eq, sum_div]
      apply sum_bij (fun j _ => j + 1)
      · intro j hj
        simp only [mem_range] at hj
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro j hj k hk he
        omega
      · intro k hk
        exact ⟨k - 1, mem_range.mpr (by have := mem_Icc.mp hk; omega),
          by have := mem_Icc.mp hk; omega⟩
      · intro j hj
        rfl
    · intro j hj
      have hjn : N < j + 1 := by simp only [mem_range] at hj; omega
      simp [F, Nat.div_eq_of_lt hjn]
  have hL : (∑' j : ℕ, L j) = Real.pi^2 / 12 := by
    have hs : HasSum (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ)^2) (Real.pi^2 / 6) := by
      simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    convert (hs.div_const 2).tsum_eq using 1 <;> ring
  simpa only [heq, hL] using ht

private noncomputable def latticeTerm (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  (Nat.totient (p.1 + 1) : ℝ) *
    triangle ((p.1 + 1) * (p.2 + 1) + 1) (p.2 + 1) (N / (p.1 + 1)) / (N : ℝ)^2

private noncomputable def latticeLimit (p : ℕ × ℕ) : ℝ :=
  (Nat.totient (p.1 + 1) : ℝ) /
    (2 * ((p.1 + 1 : ℕ) : ℝ)^2 * (p.2 + 1 : ℕ) *
      (((p.1 + 1) * (p.2 + 1) + 1 : ℕ) : ℝ))

private lemma latticeTerm_limit (p : ℕ × ℕ) :
    Tendsto (fun N : ℕ => latticeTerm N p) atTop (𝓝 (latticeLimit p)) := by
  let d := p.1 + 1
  let ell := p.2 + 1
  have hd : 0 < d := by dsimp [d]; omega
  have hl : 0 < ell := by dsimp [ell]; omega
  have hq := quotient_ratio_limit d
  have ht := (triangle_limit (d * ell + 1) ell (by omega) hl).comp
    (Nat.tendsto_div_const_atTop hd.ne')
  have h := ((ht.mul (hq.pow 2)).const_mul (Nat.totient d : ℝ))
  apply Tendsto.congr' (f₁ := fun N : ℕ => (Nat.totient d : ℝ) *
    ((triangle (d * ell + 1) ell (N / d) / ((N / d : ℕ) : ℝ)^2) *
      (((N / d : ℕ) : ℝ) / N)^2)) _
      (show Tendsto _ atTop (𝓝 (latticeLimit p)) from ?_)
  · filter_upwards [(Nat.tendsto_div_const_atTop hd.ne').eventually
      (eventually_ge_atTop 1)] with N hN
    have hQ : ((N / d : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp [latticeTerm, d, ell] at *
    field_simp
  · have hv : (Nat.totient d : ℝ) *
        (1 / (2 * ((d * ell + 1 : ℕ) : ℝ) * ell) * (1 / (d : ℝ))^2) =
        latticeLimit p := by
      dsimp [latticeLimit, d, ell]
      push_cast
      field_simp
      <;> ring
    rw [hv] at h
    exact h

private lemma latticeTerm_bound (N : ℕ) (p : ℕ × ℕ) :
    ‖latticeTerm N p‖ ≤
      (1 / ((p.1 + 1 : ℕ) : ℝ)^2) * (1 / ((p.2 + 1 : ℕ) : ℝ)^2) := by
  let d := p.1 + 1
  let ell := p.2 + 1
  have hd : 0 < d := by dsimp [d]; omega
  have hl : 0 < ell := by dsimp [ell]; omega
  have hdr : (0 : ℝ) < d := by positivity
  have hlr : (0 : ℝ) < ell := by positivity
  have hb := triangle_majorant (d * ell + 1) ell (N / d) (by omega) hl
  have hphi : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have hq : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := by
    apply (le_div_iff₀ hdr).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  have hden : (d : ℝ) * ell ≤ ((d * ell + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  change |(Nat.totient d : ℝ) * triangle (d * ell + 1) ell (N / d) / (N : ℝ)^2| ≤ _
  rw [abs_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hb.1) (sq_nonneg _))]
  by_cases hN : N = 0
  · simp [hN]
    positivity
  have hNr : (0 : ℝ) < N := by positivity
  calc
    _ ≤ (d : ℝ) * (((N / d : ℕ) : ℝ)^2 /
        ((((d * ell + 1 : ℕ) : ℝ)) * ell)) / (N : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hphi hb.2 hb.1 (by positivity)
    _ ≤ (d : ℝ) * (((N : ℝ) / d)^2 /
        ((((d * ell + 1 : ℕ) : ℝ)) * ell)) / (N : ℝ)^2 := by
      gcongr
    _ ≤ (d : ℝ) * (((N : ℝ) / d)^2 / ((d : ℝ) * ell * ell)) / (N : ℝ)^2 := by
      gcongr
    _ = _ := by dsimp [d, ell]; field_simp; <;> ring

private lemma latticeLimit_summable : Summable latticeLimit := by
  have hp : Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ)^2) := by
    simpa using (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
  have hm := hp.mul_of_nonneg hp (fun j => by positivity) (fun j => by positivity)
  apply hm.of_norm_bounded
  intro p
  exact le_of_tendsto ((latticeTerm_limit p).norm)
    (Eventually.of_forall (fun N => latticeTerm_bound N p))

private lemma lattice_series_limit :
    Tendsto (fun N : ℕ => ∑' p : ℕ × ℕ, latticeTerm N p) atTop
      (𝓝 ((1 / 2 : ℝ) * ∑' j : ℕ, coefficientTerm (j + 1))) := by
  have hp : Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ)^2) := by
    simpa using (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
  have hm := hp.mul_of_nonneg hp (fun j => by positivity) (fun j => by positivity)
  have ht := tendsto_tsum_of_dominated_convergence hm latticeTerm_limit
    (Eventually.of_forall (fun N p => latticeTerm_bound N p))
  have heq : (∑' p : ℕ × ℕ, latticeLimit p) =
      (1 / 2 : ℝ) * ∑' j : ℕ, coefficientTerm (j + 1) := by
    rw [latticeLimit_summable.tsum_prod, ← tsum_mul_left]
    apply tsum_congr
    intro j
    have hs := (hasSum_digamma_kernel (j + 1) (by omega)).mul_left
      ((Nat.totient (j + 1) : ℝ) / (2 * ((j + 1 : ℕ) : ℝ)^2))
    calc
      (∑' k : ℕ, latticeLimit (j, k)) =
          (Nat.totient (j + 1) : ℝ) / (2 * ((j + 1 : ℕ) : ℝ)^2) *
            (realDigamma (1 + 1 / ((j + 1 : ℕ) : ℝ)) + Real.eulerMascheroniConstant) := by
        convert hs.tsum_eq using 1
        apply tsum_congr
        intro k
        dsimp [latticeLimit]
        push_cast
        field_simp
        <;> ring
      _ = _ := by dsimp [coefficientTerm]; ring
  rwa [heq] at ht

private lemma tsum_succ_eq_sum_Icc (f : ℕ → ℝ) (N : ℕ) (h : ∀ n, N < n → f n = 0) :
    (∑' j : ℕ, f (j + 1)) = ∑ n ∈ Icc 1 N, f n := by
  rw [tsum_eq_sum (s := range N)]
  · apply sum_bij (fun j _ => j + 1)
    · intro j hj
      have := mem_range.mp hj
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro j hj k hk he
      omega
    · intro k hk
      have := mem_Icc.mp hk
      exact ⟨k - 1, mem_range.mpr (by omega), by omega⟩
    · intro j hj
      rfl
  · intro j hj
    apply h
    simp only [mem_range] at hj
    omega

private lemma latticeSum_eq (N : ℕ) :
    (∑' p : ℕ × ℕ, latticeTerm N p) =
      (∑ d ∈ Icc 1 N, (Nat.totient d : ℝ) *
        ∑ ell ∈ Icc 1 (N / d), triangle (d * ell + 1) ell (N / d)) / (N : ℝ)^2 := by
  have hp : Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ)^2) := by
    simpa using (summable_nat_add_iff 1).mpr hasSum_zeta_two.summable
  have hm := hp.mul_of_nonneg hp (fun j => by positivity) (fun j => by positivity)
  have hs : Summable (latticeTerm N) := hm.of_norm_bounded (latticeTerm_bound N)
  rw [hs.tsum_prod]
  change (∑' j : ℕ, ∑' k : ℕ, (Nat.totient (j + 1) : ℝ) *
    triangle ((j + 1) * (k + 1) + 1) (k + 1) (N / (j + 1)) / (N : ℝ)^2) = _
  rw [tsum_succ_eq_sum_Icc (fun d => ∑' k : ℕ, (Nat.totient d : ℝ) *
    triangle (d * (k + 1) + 1) (k + 1) (N / d) / (N : ℝ)^2) N (by
      intro d hd
      simp [triangle, Nat.div_eq_of_lt hd])]
  rw [sum_div]
  apply sum_congr rfl
  intro d hd
  have hdp : 0 < d := by have := (mem_Icc.mp hd).1; omega
  rw [tsum_succ_eq_sum_Icc (fun ell => (Nat.totient d : ℝ) *
    triangle (d * ell + 1) ell (N / d) / (N : ℝ)^2) (N / d) (by
      intro ell hl
      have ha : N / d < d * ell + 1 := by nlinarith
      simp [triangle, Nat.div_eq_of_lt ha])]
  rw [mul_sum, sum_div]

private lemma floorGcd_prefix_limit :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (floorGcd n : ℝ)) / (N : ℝ)^2) atTop
      (𝓝 (Real.pi^2 / 12 + (1 / 2 : ℝ) * ∑' j : ℕ, coefficientTerm (j + 1))) := by
  have heq (N : ℕ) :
      (∑ n ∈ Icc 1 N, (floorGcd n : ℝ)) / (N : ℝ)^2 =
        sigmaPrefix N / (N : ℝ)^2 + ∑' p : ℕ × ℕ, latticeTerm N p := by
    rw [floorGcd_prefix_lattices]
    simp_rw [sum_add_distrib, mul_add]
    rw [sum_add_distrib, boundary_eq_sigma, add_div, latticeSum_eq]
  exact (sigmaPrefix_limit.add lattice_series_limit).congr (fun N => (heq N).symm)

/-- The complete positive-index second-order summatory formula, with its convergent
literal coefficient series and unrestricted natural-number little-o remainder. -/
theorem result : originalClaim := by
  refine ⟨coefficient_summable, normalized_iff_littleO.mpr ?_⟩
  have ht := (pillai_second_term.sub floorGcd_prefix_limit).sub_const C
  have he : (3 / Real.pi^2) * (-1 / 2 + 2 * Real.eulerMascheroniConstant -
      6 * deriv realZeta 2 / Real.pi^2) -
      (Real.pi^2 / 12 + (1 / 2 : ℝ) * ∑' j : ℕ, coefficientTerm (j + 1)) - C = 0 := by
    dsimp [C]
    ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hS : S N =
      (∑ n ∈ Icc 1 N, (D5.S3.Factorization.AlternatingGcdSumPillai.pillai n : ℝ)) -
        ∑ n ∈ Icc 1 N, (floorGcd n : ℝ) := by
    simp [S, a, Int.cast_sub, sum_sub_distrib]
  dsimp [residual]
  rw [hS]
  field_simp
  <;> ring

end D5.S3.ArithSums.A400361SecondTerm
