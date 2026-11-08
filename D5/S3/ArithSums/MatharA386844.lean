/- GID: D5/S3/ArithSums/MatharA386844
   generality: I
   mirror-B: D5/B/S3/ArithSums/MatharA386844
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Native binomial series for Mathar's A386844 twin recurrences. -/

/- result:
   proof_shape: unmeasured; independent pre-freeze review required
   escape_witness: none claimed
   admission_basis: open-problem-resolution, conditional on the external registration
   Direct frozen dependencies: A308815DFiniteRecurrence.euler_coeff;
     OeisA386655LambertWEgfModSix.lagrange_subst
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27973. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Polynomial.Roots
import D5.S1.Recurrence.A308815DFiniteRecurrence
import D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix

/-! The literal binomial sum and its complete ordinary generating series. -/

open scoped BigOperators
namespace D5.S3.ArithSums.MatharA386844

def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (3*n+2).choose k * (3*n-k).choose (n-k)

def R3 (n : ℕ) : ℤ :=
  let m : ℤ := n
  3*m*(2*m-1)*(a n : ℤ) + (-353*m^2+1009*m-672)*(a (n-1) : ℤ) +
    (3938*m^2-15029*m+13872)*(a (n-2) : ℤ) -
    399*(3*m-4)*(3*m-5)*(a (n-3) : ℤ)

def R2 (n : ℕ) : ℤ :=
  let m : ℤ := n
  m*(2*m-1)*(5*m-8)*(a n : ℤ) +
    (-145*m^3+362*m^2-264*m+63)*(a (n-1) : ℤ) +
    3*(3*m-1)*(5*m-3)*(3*m-2)*(a (n-2) : ℤ)

noncomputable def A : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
noncomputable def D (j : ℕ) (f : PowerSeries ℚ) : PowerSeries ℚ :=
  (fun g : PowerSeries ℚ => PowerSeries.derivative g)^[j] f
noncomputable def op (r : ℕ) (p : Fin (r+1) → Polynomial ℚ)
    (f : PowerSeries ℚ) : PowerSeries ℚ :=
  ∑ j : Fin (r+1), (p j : PowerSeries ℚ) * D j.val f

def P : Prop :=
  (∀ n : ℕ, 3 ≤ n → R3 n = 0) ∧
  (∀ n : ℕ, 2 ≤ n → R2 n = 0) ∧
  (∃ r : ℕ, ∃ p : Fin (r+1) → Polynomial ℚ, (∃ j, p j ≠ 0) ∧ op r p A = 0)

open _root_.PowerSeries

private noncomputable def H : PowerSeries ℚ := (1 + X)^2 * (1 - X)⁻¹
private noncomputable def phi : PowerSeries ℚ := (1 + X)^3 * ((1 - X)^2)⁻¹

private theorem native_coefficient (n : ℕ) :
    coeff n (H * phi^n) = (a n : ℚ) := by
  have hi (d : ℕ) : ((1 - X : PowerSeries ℚ)^d)⁻¹ =
      (invOneSubPow ℚ d : PowerSeries ℚ) := by
    apply (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).2
    simpa only [invOneSubPow_inv_eq_one_sub_pow] using (invOneSubPow ℚ d).val_inv
  have hp : H * phi^n = (1 + X)^(3*n+2) *
      (invOneSubPow ℚ (2*n+1) : PowerSeries ℚ) := by
    simp only [H, phi, mul_pow, ← PowerSeries.inv_pow, ← pow_mul, ← mul_assoc]
    rw [show 3*n+2 = 2+3*n by omega, pow_add]
    rw [show 2*n+1 = 1+2*n by omega, ← hi, pow_add,
      PowerSeries.mul_inv_rev, pow_one]
    simp only [← PowerSeries.inv_pow]
    ring
  rw [hp, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold a
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Finset.mem_range_succ_iff.mp hk
  have hc : coeff k ((1 + X : PowerSeries ℚ)^(3*n+2)) =
      ((3*n+2).choose k : ℚ) := by
    have e : (1 + X : PowerSeries ℚ)^(3*n+2) =
        (((1 + Polynomial.X : Polynomial ℚ)^(3*n+2)) : PowerSeries ℚ) := by simp
    rw [← Polynomial.coe_one, ← Polynomial.coe_X, ← Polynomial.coe_add,
      ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  rw [hc]
  congr 1
  rw [invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk]
  congr 1
  rw [Nat.choose_symm_add]
  congr 1 <;> omega

private theorem weighted_lagrange (w : PowerSeries ℚ)
    (hw0 : constantCoeff w = 0) (hw : w = X * phi.subst w) (n : ℕ) :
    coeff n (derivative w * (H * phi⁻¹).subst w) = coeff n (H * phi^n) := by
  let B := H * phi⁻¹
  let F : PowerSeries ℚ := mk fun n => if n = 0 then 0 else coeff (n - 1) B / (n : ℚ)
  have hF : derivative F = B := by
    ext j
    simp only [coeff_derivative, F, coeff_mk, Nat.add_sub_cancel,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    exact div_mul_cancel₀ _ (by positivity)
  have hf : constantCoeff phi = 1 := by simp [phi, constantCoeff_inv]
  have hi : phi * phi⁻¹ = 1 := PowerSeries.mul_inv_cancel phi (by rw [hf]; norm_num)
  have hp : B * phi^(n+1) = H * phi^n := by
    dsimp only [B]
    calc
      _ = H * (phi * phi⁻¹) * phi^n := by ring
      _ = _ := by rw [hi, mul_one]
  have h := D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.lagrange_subst w phi F hw0 hw n
  rw [hF, hp] at h
  have hc := coeff_derivative (F.subst w) n
  rw [derivative_subst (.of_constantCoeff_zero hw0), hF,
    mul_comm (B.subst w) (derivative w)] at hc
  simp only [Nat.cast_add, Nat.cast_one] at h
  linear_combination hc + h

private theorem native_parametrization :
    ∃ w : PowerSeries ℚ, constantCoeff w = 0 ∧
      X * (1 + w)^3 = w * (1 - w)^2 ∧
      A * (1 - 5*w) = (1 + w)^3 ∧
      X * derivative w * (5*w - 1) = w * (w - 1) * (w + 1) := by
  have hf : constantCoeff phi = 1 := by simp [phi, constantCoeff_inv]
  let P : PowerSeries ℚ := X * phi⁻¹
  have hP0 : constantCoeff P = 0 := by simp [P]
  have hP1 : coeff 1 P = 1 := by
    change coeff (0 + 1) (X * phi⁻¹) = 1
    simp [coeff_succ_X_mul, coeff_zero_eq_constantCoeff, constantCoeff_inv, hf]
  let w : PowerSeries ℚ := P.substInvOfIsUnit (hP1 ▸ isUnit_one)
  have hw0 : constantCoeff w = 0 := constantCoeff_substInvOfIsUnit _ _
  have hws : HasSubst w := .of_constantCoeff_zero hw0
  have hwP : P.subst w = X := subst_substInvOfIsUnit_right _ hP0 _
  let v : PowerSeries ℚ := phi⁻¹.subst w
  have hx : (X : PowerSeries ℚ) = w * v := by
    simpa only [P, subst_mul hws, subst_X hws] using hwP.symm
  have hi : phi * phi⁻¹ = 1 := PowerSeries.mul_inv_cancel phi (by rw [hf]; norm_num)
  have hiv : phi.subst w * v = 1 := by
    have h := congrArg (substAlgHom hws) hi
    simpa only [map_mul, map_one, coe_substAlgHom] using h
  have hw : w = X * phi.subst w := by
    linear_combination -w * hiv - phi.subst w * hx
  have hA : A = derivative w * (H * phi⁻¹).subst w := by
    ext n
    rw [weighted_lagrange w hw0 hw n, native_coefficient]
    simp [A]
  have hH : H * (1 - X) = (1 + X)^2 := by
    dsimp only [H]
    rw [mul_assoc, PowerSeries.inv_mul_cancel (1 - X) (by simp), mul_one]
  have hphi : phi * (1 - X)^2 = (1 + X)^3 := by
    dsimp only [phi]
    rw [mul_assoc, PowerSeries.inv_mul_cancel ((1 - X)^2) (by simp), mul_one]
  have hb : (H * phi⁻¹) * (1 + X) = 1 - X := by
    apply (show IsUnit phi by rw [isUnit_iff_constantCoeff, hf]; exact isUnit_one).mul_right_cancel
    have hrel : H * (1 + X) = (1 - X) * phi := by
      apply (show IsUnit (1 - X : PowerSeries ℚ) by rw [isUnit_iff_constantCoeff]; simp).mul_right_cancel
      linear_combination (1 + X) * hH - hphi
    linear_combination (1 + X) * H * hi + hrel
  have hbw : (H * phi⁻¹).subst w * (1 + w) = 1 - w := by
    have h := congrArg (substAlgHom hws) hb
    simpa only [map_mul, map_add, map_sub, map_one, coe_substAlgHom, subst_X hws, subst_mul hws] using h
  have hphiw : phi.subst w * (1 - w)^2 = (1 + w)^3 := by
    have h := congrArg (substAlgHom hws) hphi
    simpa only [map_mul, map_pow, map_add, map_sub, map_one, coe_substAlgHom, subst_X hws] using h
  have he : X * (1 + w)^3 = w * (1 - w)^2 := by
    linear_combination -X * hphiw - (1 - w)^2 * hw
  have he' := congrArg (derivative (R := ℚ)) he
  simp only [map_mul, map_add, map_sub, derivative_pow, derivative_X, derivative_one,
    Derivation.leibniz, smul_eq_mul, Nat.cast_ofNat] at he'
  have hd : derivative w * (1 - w) * (1 - 5*w) = (1 + w)^4 := by
    have hfive : derivative (5 : PowerSeries ℚ) = 0 :=
      Derivation.map_natCast (derivative (R := ℚ)) 5
    linear_combination -(1 + w) * he' + 3 * derivative w * he
  refine ⟨w, hw0, he, ?_, ?_⟩
  · apply (show IsUnit (1 + w) by rw [isUnit_iff_constantCoeff]; simp [hw0]).mul_right_cancel
    rw [hA]
    linear_combination derivative w * (1 - 5*w) * hbw + hd
  · apply (show IsUnit (1 - w) by rw [isUnit_iff_constantCoeff]; simp [hw0]).mul_right_cancel
    linear_combination -X * hd - (1 + w) * he

private noncomputable def theta (f : PowerSeries ℚ) : PowerSeries ℚ := X * derivative f

private theorem theta_numerator_step (w f : PowerSeries ℚ) (m : ℕ) (N : Polynomial ℚ)
    (hw : X * derivative w * (5*w - 1) = w * (w - 1) * (w + 1))
    (h : f * (5*w - 1)^(m+1) = Polynomial.aeval w N) :
    theta f * (5*w - 1)^(m+3) = w * (w - 1) * (w + 1) *
      ((5*w - 1) * Polynomial.aeval w N.derivative -
        5*((m : PowerSeries ℚ)+1)*Polynomial.aeval w N) := by
  have h5 : derivative (5 : PowerSeries ℚ) = 0 := derivative_C
  have hd := congrArg (derivative (R := ℚ)) h
  simp only [h5, Derivation.leibniz, derivative_pow, map_sub, derivative_one,
    Derivation.map_natCast, Derivation.map_aeval, smul_eq_mul,
    Nat.add_sub_cancel, zero_mul, zero_add, sub_zero, Nat.cast_add, Nat.cast_one] at hd
  dsimp only [theta]
  simp only [pow_succ] at h hd ⊢
  linear_combination X * (5*w - 1)^2 * hd -
    (5*((m : PowerSeries ℚ)+1)*f*(5*w - 1)^(m+1) -
      Polynomial.aeval w N.derivative*(5*w - 1))*hw -
    5*((m : PowerSeries ℚ)+1)*w*(w - 1)*(w + 1)*h

private noncomputable def numeratorZero : Polynomial ℚ := -(Polynomial.X + 1)^3
private noncomputable def numeratorOne : Polynomial ℚ :=
  -2*Polynomial.X*(Polynomial.X - 1)*(Polynomial.X + 1)^3*(5*Polynomial.X - 4)
private noncomputable def numeratorTwo : Polynomial ℚ :=
  -2*Polynomial.X*(Polynomial.X - 1)*(Polynomial.X + 1)^3*
    (75*Polynomial.X^4 - 120*Polynomial.X^3 + 95*Polynomial.X^2 - 38*Polynomial.X - 4)
private noncomputable def numeratorThree : Polynomial ℚ :=
  -2*Polynomial.X*(Polynomial.X - 1)*(Polynomial.X + 1)^3*
    (1500*Polynomial.X^7 - 3225*Polynomial.X^6 + 3260*Polynomial.X^5 -
      2270*Polynomial.X^4 + 1268*Polynomial.X^3 - 301*Polynomial.X^2 - 164*Polynomial.X - 4)

private theorem theta_powers : ∃ w : PowerSeries ℚ,
    constantCoeff w = 0 ∧ X*(1+w)^3 = w*(1-w)^2 ∧
    A*(5*w-1) = Polynomial.aeval w numeratorZero ∧
    theta A*(5*w-1)^3 = Polynomial.aeval w numeratorOne ∧
    theta (theta A)*(5*w-1)^5 = Polynomial.aeval w numeratorTwo ∧
    theta (theta (theta A))*(5*w-1)^7 = Polynomial.aeval w numeratorThree := by
  obtain ⟨w, hw0, hx, hA, hw⟩ := native_parametrization
  have hzero : A*(5*w-1)^1 = Polynomial.aeval w numeratorZero := by
    simp only [numeratorZero, map_neg, map_pow, map_add, Polynomial.aeval_X, map_one, pow_one]
    linear_combination -hA
  have step0 := theta_numerator_step w A 0 numeratorZero hw hzero
  have hOne : theta A*(5*w-1)^3 = Polynomial.aeval w numeratorOne := by
    convert step0 using 1 <;> simp [numeratorZero, numeratorOne, Polynomial.derivative_pow,
      Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_add,
      map_ofNat, map_natCast] <;> norm_num <;> ring
  have step1 := theta_numerator_step w (theta A) 2 numeratorOne hw hOne
  have hTwo : theta (theta A)*(5*w-1)^5 = Polynomial.aeval w numeratorTwo := by
    convert step1 using 1 <;> simp [numeratorOne, numeratorTwo, Polynomial.derivative_pow,
      Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_add,
      map_ofNat, map_natCast] <;> norm_num <;> ring
  have step2 := theta_numerator_step w (theta (theta A)) 4 numeratorTwo hw hTwo
  have hThree : theta (theta (theta A))*(5*w-1)^7 = Polynomial.aeval w numeratorThree := by
    convert step2 using 1 <;> simp [numeratorTwo, numeratorThree, Polynomial.derivative_pow,
      Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_add,
      map_ofNat, map_natCast] <;> norm_num <;> ring
  exact ⟨w, hw0, hx, by simpa only [pow_one] using hzero, hOne, hTwo, hThree⟩

private theorem order3_numerator (w : ℚ) :
    (-6*w*(w - 1)^2*(w + 1)^9*(150*w^3 - 215*w^2 + 125*w + 4)) +
    (2*w*(w - 1)^2*(w + 1)^6*(26475*w^6 - 106710*w^5 + 164220*w^4 - 110034*w^3 + 28049*w^2 + 40*w + 8)) +
    (-2*w^2*(w - 1)^4*(w + 1)^3*(295350*w^6 - 677535*w^5 + 512220*w^4 - 274269*w^3 + 65915*w^2 + 22984*w - 217)) +
    (798*w^3*(w - 1)^6*(675*w^6 + 1620*w^5 + 760*w^4 - 932*w^3 + 483*w^2 - 56*w + 10)) +
    (-4*w*(w - 1)^2*(5*w - 1)^5*(135*w^3 - 260*w^2 + 139*w + 2)) = 0 := by ring

private theorem order2_numerator (w : ℚ) :
    (-6*w*(w - 1)^2*(w + 1)^6*(5000*w^6 - 18875*w^5 + 26575*w^4 - 19875*w^3 + 5825*w^2 + 330*w - 4)) +
    (2*w*(w - 1)^2*(w + 1)^3*(217500*w^9 - 548250*w^8 + 451575*w^7 - 183525*w^6 + 55350*w^5 - 41420*w^4 - 6989*w^3 + 21987*w^2 + 1012*w - 8)) +
    (-6*w^2*(w - 1)^4*(67500*w^9 + 158625*w^8 + 81200*w^7 - 38025*w^6 - 36200*w^5 + 62805*w^4 - 15824*w^3 + 6541*w^2 + 28*w + 70)) +
    (8*w*(w - 1)^2*(5*w - 1)^7) = 0 := by ring

private noncomputable def O3 (f : PowerSeries ℚ) : PowerSeries ℚ :=
  (6*theta (theta f) - 3*theta f) +
  X*(-353*theta (theta f) + 303*theta f - 16*f) +
  X^2*(3938*theta (theta f) + 723*theta f - 434*f) +
  X^3*(-3591*theta (theta f) - 10773*theta f - 7980*f)

private noncomputable def O2 (f : PowerSeries ℚ) : PowerSeries ℚ :=
  (10*theta (theta (theta f)) - 21*theta (theta f) + 8*theta f) +
  X*(-145*theta (theta (theta f)) - 73*theta (theta f) + 25*theta f + 16*f) +
  X^2*(135*theta (theta (theta f)) + 594*theta (theta f) + 867*theta f + 420*f)

set_option maxHeartbeats 1200000 in
private theorem forcing : O3 A = 8*X + 532*X^2 ∧ O2 A = -8*X := by
  obtain ⟨w, hw0, hx, hzero, hone, htwo, hthree⟩ := theta_powers
  have h0 := hzero
  have h1 := hone
  have h2 := htwo
  have h3 := hthree
  simp only [numeratorZero, numeratorOne, numeratorTwo, numeratorThree, map_add, map_sub,
    map_neg, map_mul, map_pow, map_one, map_ofNat, Polynomial.aeval_X] at h0 h1 h2 h3
  let d : PowerSeries ℚ := 1+w
  let q : PowerSeries ℚ := 5*w-1
  have hd : IsUnit d := by rw [isUnit_iff_constantCoeff]; simp [d, hw0]
  have hq : IsUnit q := by rw [isUnit_iff_constantCoeff]; norm_num [q, hw0]
  constructor
  · have hc : (-6*w*(w - 1)^2*(w + 1)^9*(150*w^3 - 215*w^2 + 125*w + 4)) +
    (2*w*(w - 1)^2*(w + 1)^6*(26475*w^6 - 106710*w^5 + 164220*w^4 - 110034*w^3 + 28049*w^2 + 40*w + 8)) +
    (-2*w^2*(w - 1)^4*(w + 1)^3*(295350*w^6 - 677535*w^5 + 512220*w^4 - 274269*w^3 + 65915*w^2 + 22984*w - 217)) +
    (798*w^3*(w - 1)^6*(675*w^6 + 1620*w^5 + 760*w^4 - 932*w^3 + 483*w^2 - 56*w + 10)) +
    (-4*w*(w - 1)^2*(5*w - 1)^5*(135*w^3 - 260*w^2 + 139*w + 2)) = (0 : PowerSeries ℚ) := by
      let p : Polynomial ℚ := (-6*Polynomial.X*(Polynomial.X - 1)^2*(Polynomial.X + 1)^9*(150*Polynomial.X^3 - 215*Polynomial.X^2 + 125*Polynomial.X + 4)) +
    (2*Polynomial.X*(Polynomial.X - 1)^2*(Polynomial.X + 1)^6*(26475*Polynomial.X^6 - 106710*Polynomial.X^5 + 164220*Polynomial.X^4 - 110034*Polynomial.X^3 + 28049*Polynomial.X^2 + 40*Polynomial.X + 8)) +
    (-2*Polynomial.X^2*(Polynomial.X - 1)^4*(Polynomial.X + 1)^3*(295350*Polynomial.X^6 - 677535*Polynomial.X^5 + 512220*Polynomial.X^4 - 274269*Polynomial.X^3 + 65915*Polynomial.X^2 + 22984*Polynomial.X - 217)) +
    (798*Polynomial.X^3*(Polynomial.X - 1)^6*(675*Polynomial.X^6 + 1620*Polynomial.X^5 + 760*Polynomial.X^4 - 932*Polynomial.X^3 + 483*Polynomial.X^2 - 56*Polynomial.X + 10)) +
    (-4*Polynomial.X*(Polynomial.X - 1)^2*(5*Polynomial.X - 1)^5*(135*Polynomial.X^3 - 260*Polynomial.X^2 + 139*Polynomial.X + 2))
      have hp : p = 0 := by
        apply Polynomial.funext
        intro t
        simpa only [p, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
          Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_X,
          Polynomial.eval_zero, Polynomial.eval_one] using order3_numerator t
      have h := congrArg (Polynomial.aeval w) hp
      simpa only [p, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
        map_zero, map_one, Polynomial.aeval_X] using h
    let L0 : PowerSeries ℚ := -6*w*(w-1)^2*(150*w^3-215*w^2+125*w+4)
    let L1 : PowerSeries ℚ := 2*(26475*w^6-106710*w^5+164220*w^4-110034*w^3+28049*w^2+40*w+8)
    let L2 : PowerSeries ℚ := -2*(295350*w^6-677535*w^5+512220*w^4-274269*w^3+65915*w^2+22984*w-217)
    let L3 : PowerSeries ℚ := 798*(675*w^6+1620*w^5+760*w^4-932*w^3+483*w^2-56*w+10)
    have hg0 : q^5*(6*theta (theta A)-3*theta A) = d^3*L0 := by
      dsimp only [q, d, L0]
      linear_combination 6*h2-3*(5*w-1)^2*h1
    have hg1 : q^5*(-353*theta (theta A)+303*theta A-16*A) = d^3*L1 := by
      dsimp only [q, d, L1]
      linear_combination -353*h2+303*(5*w-1)^2*h1-16*(5*w-1)^4*h0
    have hg2 : q^5*(3938*theta (theta A)+723*theta A-434*A) = d^3*L2 := by
      dsimp only [q, d, L2]
      linear_combination 3938*h2+723*(5*w-1)^2*h1-434*(5*w-1)^4*h0
    have hg3 : q^5*(-3591*theta (theta A)-10773*theta A-7980*A) = d^3*L3 := by
      dsimp only [q, d, L3]
      linear_combination -3591*h2-10773*(5*w-1)^2*h1-7980*(5*w-1)^4*h0
    have hz : d^6*q^5*(O3 A - (8*X+532*X^2)) = 0 := by
      calc
        _ = d^9*L0 + (X*d^3)*d^6*L1 + (X*d^3)^2*d^3*L2 +
            (X*d^3)^3*L3 - (8*(X*d^3)*d^3+532*(X*d^3)^2)*q^5 := by
              dsimp only [O3]
              linear_combination d^6*hg0 + X*d^6*hg1 + X^2*d^6*hg2 + X^3*d^6*hg3
        _ = 0 := by
          change X*(1+w)^3 = w*(1-w)^2 at hx
          dsimp only [d]
          rw [hx]
          dsimp only [L0, L1, L2, L3, q]
          linear_combination hc
    apply ((hd.pow 6).mul (hq.pow 5)).mul_left_cancel
    linear_combination hz
  · have hc : (-6*w*(w - 1)^2*(w + 1)^6*(5000*w^6 - 18875*w^5 + 26575*w^4 - 19875*w^3 + 5825*w^2 + 330*w - 4)) +
    (2*w*(w - 1)^2*(w + 1)^3*(217500*w^9 - 548250*w^8 + 451575*w^7 - 183525*w^6 + 55350*w^5 - 41420*w^4 - 6989*w^3 + 21987*w^2 + 1012*w - 8)) +
    (-6*w^2*(w - 1)^4*(67500*w^9 + 158625*w^8 + 81200*w^7 - 38025*w^6 - 36200*w^5 + 62805*w^4 - 15824*w^3 + 6541*w^2 + 28*w + 70)) +
    (8*w*(w - 1)^2*(5*w - 1)^7) = (0 : PowerSeries ℚ) := by
      let p : Polynomial ℚ := (-6*Polynomial.X*(Polynomial.X - 1)^2*(Polynomial.X + 1)^6*(5000*Polynomial.X^6 - 18875*Polynomial.X^5 + 26575*Polynomial.X^4 - 19875*Polynomial.X^3 + 5825*Polynomial.X^2 + 330*Polynomial.X - 4)) +
    (2*Polynomial.X*(Polynomial.X - 1)^2*(Polynomial.X + 1)^3*(217500*Polynomial.X^9 - 548250*Polynomial.X^8 + 451575*Polynomial.X^7 - 183525*Polynomial.X^6 + 55350*Polynomial.X^5 - 41420*Polynomial.X^4 - 6989*Polynomial.X^3 + 21987*Polynomial.X^2 + 1012*Polynomial.X - 8)) +
    (-6*Polynomial.X^2*(Polynomial.X - 1)^4*(67500*Polynomial.X^9 + 158625*Polynomial.X^8 + 81200*Polynomial.X^7 - 38025*Polynomial.X^6 - 36200*Polynomial.X^5 + 62805*Polynomial.X^4 - 15824*Polynomial.X^3 + 6541*Polynomial.X^2 + 28*Polynomial.X + 70)) +
    (8*Polynomial.X*(Polynomial.X - 1)^2*(5*Polynomial.X - 1)^7)
      have hp : p = 0 := by
        apply Polynomial.funext
        intro t
        simpa only [p, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_neg,
          Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_X,
          Polynomial.eval_zero, Polynomial.eval_one] using order2_numerator t
      have h := congrArg (Polynomial.aeval w) hp
      simpa only [p, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
        map_zero, map_one, Polynomial.aeval_X] using h
    let L0 : PowerSeries ℚ := -6*w*(w-1)^2*(5000*w^6-18875*w^5+26575*w^4-19875*w^3+5825*w^2+330*w-4)
    let L1 : PowerSeries ℚ := 2*(217500*w^9-548250*w^8+451575*w^7-183525*w^6+55350*w^5-41420*w^4-6989*w^3+21987*w^2+1012*w-8)
    let L2 : PowerSeries ℚ := -6*(67500*w^9+158625*w^8+81200*w^7-38025*w^6-36200*w^5+62805*w^4-15824*w^3+6541*w^2+28*w+70)
    have hg0 : q^7*(10*theta (theta (theta A))-21*theta (theta A)+8*theta A) = d^3*L0 := by
      dsimp only [q, d, L0]
      linear_combination 10*h3-21*(5*w-1)^2*h2+8*(5*w-1)^4*h1
    have hg1 : q^7*(-145*theta (theta (theta A))-73*theta (theta A)+25*theta A+16*A) = d^3*L1 := by
      dsimp only [q, d, L1]
      linear_combination -145*h3-73*(5*w-1)^2*h2+25*(5*w-1)^4*h1+16*(5*w-1)^6*h0
    have hg2 : q^7*(135*theta (theta (theta A))+594*theta (theta A)+867*theta A+420*A) = d^3*L2 := by
      dsimp only [q, d, L2]
      linear_combination 135*h3+594*(5*w-1)^2*h2+867*(5*w-1)^4*h1+420*(5*w-1)^6*h0
    have hz : d^3*q^7*(O2 A + 8*X) = 0 := by
      calc
        _ = d^6*L0 + (X*d^3)*d^3*L1 + (X*d^3)^2*L2 + 8*(X*d^3)*q^7 := by
              dsimp only [O2]
              linear_combination d^3*hg0 + X*d^3*hg1 + X^2*d^3*hg2
        _ = 0 := by
          dsimp only [d]
          rw [hx]
          dsimp only [L0, L1, L2, q]
          linear_combination hc
    apply ((hd.pow 3).mul (hq.pow 7)).mul_left_cancel
    linear_combination hz

private theorem recurrences :
    (∀ n : ℕ, 3 ≤ n → R3 n = 0) ∧ (∀ n : ℕ, 2 ≤ n → R2 n = 0) := by
  have ec (f : PowerSeries ℚ) (k : ℕ) : coeff k (theta f) = (k : ℚ)*coeff k f :=
    D5.S1.Recurrence.A308815DFiniteRecurrence.euler_coeff f k
  constructor
  · intro n hn
    have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := hn
    have shift1 (f : PowerSeries ℚ) : coeff n (X*f) = coeff (n-1) f := by
      simpa only [pow_one, if_pos h1] using (coeff_X_pow_mul' f 1 n)
    have shift2 (f : PowerSeries ℚ) : coeff n (X^2*f) = coeff (n-2) f := by
      rw [coeff_X_pow_mul', if_pos h2]
    have shift3 (f : PowerSeries ℚ) : coeff n (X^3*f) = coeff (n-3) f := by
      rw [coeff_X_pow_mul', if_pos h3]
    have h := congrArg (coeff n) forcing.1
    simp only [O3, map_add, map_sub, neg_mul, map_neg, coeff_ofNat_mul,
      shift1, shift2, shift3, ec, A, coeff_mk] at h
    have hx : coeff n (X : PowerSeries ℚ) = 0 := by
      rw [coeff_X, if_neg (by omega)]
    have hxx : coeff n (X^2 : PowerSeries ℚ) = 0 := by
      rw [coeff_X_pow, if_neg (by omega)]
    rw [hx, hxx] at h
    simp only [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3] at h
    have hq : (R3 n : ℚ) = 0 := by
      dsimp only [R3]
      push_cast
      linear_combination h
    exact_mod_cast hq
  · intro n hn
    have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have shift1 (f : PowerSeries ℚ) : coeff n (X*f) = coeff (n-1) f := by
      simpa only [pow_one, if_pos h1] using (coeff_X_pow_mul' f 1 n)
    have shift2 (f : PowerSeries ℚ) : coeff n (X^2*f) = coeff (n-2) f := by
      rw [coeff_X_pow_mul', if_pos h2]
    have h := congrArg (coeff n) forcing.2
    simp only [O2, map_add, map_sub, neg_mul, map_neg, coeff_ofNat_mul,
      shift1, shift2, ec, A, coeff_mk] at h
    have hx : coeff n (X : PowerSeries ℚ) = 0 := by
      rw [coeff_X, if_neg (by omega)]
    rw [hx] at h
    simp only [Nat.cast_sub h1, Nat.cast_sub h2] at h
    have hq : (R2 n : ℚ) = 0 := by
      dsimp only [R2]
      push_cast
      linear_combination h
    exact_mod_cast hq

private theorem homogeneous :
    420*A + (3612*X-177)*derivative A +
      (4593*X^2-1209*X+6)*derivative (derivative A) +
      (1539*X^3-943*X^2+29*X)*derivative (derivative (derivative A)) +
      (135*X^4-145*X^3+10*X^2)*derivative (derivative (derivative (derivative A))) = 0 := by
  have ho : (420*X^2+16*X)*A +
      (1596*X^3-193*X^2-3*X)*derivative A +
      (999*X^4-508*X^3+9*X^2)*derivative (derivative A) +
      (135*X^5-145*X^4+10*X^3)*derivative (derivative (derivative A)) = -8*X := by
    have h := forcing.2
    dsimp only [O2, theta] at h
    simp only [smul_eq_mul, Derivation.leibniz, derivative_X, derivative_one, map_add,
      map_sub, zero_mul, mul_zero, add_zero, zero_add, one_mul, mul_one] at h
    linear_combination h
  have hc420 : derivative (420 : PowerSeries ℚ) = 0 := derivative_C
  have hc16 : derivative (16 : PowerSeries ℚ) = 0 := derivative_C
  have hc1596 : derivative (1596 : PowerSeries ℚ) = 0 := derivative_C
  have hc193 : derivative (193 : PowerSeries ℚ) = 0 := derivative_C
  have hc3 : derivative (3 : PowerSeries ℚ) = 0 := derivative_C
  have hc999 : derivative (999 : PowerSeries ℚ) = 0 := derivative_C
  have hc508 : derivative (508 : PowerSeries ℚ) = 0 := derivative_C
  have hc9 : derivative (9 : PowerSeries ℚ) = 0 := derivative_C
  have hc135 : derivative (135 : PowerSeries ℚ) = 0 := derivative_C
  have hc145 : derivative (145 : PowerSeries ℚ) = 0 := derivative_C
  have hc10 : derivative (10 : PowerSeries ℚ) = 0 := derivative_C
  have hc8 : derivative (8 : PowerSeries ℚ) = 0 := derivative_C
  have h := congrArg (derivative (R := ℚ)) ho
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, derivative_pow,
    derivative_X, derivative_one, smul_eq_mul, Nat.cast_ofNat,
    hc420, hc16, hc1596, hc193, hc3, hc999, hc508, hc9, hc135, hc145, hc10, hc8] at h
  apply (PowerSeries.X_pow_mul_inj (k := 2)).mp
  simp only [mul_zero]
  linear_combination X*h - ho

/-- Both exact signed recurrences and ordinary D-finiteness of the literal native series. -/
theorem result : P := by
  refine ⟨recurrences.1, recurrences.2, ?_⟩
  let p : Fin 5 → Polynomial ℚ := fun j =>
    if j.val = 0 then 420 else
    if j.val = 1 then 3612*Polynomial.X-177 else
    if j.val = 2 then 4593*Polynomial.X^2-1209*Polynomial.X+6 else
    if j.val = 3 then 1539*Polynomial.X^3-943*Polynomial.X^2+29*Polynomial.X else
    135*Polynomial.X^4-145*Polynomial.X^3+10*Polynomial.X^2
  refine ⟨4, p, ⟨0, ?_⟩, ?_⟩
  · intro hp
    have h := congrArg (fun q : Polynomial ℚ => q.coeff 0) hp
    norm_num [p] at h
  · have cn (k : ℕ) : ((k : Polynomial ℚ) : PowerSeries ℚ) = k := by
      rw [← Polynomial.C_eq_natCast, Polynomial.coe_C, map_natCast]
    have co (k : ℕ) [k.AtLeastTwo] :
        ((ofNat(k) : Polynomial ℚ) : PowerSeries ℚ) = ofNat(k) := cn k
    simpa [op, p, D, Fin.sum_univ_succ, Function.iterate_succ_apply',
      Function.iterate_zero_apply, add_mul, sub_mul, add_assoc, co] using homogeneous

end D5.S3.ArithSums.MatharA386844
