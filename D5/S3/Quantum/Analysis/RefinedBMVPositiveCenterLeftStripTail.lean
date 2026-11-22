/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterLeftStripTail
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth extension of the distinct-node tail and its repeated-node cancellation. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterTailFormula
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftStripProfile

/-! # The repeat-node tail correction as a finite exponential sum -/

open Finset Set

noncomputable section

namespace RefinedBMV.PositiveCenter

private def tailSum (p : ℕ) (h a : ℝ) : ℝ :=
  ∑ j ∈ range (p+1), Real.exp (-(h*((j : ℝ)+1)*a))

/-- The distinct-node correction extended smoothly through the lower
collision, with (a) and (v) as independent coordinates. -/
def leftStripCross (p : ℕ) (a v : ℝ) : ℝ :=
  let h := 3/(p : ℝ)
  let s := v-a
  Real.exp (-((3+h)*s)) * (1+h*upperTailGap h s*tailSum p h a)

private theorem gap_relation {h : ℝ} (hh : 0 < h) (t : ℝ) :
    h*upperTailGap h t = 1-Real.exp (-(h*t)) := by
  unfold upperTailGap
  field_simp [hh.ne']

/-- The smooth extension equals the original correction at distinct nodes. -/
theorem leftStripCross_eq {p : ℕ} (hp : 0 < p) {a v : ℝ} (ha : 0 < a) :
    let h := 3/(p : ℝ)
    leftStripCross p a v = upperTailCrossCorrection h a (v-a) := by
  let h := 3/(p : ℝ)
  let q := Real.exp (-(h*a))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hpH : h*(p : ℝ) = 3 := by dsimp [h]; field_simp [hpR.ne']
  have hgap : 0 < upperTailGap h a := by
    unfold upperTailGap
    exact div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh ha)))) hh
  have hsum : 1+tailSum p h a = ∑ j ∈ range (p+2), q^j := by
    rw [Finset.sum_range_succ', pow_zero, add_comm 1]
    congr 1
    exact sum_congr rfl fun j _ ↦ by
      unfold q
      rw [← Real.exp_nat_mul]
      push_cast
      congr 1
      ring
  have hpow : q^(p+2) = Real.exp (-((3+2*h)*a)) := by
    unfold q
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    linear_combination -a*hpH
  have hgeom := geom_sum_mul_neg q (p+2)
  rw [← hsum, hpow, ← gap_relation hh a] at hgeom
  have hcoef : (1-Real.exp (-((3+2*h)*a)))/upperTailGap h a =
      h+h*tailSum p h a := by
    apply (div_eq_iff hgap.ne').2
    linear_combination -hgeom
  change _ = upperTailCrossCorrection h a (v-a)
  unfold upperTailCrossCorrection leftStripCross
  change _ = Real.exp (-((3+h)*(v-a))) *
    (Real.exp (-(h*(v-a))) + upperTailGap h (v-a) *
      (1-Real.exp (-((3+2*h)*a)))/upperTailGap h a)
  have hQ : Real.exp (-(h*(v-a))) = 1-h*upperTailGap h (v-a) := by
    linarith only [gap_relation hh (v-a)]
  rw [mul_div_assoc, hcoef, hQ]
  ring

/-- The unweighted tail residual that enters the lower-collision profile. -/
def leftStripTailResidual (p : ℕ) (a v : ℝ) : ℝ :=
  let h := 3/(p : ℝ)
  (upperTailRepeatCorrection h v + upperTailRepeatCorrection h (v-a))/2 -
    leftStripCross p a v

private theorem hasDerivAt_repeat {h t : ℝ} (hh : 0 < h) :
    HasDerivAt (upperTailRepeatCorrection h)
      (-((3+h)*(3+2*h))*upperTailGap h t*Real.exp (-((3+h)*t))) t := by
  let α := 3+h
  have he := (((hasDerivAt_id' t).const_mul α).neg).exp
  have hd := (((hasDerivAt_upperTailGap (t := t) hh).const_mul α).const_add 1).mul he
  change HasDerivAt (upperTailRepeatCorrection h) _ t at hd
  apply hd.congr_deriv
  dsimp [α]
  linear_combination (3+h)*Real.exp (-((3+h)*t))*(gap_relation hh t)

private theorem tailSum_zero (p : ℕ) (h : ℝ) : tailSum p h 0 = (p : ℝ)+1 := by
  simp [tailSum]

private theorem hasDerivAt_tailSum_zero (p : ℕ) (h : ℝ) :
    HasDerivAt (tailSum p h) (-h*((p : ℝ)+1)*((p : ℝ)+2)/2) 0 := by
  have hd (j : ℕ) : HasDerivAt (fun a : ℝ ↦ Real.exp (-(h*((j : ℝ)+1)*a)))
      (-h*((j : ℝ)+1)) 0 := by
    have he := (((hasDerivAt_id' (0 : ℝ)).const_mul (h*((j : ℝ)+1))).neg).exp
    convert he using 1 <;> simp [neg_mul]
  have hsum := HasDerivAt.fun_sum fun j (_ : j ∈ range (p+1)) ↦ hd j
  change HasDerivAt (tailSum p h) _ 0 at hsum
  apply hsum.congr_deriv
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  have hmoment : (∑ j ∈ range (p+1), (j : ℝ))*2 = ((p : ℝ)+1)*p := by
    have hm : (∑ j ∈ range (p+1), j)*2 = (p+1)*p := by
      simpa using sum_range_id_mul_two (p+1)
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      congrArg (fun n : ℕ ↦ (n : ℝ)) hm
  linear_combination (-h/2)*hmoment

/-- The smooth residual vanishes to second order at the repeated node. -/
theorem leftStripTailResidual_zero {p : ℕ} (hp : 0 < p) (v : ℝ) :
    leftStripTailResidual p 0 v = 0 ∧ HasDerivAt (leftStripTailResidual p · v) 0 0 := by
  let h := 3/(p : ℝ)
  let α := 3+h
  let β := 3+2*h
  let U := upperTailRepeatCorrection h
  let F := upperTailGap h
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hpH : h*(p : ℝ) = 3 := by dsimp [h]; field_simp [hpR.ne']
  have hα : h*((p : ℝ)+1) = α := by dsimp [α]; linarith only [hpH]
  have hβ : h*((p : ℝ)+2) = β := by dsimp [β]; linarith only [hpH]
  have hcross : leftStripCross p 0 v = U v := by
    unfold leftStripCross U upperTailRepeatCorrection
    change Real.exp (-(α*(v-0))) * (1+h*F (v-0)*tailSum p h 0) = _
    rw [sub_zero, tailSum_zero]
    linear_combination (F v * Real.exp (-(α*v)))*hα
  constructor
  · change (U v+U (v-0))/2-leftStripCross p 0 v = 0
    rw [sub_zero, hcross]
    ring
  have hshift := (hasDerivAt_id' (0 : ℝ)).const_sub v
  have hU := (hasDerivAt_repeat (t := v-0) hh).comp 0 hshift
  have hF := (hasDerivAt_upperTailGap (t := v-0) hh).comp 0 hshift
  have he := (hshift.const_mul α).neg.exp
  have hd := he.mul (((hF.const_mul h).mul (hasDerivAt_tailSum_zero p h)).const_add 1)
  change HasDerivAt (leftStripCross p · v) _ 0 at hd
  have hcor := (((hU.const_add (U v)).div_const 2).sub hd)
  change HasDerivAt (leftStripTailResidual p · v) _ 0 at hcor
  apply hcor.congr_deriv
  let E := Real.exp (-(α*(v-0)))
  let Q := Real.exp (-(h*(v-0)))
  let m := tailSum p h 0
  change -(α*β)*F (v-0)*E*(-1)/2 -
    (E*(-(α*(-1)))*(1+h*F (v-0)*m) +
      E*(h*(Q*(-1))*m+h*F (v-0)*(-h*((p : ℝ)+1)*((p : ℝ)+2)/2))) = 0
  dsimp only [E, Q, m]
  rw [sub_zero, tailSum_zero]
  dsimp only [α, β] at hα hβ ⊢
  have hgap := gap_relation hh v
  -- The first moment of the finite sum makes the two derivatives identical.
  linear_combination
    (Real.exp (-((3+h)*v))*(Real.exp (-(h*v))-(3+h)*F v+h*((p : ℝ)+2)*F v/2))*hα +
    (Real.exp (-((3+h)*v))*(3+h)*F v/2)*hβ +
    (Real.exp (-((3+h)*v))*(3+h))*hgap

/-- The second lower-coordinate derivative and its upper-coordinate
derivative retain the signs of the two finite-moment contributions. -/
theorem leftStripCross_derivatives {p : ℕ} (hp : 0 < p) (a v : ℝ) :
    let h := 3/(p : ℝ)
    let α := 3+h
    let β := α+h
    let s := v-a
    let F := upperTailGap h s
    let q := Real.exp (-(h*s))
    let E := Real.exp (-(α*s))
    let w (j : ℕ) := α-h*((j : ℝ)+1)
    let M := ∑ j ∈ range (p+1), (w j)^2*Real.exp (-(h*((j : ℝ)+1)*a))
    let N := ∑ j ∈ range (p+1), (2*w j+h)*Real.exp (-(h*((j : ℝ)+1)*a))
    deriv (deriv (leftStripCross p · v)) a = E*(α^2+h*F*M-h*q*N) ∧
      deriv (fun y ↦ deriv (deriv (leftStripCross p · y)) a) v =
        E*(-α^3-h*α*F*M+h*q*(M+β*N)) := by
  let h := 3/(p : ℝ)
  let α := 3+h
  let β := α+h
  let F := upperTailGap h
  let Q (a v : ℝ) := Real.exp (-(h*(v-a)))
  let E (a v : ℝ) := Real.exp (-(α*(v-a)))
  let k (j : ℕ) := h*((j : ℝ)+1)
  let w (j : ℕ) := α-k j
  let e (j : ℕ) (a v : ℝ) := Real.exp (-(α*(v-a))-k j*a)
  let f₀ (j : ℕ) (a v : ℝ) := F (v-a)*e j a v
  let f₁ (j : ℕ) (a v : ℝ) := (F (v-a)*w j-Q a v)*e j a v
  let f₂ (j : ℕ) (a v : ℝ) := (F (v-a)*(w j)^2-Q a v*(2*w j+h))*e j a v
  let f₃ (j : ℕ) (a v : ℝ) := (-α*F (v-a)*(w j)^2+
    Q a v*((w j)^2+β*(2*w j+h)))*e j a v
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hl (r k x y : ℝ) : HasDerivAt (fun t ↦ Real.exp (-(r*(y-t))-k*t))
      ((r-k)*Real.exp (-(r*(y-x))-k*x)) x := by
    have hd := (((hasDerivAt_id' x).const_sub y).const_mul r).neg.sub
      ((hasDerivAt_id' x).const_mul k)
    exact hd.exp.congr_deriv (by dsimp; ring)
  have hr (r k x y : ℝ) : HasDerivAt (fun t ↦ Real.exp (-(r*(t-x))-k*x))
      (-r*Real.exp (-(r*(y-x))-k*x)) y := by
    have hd := ((((hasDerivAt_id' y).sub_const x).const_mul r).neg).sub_const (k*x)
    exact hd.exp.congr_deriv (by dsimp; ring)
  have hEl (x y : ℝ) : HasDerivAt (E · y) (α*E x y) x := by
    simpa only [E, zero_mul, sub_zero] using hl α 0 x y
  have hEr (x y : ℝ) : HasDerivAt (E x) (-α*E x y) y := by
    simpa only [E, zero_mul, sub_zero] using hr α 0 x y
  have hFl (x y : ℝ) : HasDerivAt (fun t ↦ F (y-t)) (-Q x y) x := by
    have hd := (hasDerivAt_upperTailGap (t := y-x) hh).comp x ((hasDerivAt_id' x).const_sub y)
    change HasDerivAt (fun t ↦ F (y-t)) (Q x y*(-1)) x at hd
    simpa only [mul_neg, mul_one] using hd
  have hFr (x y : ℝ) : HasDerivAt (fun t ↦ F (t-x)) (Q x y) y := by
    have hd := (hasDerivAt_upperTailGap (t := y-x) hh).comp y ((hasDerivAt_id' y).sub_const x)
    change HasDerivAt (fun t ↦ F (t-x)) (Q x y*1) y at hd
    simpa only [mul_one] using hd
  have hQl (x y : ℝ) : HasDerivAt (Q · y) (h*Q x y) x := by
    simpa only [Q, zero_mul, sub_zero] using hl h 0 x y
  have hQr (x y : ℝ) : HasDerivAt (Q x) (-h*Q x y) y := by
    simpa only [Q, zero_mul, sub_zero] using hr h 0 x y
  have h₁ (j : ℕ) (x y : ℝ) : HasDerivAt (f₀ j · y) (f₁ j x y) x := by
    have hd := (hFl x y).mul (hl α (k j) x y)
    change HasDerivAt (f₀ j · y) (-Q x y*e j x y+F (y-x)*((w j)*e j x y)) x at hd
    exact hd.congr_deriv (by dsimp only [f₁]; ring)
  have h₂ (j : ℕ) (x y : ℝ) : HasDerivAt (f₁ j · y) (f₂ j x y) x := by
    have hd := (((hFl x y).mul_const (w j)).sub (hQl x y)).mul (hl α (k j) x y)
    change HasDerivAt (f₁ j · y) _ x at hd
    apply hd.congr_deriv
    change ((-Q x y*(w j)-h*Q x y)*e j x y+
      (F (y-x)*w j-Q x y)*(w j*e j x y)) = f₂ j x y
    dsimp only [f₂]
    ring
  have h₃ (j : ℕ) (x y : ℝ) : HasDerivAt (f₂ j x) (f₃ j x y) y := by
    have hd := (((hFr x y).mul_const ((w j)^2)).sub
      ((hQr x y).mul_const (2*w j+h))).mul (hr α (k j) x y)
    change HasDerivAt (f₂ j x) _ y at hd
    apply hd.congr_deriv
    change (Q x y*(w j)^2-(-h*Q x y)*(2*w j+h))*e j x y+
      (F (y-x)*(w j)^2-Q x y*(2*w j+h))*(-α*e j x y) = f₃ j x y
    dsimp only [f₃, β]
    ring
  have hfactor (j : ℕ) (x y : ℝ) :
      e j x y = E x y*Real.exp (-(k j*x)) := by
    unfold e E
    rw [sub_eq_add_neg, Real.exp_add]
  have hExpand (y : ℝ) :
      (leftStripCross p · y) = fun x ↦ E x y+h*∑ j ∈ range (p+1), f₀ j x y := by
    funext x
    change E x y*(1+h*F (y-x)*tailSum p h x) =
      E x y+h*∑ j ∈ range (p+1), f₀ j x y
    simp only [f₀, hfactor, ← mul_assoc, ← Finset.mul_sum]
    dsimp only [tailSum, k]
    ring
  have hfirst (y : ℝ) :
      deriv (leftStripCross p · y) = fun x ↦ α*E x y+h*∑ j ∈ range (p+1), f₁ j x y := by
    funext x
    rw [hExpand y]
    exact ((hEl x y).add ((HasDerivAt.fun_sum fun j (_ : j ∈ range (p+1)) ↦
      h₁ j x y).const_mul h)).deriv
  have hsecond (x y : ℝ) :
      deriv (deriv (leftStripCross p · y)) x = α^2*E x y+h*∑ j ∈ range (p+1), f₂ j x y := by
    rw [hfirst y]
    have hd := ((hEl x y).const_mul α).add ((HasDerivAt.fun_sum
      fun j (_ : j ∈ range (p+1)) ↦ h₂ j x y).const_mul h)
    exact hd.deriv.trans (by ring)
  have hthird : deriv (fun y ↦ deriv (deriv (leftStripCross p · y)) a) v =
      -α^3*E a v+h*∑ j ∈ range (p+1), f₃ j a v := by
    rw [show (fun y ↦ deriv (deriv (leftStripCross p · y)) a) =
      fun y ↦ α^2*E a y+h*∑ j ∈ range (p+1), f₂ j a y from funext (hsecond a)]
    have hd := ((hEr a v).const_mul (α^2)).add ((HasDerivAt.fun_sum
      fun j (_ : j ∈ range (p+1)) ↦ h₃ j a v).const_mul h)
    exact hd.deriv.trans (by ring)
  let M := ∑ j ∈ range (p+1), (w j)^2*Real.exp (-(k j*a))
  let N := ∑ j ∈ range (p+1), (2*w j+h)*Real.exp (-(k j*a))
  change deriv (deriv (leftStripCross p · v)) a = E a v*(α^2+h*F (v-a)*M-h*Q a v*N) ∧
    deriv (fun y ↦ deriv (deriv (leftStripCross p · y)) a) v =
      E a v*(-α^3-h*α*F (v-a)*M+h*Q a v*(M+β*N))
  constructor
  · rw [hsecond a v]
    have hsum : (∑ j ∈ range (p+1), f₂ j a v) =
        E a v*F (v-a)*M-E a v*Q a v*N := by
      simp only [M, N, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      dsimp only [f₂]
      rw [hfactor]
      ring
    rw [hsum]
    ring
  · rw [hthird]
    have hsum : (∑ j ∈ range (p+1), f₃ j a v) =
        -E a v*α*F (v-a)*M+E a v*Q a v*M+E a v*Q a v*β*N := by
      simp only [M, N, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      dsimp only [f₃]
      rw [hfactor]
      ring
    rw [hsum]
    ring

/-- Signed estimates of the two derivative formulas use only the first
moment of the finite rate distribution. -/
theorem leftStripCross_derivative_bounds {p : ℕ} (hp : 11 ≤ p) {a v : ℝ}
    (ha : 0 ≤ a) (hgap : 6 ≤ v-a) :
    let h := 3/(p : ℝ)
    let U := upperTailRepeatCorrection h (v-a)
    |deriv (deriv (leftStripCross p · v)) a| ≤ (13/2)*U ∧
      |deriv (fun y ↦ deriv (deriv (leftStripCross p · y)) a) v| ≤ 22*U := by
  let h := 3/(p : ℝ)
  let α := 3+h
  let β := α+h
  let s := v-a
  let F := upperTailGap h s
  let q := Real.exp (-(h*s))
  let E := Real.exp (-(α*s))
  let w (j : ℕ) := α-h*((j : ℝ)+1)
  let e (j : ℕ) := Real.exp (-(h*((j : ℝ)+1)*a))
  let M := ∑ j ∈ range (p+1), (w j)^2*e j
  let N := ∑ j ∈ range (p+1), (2*w j+h)*e j
  let m := (p : ℝ)+1
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3/11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hpH : h*(p : ℝ) = 3 := by dsimp [h]; field_simp [hpR.ne']
  have hm : h*m = α := by dsimp only [m, α]; linarith only [hpH]
  have hw (j : ℕ) (hj : j ∈ range (p+1)) : 0 ≤ w j ∧ w j ≤ 3 := by
    have hjp : (j : ℝ) ≤ p := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hj₀ : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hmj := mul_le_mul_of_nonneg_left hjp hh.le
    have hz := mul_nonneg hh.le hj₀
    dsimp only [w, α]
    constructor <;> linarith only [hmj, hpH, hz]
  have he (j : ℕ) : 0 ≤ e j ∧ e j ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg (by positivity : 0 ≤ h*((j : ℝ)+1)) ha))⟩
  have hsumJ : (∑ j ∈ range (p+1), (j : ℝ))*2 = m*p := by
    have hmN : (∑ j ∈ range (p+1), j)*2 = (p+1)*p := by
      simpa using sum_range_id_mul_two (p+1)
    simpa only [m, Nat.cast_mul, Nat.cast_sum, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      congrArg (fun n : ℕ ↦ (n : ℝ)) hmN
  have hsumW : (∑ j ∈ range (p+1), w j) = (3/2)*m := by
    have hwEq (j : ℕ) : w j = 3-h*(j : ℝ) := by dsimp only [w, α]; ring
    simp only [hwEq, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    change m*3-h*(∑ j ∈ range (p+1), (j : ℝ)) = _
    linear_combination -(m/2)*hpH-(h/2)*hsumJ
  have hM₀ : 0 ≤ M := sum_nonneg fun j _ ↦ mul_nonneg (sq_nonneg _) (he j).1
  have hN₀ : 0 ≤ N := sum_nonneg fun j hj ↦
    mul_nonneg (add_nonneg (mul_nonneg (by norm_num) (hw j hj).1) hh.le) (he j).1
  have hM : h*M ≤ (9/2)*α := by
    have hs : M ≤ (9/2)*m := calc
      M ≤ ∑ j ∈ range (p+1), 3*w j := by
        apply sum_le_sum
        intro j hj
        exact (mul_le_of_le_one_right (sq_nonneg _) (he j).2).trans (by
          have hmul := mul_le_mul_of_nonneg_right (hw j hj).2 (hw j hj).1
          nlinarith only [hmul])
      _ = _ := by rw [← mul_sum, hsumW]; ring
    have hle := mul_le_mul_of_nonneg_left hs hh.le
    nlinarith only [hle, hm]
  have hN : h*N ≤ α^2 := by
    have hs : N ≤ α*m := calc
      N ≤ ∑ j ∈ range (p+1), (2*w j+h) := by
        exact sum_le_sum fun j hj ↦ mul_le_of_le_one_right
          (add_nonneg (mul_nonneg (by norm_num) (hw j hj).1) hh.le) (he j).2
      _ = _ := by
        rw [sum_add_distrib, ← mul_sum, hsumW, sum_const, card_range, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_one]
        change 2*((3/2)*m)+m*h = _
        dsimp only [α]
        ring
    have hle := mul_le_mul_of_nonneg_left hs hh.le
    nlinarith only [hle, mul_le_mul_of_nonneg_left hm.le (by positivity : 0 ≤ α)]
  have hs : 0 < s := by linarith
  have hF : 0 < F := div_pos
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hh hs)))) hh
  have hq₀ : 0 ≤ q := (Real.exp_pos _).le
  have hq₁ : q ≤ 1 := Real.exp_le_one_iff.mpr (by
    exact neg_nonpos.mpr (mul_nonneg hh.le hs.le))
  have hqle : q ≤ F/6 := by
    have hlog := upperTailGap_logDeriv hh hs
    rw [(hasDerivAt_upperTailGap hh).deriv] at hlog
    have hSlope := (upperTailSlope_bounds hh hs).2.1.trans
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) hgap)
    rw [show q = upperTailSlope h s*F from (div_eq_iff hF.ne').mp hlog]
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      mul_le_mul_of_nonneg_right hSlope hF.le
  have hFmin : 2 ≤ F := by
    have hgapEq : h*F = 1-q := gap_relation hh s
    have ht := mul_le_mul_of_nonneg_right hhmax hF.le
    linarith only [hgapEq, ht, hqle, hF.le]
  have hα₀ : 0 ≤ α := by dsimp only [α]; linarith
  have hα : α ≤ 10/3 := by dsimp only [α]; linarith
  have hβ₀ : 0 ≤ β := by dsimp only [β]; linarith
  have hβ : β ≤ 18/5 := by dsimp only [β, α]; linarith
  have hX : 0 ≤ α*F := mul_nonneg hα₀ hF.le
  have hXlo := mul_le_mul_of_nonneg_left hFmin hα₀
  have hαsq := mul_le_mul_of_nonneg_right hα hα₀
  have hαcube := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hα₀ hα 2) hα₀
  have hA : α^2+h*F*M ≤ (13/2)*(α*F) := by
    have hFM := mul_le_mul_of_nonneg_left hM hF.le
    nlinarith only [hXlo, hαsq, hFM, hX]
  have hB : h*q*N ≤ (13/2)*(α*F) := by
    have hqN := mul_le_of_le_one_right (mul_nonneg hh.le hN₀) hq₁
    nlinarith only [hXlo, hαsq, hN, hqN, hX]
  have hC : α^3+h*α*F*M ≤ 22*(α*F) := by
    have hαM := mul_le_mul hα hM (mul_nonneg hh.le hM₀) (by norm_num : (0 : ℝ) ≤ 10/3)
    have hFαM := mul_le_mul_of_nonneg_left hαM hF.le
    nlinarith only [hαcube, hXlo, hFαM, hX]
  have hD : h*q*(M+β*N) ≤ 22*(α*F) := by
    have hαβ := mul_le_mul hβ hα hα₀ (by norm_num : (0 : ℝ) ≤ 18/5)
    have hαβ₂ := mul_le_mul_of_nonneg_right hαβ hα₀
    have hβN := mul_le_mul_of_nonneg_left hN hβ₀
    have hsum := mul_le_of_le_one_right (mul_nonneg hh.le
      (add_nonneg hM₀ (mul_nonneg hβ₀ hN₀))) hq₁
    nlinarith only [hαβ₂, hβN, hM, hsum, hXlo, hX]
  obtain ⟨h₂, h₃⟩ := leftStripCross_derivatives hp₀ a v
  change deriv (deriv (leftStripCross p · v)) a = E*(α^2+h*F*M-h*q*N) at h₂
  change deriv (fun y ↦ deriv (deriv (leftStripCross p · y)) a) v =
    E*(-α^3-h*α*F*M+h*q*(M+β*N)) at h₃
  have he₀ : 0 ≤ E := (Real.exp_pos _).le
  have h₂' : |α^2+h*F*M-h*q*N| ≤ (13/2)*(α*F) := by
    exact abs_le.mpr ⟨by linarith only [hB, show 0 ≤ α^2+h*F*M by positivity],
      by linarith only [hA, show 0 ≤ h*q*N by positivity]⟩
  have h₃' : |-α^3-h*α*F*M+h*q*(M+β*N)| ≤ 22*(α*F) := by
    exact abs_le.mpr ⟨by linarith only [hC, show 0 ≤ h*q*(M+β*N) by positivity],
      by linarith only [hD, show 0 ≤ α^3+h*α*F*M by positivity]⟩
  rw [h₂, h₃, abs_mul, abs_mul, abs_of_nonneg he₀]
  change E*|α^2+h*F*M-h*q*N| ≤ (13/2)*((1+α*F)*E) ∧
    E*|-α^3-h*α*F*M+h*q*(M+β*N)| ≤ 22*((1+α*F)*E)
  exact ⟨by nlinarith only [mul_le_mul_of_nonneg_left h₂' he₀, he₀],
    by nlinarith only [mul_le_mul_of_nonneg_left h₃' he₀, he₀]⟩

theorem leftStripCross_smooth (p : ℕ) :
    ContDiff ℝ 3 (Function.uncurry (leftStripCross p)) := by
  let h := 3/(p : ℝ)
  have hsum : ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ tailSum p h z.1) := by
    unfold tailSum
    apply ContDiff.sum
    intro j _
    fun_prop
  change ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ Real.exp (-((3+h)*(z.2-z.1))) *
    (1+h*upperTailGap h (z.2-z.1)*tailSum p h z.1))
  unfold upperTailGap
  fun_prop

theorem leftStripTailResidual_smooth (p : ℕ) :
    ContDiff ℝ 3 (Function.uncurry (leftStripTailResidual p)) := by
  let h := 3/(p : ℝ)
  have hc := leftStripCross_smooth p
  change ContDiff ℝ 3 (fun z : ℝ × ℝ ↦ leftStripCross p z.1 z.2) at hc
  change ContDiff ℝ 3 (fun z : ℝ × ℝ ↦
    (upperTailRepeatCorrection h z.2+upperTailRepeatCorrection h (z.2-z.1))/2 -
      leftStripCross p z.1 z.2)
  unfold upperTailRepeatCorrection upperTailGap
  fun_prop

private theorem contDiff_partialLeft {f : ℝ → ℝ → ℝ} {n m : WithTop ℕ∞}
    (hf : ContDiff ℝ n (Function.uncurry f)) (hn : n ≠ 0) (hm : m+1 ≤ n) :
    ContDiff ℝ m (Function.uncurry (fun x y ↦ deriv (f · y) x)) := by
  have hd := (hf.fderiv_right hm).clm_apply
    (contDiff_const : ContDiff ℝ m (fun _ : ℝ × ℝ ↦ ((1,0) : ℝ × ℝ)))
  convert hd using 1
  funext z
  rcases z with ⟨x,y⟩
  have hLine : HasDerivAt (fun t : ℝ ↦ (t,y)) (1,0) x := by
    simpa only [id_eq] using (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  exact ((hf.differentiable hn (x,y)).hasFDerivAt.comp_hasDerivAt x hLine).deriv

/-- Second and mixed third derivative bounds for the cancelled tail.
Both are measured against the correction at the smaller separated gap. -/
theorem leftStripTailResidual_derivative_bounds {p : ℕ} (hp : 11 ≤ p) {a v : ℝ}
    (ha : 0 ≤ a) (hgap : 6 ≤ v-a) :
    let h := 3/(p : ℝ)
    let U := upperTailRepeatCorrection h (v-a)
    let A := leftStripTailResidual p
    |deriv (deriv (A · v)) a| ≤ 12*U ∧
      |deriv (fun y ↦ deriv (deriv (A · y)) a) v| ≤ 40*U := by
  let h := 3/(p : ℝ)
  let U := upperTailRepeatCorrection h
  let C := leftStripCross p
  let A := leftStripTailResidual p
  let s := v-a
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp [h]; positivity
  have hhmax : h ≤ 3/11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hU : ContDiff ℝ 3 U := by unfold U upperTailRepeatCorrection upperTailGap; fun_prop
  have hU₁ : ContDiff ℝ 2 (deriv U) := hU.deriv'
  have hU₂ : ContDiff ℝ 1 (deriv (deriv U)) := hU₁.deriv'
  have hCleft (y : ℝ) : ContDiff ℝ 3 (C · y) := by
    have hd := leftStripCross_smooth p
    have h := hd.comp (contDiff_id.prodMk contDiff_const :
      ContDiff ℝ 3 (fun x : ℝ ↦ (x,y)))
    exact h
  have hfirst (y : ℝ) : deriv (A · y) = fun x ↦ -(deriv U (y-x))/2-deriv (C · y) x := by
    funext x
    have hShift := (hasDerivAt_id' x).const_sub y
    have hd := (((hU.differentiable (by decide) (y-x)).hasDerivAt.comp x hShift).const_add
      (U y)).div_const 2
    have ht := hd.sub ((hCleft y).differentiable (by decide) x).hasDerivAt
    change HasDerivAt (A · y) _ x at ht
    simpa only [mul_neg, mul_one, zero_add] using ht.deriv
  have hsecond (x y : ℝ) : deriv (deriv (A · y)) x =
      deriv (deriv U) (y-x)/2-deriv (deriv (C · y)) x := by
    rw [hfirst y]
    have hShift := (hasDerivAt_id' x).const_sub y
    have hd := (((hU₁.differentiable (by decide) (y-x)).hasDerivAt.comp x hShift).neg).div_const 2
    have hCc : ContDiff ℝ 2 (deriv (C · y)) := (hCleft y).deriv'
    have ht := hd.sub (hCc.differentiable (by decide) x).hasDerivAt
    change HasDerivAt (fun t ↦ -(deriv U (y-t))/2-deriv (C · y) t) _ x at ht
    simpa only [mul_neg, mul_one, neg_neg] using ht.deriv
  have hCaa :
      DifferentiableAt ℝ (fun y ↦ deriv (deriv (C · y)) a) v := by
    have hSmooth := leftStripCross_smooth p
    have h₁ := contDiff_partialLeft hSmooth (by decide) (show (2 : WithTop ℕ∞)+1 ≤ 3 by decide)
    have h₂ := contDiff_partialLeft h₁ (by decide) (show (1 : WithTop ℕ∞)+1 ≤ 2 by decide)
    exact ((h₂.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ 1 (fun y : ℝ ↦ (a,y)))).differentiable (by decide) v)
  have hthird : deriv (fun y ↦ deriv (deriv (A · y)) a) v =
      deriv (deriv (deriv U)) s/2-deriv (fun y ↦ deriv (deriv (C · y)) a) v := by
    rw [show (fun y ↦ deriv (deriv (A · y)) a) =
      (fun y ↦ deriv (deriv U) (y-a)/2-deriv (deriv (C · y)) a) from funext (hsecond a)]
    have hd := ((hU₂.differentiable (by decide) s).hasDerivAt.comp v
      ((hasDerivAt_id' v).sub_const a)).div_const 2
    have ht := hd.sub hCaa.hasDerivAt
    change HasDerivAt (fun y ↦ deriv (deriv U) (y-a)/2-deriv (deriv (C · y)) a) _ v at ht
    simpa only [mul_one] using ht.deriv
  obtain ⟨_, _, h₂₀, h₂, h₃₀, h₃⟩ := separated_correction_derivative_bounds hh hgap
  change 0 ≤ deriv (deriv U) s at h₂₀
  change deriv (deriv U) s ≤ (3+h)^2*U s at h₂
  change 0 ≤ -deriv (deriv (deriv U)) s at h₃₀
  change -deriv (deriv (deriv U)) s ≤ (3+h)^3*U s at h₃
  have hF : 0 ≤ upperTailGap h s := by
    unfold upperTailGap
    exact div_nonneg
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hh.le (by linarith))))) hh.le
  have hU₀ : 0 ≤ U s := by unfold U upperTailRepeatCorrection; positivity
  have hα : 3+h ≤ 36/11 := by linarith
  have hα₀ : 0 ≤ 3+h := by linarith
  have hU2 : |deriv (deriv U) s| ≤ 11*U s := by
    rw [abs_of_nonneg h₂₀]
    refine h₂.trans (mul_le_mul_of_nonneg_right ?_ hU₀)
    exact (pow_le_pow_left₀ hα₀ hα 2).trans (by norm_num)
  have hU3 : |deriv (deriv (deriv U)) s| ≤ 36*U s := by
    rw [← abs_neg, abs_of_nonneg h₃₀]
    refine h₃.trans (mul_le_mul_of_nonneg_right ?_ hU₀)
    exact (pow_le_pow_left₀ hα₀ hα 3).trans (by norm_num)
  obtain ⟨hC2, hC3⟩ := leftStripCross_derivative_bounds hp ha hgap
  change |deriv (deriv (C · v)) a| ≤ (13/2)*U s at hC2
  change |deriv (fun y ↦ deriv (deriv (C · y)) a) v| ≤ 22*U s at hC3
  change |deriv (deriv (A · v)) a| ≤ 12*U s ∧
    |deriv (fun y ↦ deriv (deriv (A · y)) a) v| ≤ 40*U s
  constructor
  · rw [hsecond a v]
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hU2, hC2]
  · rw [hthird]
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hU3, hC3]

private theorem mixed_partial_eq {f : ℝ → ℝ → ℝ} {x y : ℝ}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (x,y)) :
    deriv (fun t ↦ deriv (f t) y) x = deriv (fun t ↦ deriv (f · t) x) y := by
  have h := Extreme.hasDerivAt_deriv_second hf
  exact h.deriv.trans (Extreme.hasDerivAt_deriv_first_of_second hf h).deriv.symm

private theorem bounds_of_cancelled_second_derivative {f : ℝ → ℝ} {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (h₀ : f 0 = 0) (h₁ : deriv f 0 = 0)
    (h₂ : ∀ x ∈ Icc (0 : ℝ) a, |deriv (deriv f) x| ≤ C) :
    |f a| ≤ C*a^2 ∧ |deriv f a| ≤ C*a := by
  have hderiv (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : |deriv f x| ≤ C*x := by
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f)
      (fun t _ ↦ hf' t) (fun t ht ↦ by simpa only [Real.norm_eq_abs] using h₂ t ht)
      (convex_Icc 0 a) (left_mem_Icc.mpr ha) hx
    simpa only [Real.norm_eq_abs, h₁, sub_zero, abs_of_nonneg hx.1] using hm
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le (f := f)
    (fun t _ ↦ hf t)
    (fun t ht ↦ by
      rw [Real.norm_eq_abs]
      exact (hderiv t ht).trans (mul_le_mul_of_nonneg_left ht.2 hC))
    (convex_Icc 0 a) (left_mem_Icc.mpr ha) (right_mem_Icc.mpr ha)
  refine ⟨?_, hderiv a (right_mem_Icc.mpr ha)⟩
  simpa only [Real.norm_eq_abs, h₀, sub_zero, abs_of_nonneg ha, pow_two, mul_assoc] using hm

/-- The zero value and slope give a quadratic bound on both the tail
residual and its upper-coordinate derivative. -/
theorem leftStripTailResidual_cancellation_bounds {p : ℕ} (hp : 11 ≤ p) {a v : ℝ}
    (ha : 0 ≤ a) (hgap : 6 ≤ v-a) :
    let h := 3/(p : ℝ)
    let U := upperTailRepeatCorrection h (v-a)
    let A := leftStripTailResidual p
    |A a v| ≤ 12*U*a^2 ∧ |deriv (A · v) a| ≤ 12*U*a ∧
      |deriv (A a) v| ≤ 40*U*a^2 ∧ |deriv (fun x ↦ deriv (A x) v) a| ≤ 40*U*a := by
  let h := 3/(p : ℝ)
  let U := upperTailRepeatCorrection h
  let A := leftStripTailResidual p
  let P (x y : ℝ) := deriv (A · y) x
  let R (x y : ℝ) := deriv (A x) y
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp [h]; positivity
  have hA : ContDiff ℝ 3 (Function.uncurry A) := leftStripTailResidual_smooth p
  have hA₂ : ContDiff ℝ 2 (Function.uncurry A) := hA.of_le (by decide)
  have hP : ContDiff ℝ 2 (Function.uncurry P) :=
    contDiff_partialLeft hA (by decide) (by norm_num)
  have hLeft {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 2 (Function.uncurry f)) :
      Differentiable ℝ (f · v) :=
    (hf.comp (contDiff_id.prodMk contDiff_const :
      ContDiff ℝ 2 (fun x : ℝ ↦ (x,v)))).differentiable (by decide)
  have hR (x : ℝ) : DifferentiableAt ℝ (R · v) x :=
    (Extreme.hasDerivAt_deriv_second (hA₂.contDiffAt (x := (x,v)))).differentiableAt
  have hRfirst : deriv (R · v) = fun x ↦ deriv (P x) v :=
    funext fun x ↦ mixed_partial_eq (hA₂.contDiffAt (x := (x,v)))
  have hRsecond (x : ℝ) :
      deriv (deriv (R · v)) x = deriv (fun y ↦ deriv (deriv (A · y)) x) v := by
    rw [hRfirst]
    exact mixed_partial_eq (hP.contDiffAt (x := (x,v)))
  have hRdiff : Differentiable ℝ (deriv (R · v)) := by
    rw [hRfirst]
    intro x
    exact (Extreme.hasDerivAt_deriv_second (hP.contDiffAt (x := (x,v)))).differentiableAt
  have hA₀ (y : ℝ) : A 0 y = 0 := (leftStripTailResidual_zero hp₀ y).1
  have hP₀ (y : ℝ) : P 0 y = 0 := (leftStripTailResidual_zero hp₀ y).2.deriv
  have hR₀ : R 0 v = 0 := by
    change deriv (A 0) v = 0
    rw [show A 0 = fun _ ↦ 0 from funext hA₀, deriv_const]
  have hR₁ : deriv (R · v) 0 = 0 := by
    rw [hRfirst]
    change deriv (P 0) v = 0
    rw [show P 0 = fun _ ↦ 0 from funext hP₀, deriv_const]
  have hUd : Differentiable ℝ U :=
    fun t ↦ (hasDerivAt_repeat (t := t) hh).differentiableAt
  have hUm : AntitoneOn U (Ici 6) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) hUd.continuous.continuousOn hUd.differentiableOn
    intro t ht
    exact neg_nonneg.mp (separated_correction_derivative_bounds hh
      (interior_subset ht : t ∈ Ici (6 : ℝ))).1
  have hF : 0 ≤ upperTailGap h (v-a) := by
    unfold upperTailGap
    exact div_nonneg
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hh.le (by linarith))))) hh.le
  have hU₀ : 0 ≤ U (v-a) := by unfold U upperTailRepeatCorrection; positivity
  have hBounds (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) :
      |deriv (deriv (A · v)) x| ≤ 12*U (v-a) ∧
        |deriv (deriv (R · v)) x| ≤ 40*U (v-a) := by
    have hs : v-a ≤ v-x := sub_le_sub_left hx.2 _
    have hxs := hgap.trans hs
    have hmono : U (v-x) ≤ U (v-a) := hUm hgap hxs hs
    obtain ⟨h₂,h₃⟩ := leftStripTailResidual_derivative_bounds hp hx.1 hxs
    rw [hRsecond x]
    exact ⟨h₂.trans (mul_le_mul_of_nonneg_left hmono (by norm_num)),
      h₃.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))⟩
  obtain ⟨hA₁,hA₂⟩ := bounds_of_cancelled_second_derivative ha
    (by positivity : 0 ≤ 12*U (v-a)) (hLeft hA₂) (hLeft hP) (hA₀ v) (hP₀ v)
    (fun x hx ↦ (hBounds x hx).1)
  obtain ⟨hRv,hRv₁⟩ := bounds_of_cancelled_second_derivative ha
    (by positivity : 0 ≤ 40*U (v-a)) hR hRdiff hR₀ hR₁ (fun x hx ↦ (hBounds x hx).2)
  exact ⟨hA₁,hA₂,hRv,hRv₁⟩

#print axioms leftStripCross_eq
#print axioms leftStripTailResidual_zero
#print axioms leftStripCross_derivatives
#print axioms leftStripCross_derivative_bounds
#print axioms leftStripTailResidual_derivative_bounds
#print axioms leftStripTailResidual_cancellation_bounds

end RefinedBMV.PositiveCenter
