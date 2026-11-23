/- GID: D5/S3/Quantum/Semigroups/WuCriticalQuartic
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCriticalQuartic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict exponent decrease of the positive-temperature Wu quartic kernel. -/

import D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Positivity

/-! The reduced positive-temperature quartic in the population and coherence coordinates. -/

noncomputable section

open Matrix Set
open D5.S3.Observer.Fluctuation.ThermalCoefficientFloor (coth inv_le_coth)
open D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic (sinh_cosh_sub_pos)

namespace D5.S3.Quantum.Semigroups.WuCriticalQuartic

set_option autoImplicit false

private def cschSq (x : ℝ) : ℝ := 1 / Real.sinh x ^ 2
private def scale (x y : ℝ) : ℝ := y / x * (Real.sinh x ^ 2 / Real.sinh y ^ 2)
private def rate (x y : ℝ) : ℝ := 2 * (coth x + coth y) - 1 / x - 1 / y
private def xAt (β q : ℝ) : ℝ := β / 2 / q
private def yAt (β q : ℝ) : ℝ := β / 2 - xAt β q

/-- The coefficient of the squared population coordinate. -/
def a (β q : ℝ) : ℝ := scale (xAt β q) (yAt β q) / 2

/-- The mixed coefficient of the normalized quadratic form. -/
def e (β q : ℝ) : ℝ := coth (yAt β q) - scale (xAt β q) (yAt β q) * (coth (xAt β q) - 1)

/-- The coefficient of the squared coherence coordinate. -/
def d (β q : ℝ) : ℝ :=
  -1 + (1 - coth (xAt β q) / 2) * coth (yAt β q) +
    scale (xAt β q) (yAt β q) / 2 * (coth (xAt β q) - 1) ^ 2

/-- The normalized Gibbs-quartic matrix at inverse temperature β and real exponent q. -/
def K (β q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a β q, e β q / 2; e β q / 2, d β q]

/-- Evaluate the quadratic form of the normalized matrix. -/
def value (β q : ℝ) (v : Fin 2 → ℝ) : ℝ := v ⬝ᵥ (K β q *ᵥ v)

private theorem value_eq (β q : ℝ) (v : Fin 2 → ℝ) :
    value β q v = a β q * v 0 ^ 2 + e β q * v 0 * v 1 + d β q * v 1 ^ 2 := by
  simp [value, K, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

private theorem x_pos {β q : ℝ} (hβ : 0 < β) (hq : 1 < q) : 0 < xAt β q := by
  unfold xAt
  exact div_pos (by positivity) (by linarith)

private theorem y_pos {β q : ℝ} (hβ : 0 < β) (hq : 1 < q) : 0 < yAt β q := by
  unfold yAt xAt
  apply sub_pos.mpr
  exact (div_lt_iff₀ (by linarith : 0 < q)).mpr
    (lt_mul_of_one_lt_right (by positivity) hq)

private theorem sinh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x :=
  Real.sinh_pos_iff.mpr hx

private theorem cschSq_pos {x : ℝ} (hx : 0 < x) : 0 < cschSq x := by
  exact one_div_pos.mpr (sq_pos_of_pos (sinh_pos hx))

private theorem coth_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt coth (-cschSq x) x := by
  have h := (Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) (sinh_pos hx).ne'
  convert h using 1
  · rfl
  · change -(1 / Real.sinh x ^ 2) =
        (Real.sinh x * Real.sinh x - Real.cosh x * Real.cosh x) / Real.sinh x ^ 2
    rw [← neg_div]
    congr 1
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

private theorem scale_hasDerivAt {T x : ℝ} (hx : 0 < x) (hy : 0 < T - x) :
    HasDerivAt (fun s => scale s (T - s)) (scale x (T - x) * rate x (T - x)) x := by
  have hy' := (hasDerivAt_const x T).sub (hasDerivAt_id x)
  have h := (hy'.div (hasDerivAt_id x) hx.ne').mul
    (((Real.hasDerivAt_sinh x).pow 2).div
      (hy'.sinh.pow 2) (pow_ne_zero 2 (sinh_pos hy).ne'))
  convert h using 1
  · rfl
  · unfold scale
    simp only [rate, coth, Pi.div_apply, Pi.sub_apply, Pi.pow_apply, zero_sub, id_eq,
      Nat.cast_ofNat]
    field_simp [hx.ne', hy.ne', (sinh_pos hx).ne', (sinh_pos hy).ne']
    ring

private def leading (x y : ℝ) : ℝ := scale x y * rate x y
private def mixed (x y : ℝ) : ℝ := cschSq y + cschSq x * scale x y
private def trailing (x y : ℝ) : ℝ := cschSq x * coth y + coth x * cschSq y

private def determinantFactor (x y : ℝ) : ℝ :=
  (2 * x * y * (coth x + coth y) - (x + y)) *
    (Real.sinh x * Real.cosh x + Real.sinh y * Real.cosh y) - (x + y) ^ 2

private theorem leading_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < leading x y := by
  have hsum := add_le_add (inv_le_coth hx) (inv_le_coth hy)
  have hi : 0 < 1 / x + 1 / y := by positivity
  have hrate : 0 < rate x y := by
    unfold rate
    rw [one_div, one_div] at hi ⊢
    linarith
  have hscale : 0 < scale x y :=
    mul_pos (div_pos hy hx) (div_pos (sq_pos_of_pos (sinh_pos hx)) (sq_pos_of_pos (sinh_pos hy)))
  exact mul_pos hscale hrate

private theorem determinantFactor_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < determinantFactor x y := by
  have hs := add_le_add (inv_le_coth hx) (inv_le_coth hy)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * x * y by positivity)
  have hid : 2 * x * y * (1 / x + 1 / y) = 2 * (x + y) := by
    field_simp [hx.ne', hy.ne']
    ring
  rw [← one_div, ← one_div, hid] at hm
  have hfirst : x + y ≤ 2 * x * y * (coth x + coth y) - (x + y) := by linarith
  have hsecond : x + y < Real.sinh x * Real.cosh x + Real.sinh y * Real.cosh y := by
    linarith [sinh_cosh_sub_pos hx, sinh_cosh_sub_pos hy]
  unfold determinantFactor
  exact sub_pos.mpr (by
    rw [pow_two]
    exact (mul_lt_mul_of_pos_left hsecond (add_pos hx hy)).trans_le
      (mul_le_mul_of_nonneg_right hfirst (le_of_lt ((add_pos hx hy).trans hsecond))))

private theorem determinant_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    leading x y * trailing x y - mixed x y ^ 2 =
      (cschSq y ^ 2 / x ^ 2) * determinantFactor x y := by
  unfold leading trailing mixed determinantFactor scale rate cschSq coth
  field_simp [hx.ne', hy.ne', (sinh_pos hx).ne', (sinh_pos hy).ne']
  ring

private theorem positiveForm {A B C s t : ℝ} (hA : 0 < A) (hdet : 0 < A * C - B ^ 2)
    (hne : s ≠ 0 ∨ t ≠ 0) : 0 < A * s ^ 2 + 2 * B * s * t + C * t ^ 2 := by
  have hid : A * s ^ 2 + 2 * B * s * t + C * t ^ 2 =
      A * (s + B / A * t) ^ 2 + ((A * C - B ^ 2) / A) * t ^ 2 := by
    field_simp [hA.ne']
    ring
  by_cases ht : t = 0
  · subst t
    simpa using mul_pos hA (sq_pos_of_ne_zero (hne.resolve_right (not_not_intro rfl)))
  · rw [hid]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hA.le (sq_nonneg _))
      (mul_pos (div_pos hdet hA) (sq_pos_of_ne_zero ht))

private theorem value_hasDerivAt {β q : ℝ} (hβ : 0 < β) (hq : 1 < q) (v : Fin 2 → ℝ) :
    HasDerivAt (fun z => value β z v)
      (-(xAt β q / (2 * q)) *
        (leading (xAt β q) (yAt β q) * (v 0 - (coth (xAt β q) - 1) * v 1) ^ 2 +
          2 * mixed (xAt β q) (yAt β q) * (v 0 - (coth (xAt β q) - 1) * v 1) * v 1 +
          trailing (xAt β q) (yAt β q) * v 1 ^ 2)) q := by
  let T := β / 2
  let x := xAt β q
  let y := T - x
  have hx : 0 < x := x_pos hβ hq
  have hy : 0 < y := y_pos hβ hq
  have hq₀ : q ≠ 0 := by linarith
  have hxq : HasDerivAt (xAt β) (-(x / q)) q := by
    have h := (hasDerivAt_const q T).div (hasDerivAt_id q) hq₀
    convert h using 1
    · rfl
    · simp only [x, xAt, zero_mul, mul_one, zero_sub, id_eq]
      field_simp [hq₀]
      dsimp [T]
      ring
  have hA := scale_hasDerivAt hx hy
  have hR := coth_hasDerivAt hx
  have hS : HasDerivAt (fun s => coth (T - s)) (cschSq y) x := by
    have h := (coth_hasDerivAt hy).comp x ((hasDerivAt_const x T).sub (hasDerivAt_id x))
    convert h using 1
    · rfl
    · simp
  have hw := hR.sub_const 1
  have hd := ((((hR.div_const 2).const_sub 1).mul hS).const_add (-1)).add
    ((hA.div_const 2).mul (hw.pow 2))
  have hQ := (((hA.div_const 2).mul_const (v 0 ^ 2)).add
    ((hS.sub (hA.mul hw)).mul_const (v 0 * v 1))).add (hd.mul_const (v 1 ^ 2))
  have hf := hQ.comp q hxq
  convert hf using 1
  · ext z
    rw [value_eq]
    simp only [Function.comp_def, a, e, d, yAt, T, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.pow_apply]
    ring
  · change -(x / (2 * q)) * _ = _
    simp only [leading, mixed, trailing, yAt, ← show T - x = y from rfl,
      Pi.pow_apply, Nat.cast_ofNat, neg_mul, mul_neg]
    ring

/-- The exponent derivative is strictly negative on every nonzero real direction. -/
theorem deriv_value_neg {β q : ℝ} (hβ : 0 < β) (hq : 1 < q)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    deriv (fun t => value β t v) q < 0 := by
  have hx := x_pos hβ hq
  have hy := y_pos hβ hq
  have hdet : 0 < leading (xAt β q) (yAt β q) * trailing (xAt β q) (yAt β q) -
      mixed (xAt β q) (yAt β q) ^ 2 := by
    rw [determinant_eq hx hy]
    exact mul_pos (div_pos (sq_pos_of_pos (cschSq_pos hy)) (sq_pos_of_pos hx))
      (determinantFactor_pos hx hy)
  have hv' : v 0 - (coth (xAt β q) - 1) * v 1 ≠ 0 ∨ v 1 ≠ 0 := by
    by_cases h : v 1 = 0
    · left
      simp only [h, mul_zero, sub_zero]
      intro h₀
      apply hv
      funext i
      exact Fin.cases h₀ (fun j => by rw [Subsingleton.elim j 0]; exact h) i
    · exact Or.inr h
  rw [(value_hasDerivAt hβ hq v).deriv]
  have hq' : 0 < q := by linarith
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity))
    (positiveForm (leading_pos hx hy) hdet hv')

/-- For two ordered exponents, the matrix difference is positive on every nonzero vector. -/
theorem endpoint_drop_pos {β p r : ℝ} (hβ : 0 < β) (hp : 1 < p) (hpr : p < r)
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    0 < value β p v - value β r v := by
  apply sub_pos.mpr
  have hanti : StrictAntiOn (fun q => value β q v) (Ioi 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi (1 : ℝ))
    · exact fun q hq => (value_hasDerivAt hβ hq v).continuousAt.continuousWithinAt
    · intro q hq
      rw [interior_Ioi] at hq
      exact deriv_value_neg hβ hq v hv
  exact hanti hp (hp.trans hpr) hpr

/-- The leading minor and the Schur complement of the endpoint difference are strictly positive. -/
theorem endpoint_schur_pos {β p r : ℝ} (hβ : 0 < β) (hp : 1 < p) (hpr : p < r) :
    0 < a β p - a β r ∧
    0 < d β p - d β r - (e β p - e β r) ^ 2 / (4 * (a β p - a β r)) := by
  have hnonzero (s : ℝ) : (![s, 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 1
    norm_num at this
  have ha := endpoint_drop_pos hβ hp hpr ![1, 0] (by
    intro h
    have := congrFun h 0
    norm_num at this)
  simp only [value_eq, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, zero_pow
    (by decide : (2 : ℕ) ≠ 0), mul_zero, mul_one, add_zero] at ha
  refine ⟨ha, ?_⟩
  let s := -(e β p - e β r) / (2 * (a β p - a β r))
  have h := endpoint_drop_pos hβ hp hpr ![s, 1] (hnonzero s)
  simp only [value_eq, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one] at h
  convert h using 1
  dsimp [s]
  field_simp [ha.ne']
  ring

/-- The squared population coefficient in the exponential Gibbs coordinates. -/
def exponentA (β q : ℝ) : ℝ :=
  let z := Real.exp (-β)
  let k := z ^ (1 / q)
  let g := 1 - z / k
  let h := 1 - k
  (q - 1) * (z / k ^ 2) * h ^ 2 / (2 * g ^ 2)

/-- The mixed coefficient in the exponential Gibbs coordinates. -/
def exponentE (β q : ℝ) : ℝ :=
  let z := Real.exp (-β)
  let k := z ^ (1 / q)
  let u := z / k
  let g := 1 - u
  let h := 1 - k
  2 / g - 1 - 2 * (q - 1) * u * h / g ^ 2

/-- The squared coherence coefficient in the exponential Gibbs coordinates. -/
def exponentD (β q : ℝ) : ℝ :=
  let z := Real.exp (-β)
  let k := z ^ (1 / q)
  let g := 1 - z / k
  let h := 1 - k
  2 / g - 3 / 2 - (1 + z) / (g * h) + 2 * (q - 1) * z / g ^ 2

/-- The normalized reduced-quartic matrix in the exponential Gibbs coordinates. -/
def exponentK (β q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![exponentA β q, exponentE β q / 2; exponentE β q / 2, exponentD β q]

private theorem hyperbolic_exp {t : ℝ} (ht : 0 < t) :
    let w := Real.exp (-t)
    let k := Real.exp (-2 * t)
    Real.sinh t = (1 - k) / (2 * w) ∧ coth t = (1 + k) / (1 - k) := by
  dsimp only
  have hw := (Real.exp_pos (-t)).ne'
  have hk : 0 < 1 - Real.exp (-2 * t) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hid : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
    rw [show -2 * t = (2 : ℕ) * (-t) by norm_num, Real.exp_nat_mul]
  have hs : Real.sinh t = (1 - Real.exp (-2 * t)) / (2 * Real.exp (-t)) := by
    rw [Real.sinh_eq, hid, show Real.exp t = (Real.exp (-t))⁻¹ by rw [← Real.exp_neg, neg_neg]]
    field_simp [hw]
  have hc : Real.cosh t = (1 + Real.exp (-2 * t)) / (2 * Real.exp (-t)) := by
    rw [Real.cosh_eq, hid, show Real.exp t = (Real.exp (-t))⁻¹ by rw [← Real.exp_neg, neg_neg]]
    field_simp [hw]
  exact ⟨hs, by rw [coth, hs, hc]; field_simp [hk.ne', hw]⟩

/-- The normalized hyperbolic coefficients agree with the exponential Gibbs coefficients. -/
private theorem K_eq_exponentK {β q : ℝ} (hβ : 0 < β) (hq : 1 < q) :
    K β q = exponentK β q := by
  let x := xAt β q
  let y := yAt β q
  let z := Real.exp (-β)
  let k := Real.exp (-2 * x)
  let u := Real.exp (-2 * y)
  have hx := x_pos hβ hq
  have hy := y_pos hβ hq
  have hq₀ : q ≠ 0 := by linarith
  have hk : 0 < 1 - k := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hu : 0 < 1 - u := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hk₀ : k ≠ 0 := (Real.exp_pos _).ne'
  have hxy : x + y = β / 2 := by dsimp [x, y, yAt]; ring
  have hz : z = k * u := by
    dsimp only [z, k, u]
    rw [← Real.exp_add]
    congr 1
    linarith
  have hk_def : z ^ (1 / q) = k := by
    rw [Real.rpow_def_of_pos (Real.exp_pos (-β)), Real.log_exp]
    unfold k x xAt
    congr 1
    ring
  have hu_def : z / k = u := by rw [hz, mul_comm k u, mul_div_cancel_right₀ _ hk₀]
  have hq_def : y / x = q - 1 := by
    have hxq : x * q = β / 2 := by dsimp [x, xAt]; field_simp [hq₀]
    apply (div_eq_iff hx.ne').mpr
    linarith
  obtain ⟨hsx, hcx⟩ := hyperbolic_exp hx
  obtain ⟨hsy, hcy⟩ := hyperbolic_exp hy
  have hA : scale x y = (q - 1) * (u / k) * (1 - k) ^ 2 / (1 - u) ^ 2 := by
    change Real.sinh x = (1 - k) / (2 * Real.exp (-x)) at hsx
    change Real.sinh y = (1 - u) / (2 * Real.exp (-y)) at hsy
    have hxexp : Real.exp (-x) ^ 2 = k := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    have hyexp : Real.exp (-y) ^ 2 = u := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    unfold scale
    rw [hq_def, hsx, hsy, div_pow, div_pow, mul_pow, mul_pow, hxexp, hyexp]
    field_simp [hk₀, hu.ne', (Real.exp_pos (-2 * y)).ne']
  change coth x = (1 + k) / (1 - k) at hcx
  change coth y = (1 + u) / (1 - u) at hcy
  dsimp only [K, exponentK, exponentA, exponentE, exponentD]
  rw [show Real.exp (-β) = z from rfl, hk_def, hu_def, hz]
  have ha : a β q = (q - 1) * (k * u / k ^ 2) * (1 - k) ^ 2 / (2 * (1 - u) ^ 2) := by
    change scale x y / 2 = _
    rw [hA]
    field_simp [hk₀, hu.ne']
  have he : e β q = 2 / (1 - u) - 1 - 2 * (q - 1) * u * (1 - k) / (1 - u) ^ 2 := by
    change coth y - scale x y * (coth x - 1) = _
    rw [hA, hcx, hcy]
    field_simp [hk₀, hk.ne', hu.ne']
    ring
  have hd : d β q = 2 / (1 - u) - 3 / 2 - (1 + k * u) / ((1 - u) * (1 - k)) +
      2 * (q - 1) * (k * u) / (1 - u) ^ 2 := by
    change -1 + (1 - coth x / 2) * coth y + scale x y / 2 * (coth x - 1) ^ 2 = _
    rw [hA, hcx, hcy]
    field_simp [hk₀, hk.ne', hu.ne']
    ring
  rw [ha, he, hd]

/-- The exponential Gibbs endpoint drop has a positive leading coefficient and attains its
positive Schur complement as the minimum over the shifted population coordinate. -/
theorem exponent_endpoint_schur_pos {β p r : ℝ} (hβ : 0 < β) (hp : 1 < p) (hpr : p < r) :
    0 < exponentA β p - exponentA β r ∧
    0 < exponentD β p - exponentD β r -
      (exponentE β p - exponentE β r) ^ 2 / (4 * (exponentA β p - exponentA β r)) ∧
    let A := exponentA β p - exponentA β r
    let E := exponentE β p - exponentE β r
    let D := exponentD β p - exponentD β r
    IsLeast (range (fun s : ℝ => A * s ^ 2 + E * s + D)) (D - E ^ 2 / (4 * A)) := by
  have coefficients (q : ℝ) (hq : 1 < q) :
      a β q = exponentA β q ∧ e β q = exponentE β q ∧ d β q = exponentD β q := by
    have h := K_eq_exponentK hβ hq
    refine ⟨congrArg (fun M => M 0 0) h, ?_, congrArg (fun M => M 1 1) h⟩
    have he : e β q / 2 = exponentE β q / 2 := congrArg (fun M => M 0 1) h
    linarith
  obtain ⟨hap, hep, hdp⟩ := coefficients p hp
  obtain ⟨har, her, hdr⟩ := coefficients r (hp.trans hpr)
  have h := endpoint_schur_pos hβ hp hpr
  rw [hap, har, hep, her, hdp, hdr] at h
  obtain ⟨hA, hSchur⟩ := h
  refine ⟨hA, hSchur, ?_⟩
  dsimp only
  let A := exponentA β p - exponentA β r
  let E := exponentE β p - exponentE β r
  let D := exponentD β p - exponentD β r
  change IsLeast (range (fun s : ℝ => A * s ^ 2 + E * s + D)) (D - E ^ 2 / (4 * A))
  have square (s : ℝ) :
      A * s ^ 2 + E * s + D = D - E ^ 2 / (4 * A) + A * (s + E / (2 * A)) ^ 2 := by
    field_simp [show A ≠ 0 from hA.ne']
    ring
  constructor
  · refine ⟨-(E / (2 * A)), ?_⟩
    dsimp only
    rw [square, neg_add_cancel, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero]
  · rintro _ ⟨s, rfl⟩
    dsimp only
    rw [square]
    exact le_add_of_nonneg_right (mul_nonneg hA.le (sq_nonneg _))

end D5.S3.Quantum.Semigroups.WuCriticalQuartic
