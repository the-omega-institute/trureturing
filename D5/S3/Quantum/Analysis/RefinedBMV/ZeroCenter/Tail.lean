/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Tail
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strictly positive curvature of the zero-centered profile on the tail. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Moments
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Profile
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Taylor estimates through order two and strict curvature of the profile on the tail. -/

open Filter
open scoped Topology

noncomputable section

namespace RefinedBMV.FourSpectrumLift

/-- A first derivative on a neighborhood and its derivative at the center. -/
private structure Taylor2 (c : ℝ) (f : ℝ → ℝ) where
  d₁ : ℝ → ℝ
  d₂ : ℝ
  first : ∀ᶠ x in 𝓝 c, HasDerivAt f (d₁ x) x
  second : HasDerivAt d₁ d₂ c

namespace Taylor2

variable {c : ℝ} {f g : ℝ → ℝ}

private theorem firstAt (j : Taylor2 c f) : HasDerivAt f (j.d₁ c) c :=
  j.first.self_of_nhds

private def norm (j : Taylor2 c f) : ℝ := |f c| + |j.d₁ c| + |j.d₂| / 2

private theorem norm_nonneg (j : Taylor2 c f) : 0 ≤ j.norm := by
  unfold norm
  positivity

private theorem abs_value_le (j : Taylor2 c f) : |f c| ≤ j.norm := by
  unfold norm
  linarith [abs_nonneg (j.d₁ c), abs_nonneg j.d₂]

private theorem abs_first_le (j : Taylor2 c f) : |j.d₁ c| ≤ j.norm := by
  unfold norm
  linarith [abs_nonneg (f c), abs_nonneg j.d₂]

private def const (c a : ℝ) : Taylor2 c (fun _ ↦ a) where
  d₁ := fun _ ↦ 0
  d₂ := 0
  first := Eventually.of_forall fun x ↦ hasDerivAt_const x a
  second := hasDerivAt_const c 0

private theorem norm_const (c a : ℝ) : (const c a).norm = |a| := by
  simp [const, norm]

private def add (j : Taylor2 c f) (k : Taylor2 c g) : Taylor2 c (fun x ↦ f x + g x) where
  d₁ := fun x ↦ j.d₁ x + k.d₁ x
  d₂ := j.d₂ + k.d₂
  first := j.first.mp (k.first.mono fun _ hk hj ↦ hj.add hk)
  second := j.second.add k.second

private def sub (j : Taylor2 c f) (k : Taylor2 c g) : Taylor2 c (fun x ↦ f x - g x) where
  d₁ := fun x ↦ j.d₁ x - k.d₁ x
  d₂ := j.d₂ - k.d₂
  first := j.first.mp (k.first.mono fun _ hk hj ↦ hj.sub hk)
  second := j.second.sub k.second

private theorem norm_add_le (j : Taylor2 c f) (k : Taylor2 c g) :
    (j.add k).norm ≤ j.norm + k.norm := by
  dsimp [norm, add]
  linarith [abs_add_le (f c) (g c), abs_add_le (j.d₁ c) (k.d₁ c), abs_add_le j.d₂ k.d₂]

private theorem norm_sub_le (j : Taylor2 c f) (k : Taylor2 c g) :
    (j.sub k).norm ≤ j.norm + k.norm := by
  dsimp [norm, sub]
  linarith [abs_sub (f c) (g c), abs_sub (j.d₁ c) (k.d₁ c), abs_sub j.d₂ k.d₂]

private def scale (a : ℝ) (j : Taylor2 c f) : Taylor2 c (fun x ↦ a * f x) where
  d₁ := fun x ↦ a * j.d₁ x
  d₂ := a * j.d₂
  first := j.first.mono fun _ hj ↦ hj.const_mul a
  second := j.second.const_mul a

private theorem norm_scale (a : ℝ) (j : Taylor2 c f) :
    (j.scale a).norm = |a| * j.norm := by
  dsimp [norm, scale]
  simp only [abs_mul]
  ring

private def mul (j : Taylor2 c f) (k : Taylor2 c g) : Taylor2 c (fun x ↦ f x * g x) where
  d₁ := fun x ↦ j.d₁ x * g x + f x * k.d₁ x
  d₂ := j.d₂ * g c + 2 * j.d₁ c * k.d₁ c + f c * k.d₂
  first := j.first.mp (k.first.mono fun _ hk hj ↦ hj.mul hk)
  second := by
    apply ((j.second.mul k.firstAt).add (j.firstAt.mul k.second)).congr_deriv
    ring

private theorem norm_mul_le (j : Taylor2 c f) (k : Taylor2 c g) :
    (j.mul k).norm ≤ j.norm * k.norm := by
  have h₁ := abs_add_le (j.d₁ c * g c) (f c * k.d₁ c)
  have h₂ := abs_add_le (j.d₂ * g c + 2 * j.d₁ c * k.d₁ c) (f c * k.d₂)
  have h₂' := abs_add_le (j.d₂ * g c) (2 * j.d₁ c * k.d₁ c)
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h₁ h₂ h₂' ⊢
  dsimp [norm, mul]
  rw [abs_mul]
  nlinarith only [h₁, h₂, h₂',
    mul_nonneg (abs_nonneg (j.d₁ c)) (abs_nonneg k.d₂),
    mul_nonneg (abs_nonneg j.d₂) (abs_nonneg (k.d₁ c)),
    mul_nonneg (abs_nonneg j.d₂) (abs_nonneg k.d₂)]

private theorem norm_eq_of_eventuallyEq (j : Taylor2 c f) (k : Taylor2 c g)
    (h : f =ᶠ[𝓝 c] g) : j.norm = k.norm := by
  have hj : j.d₁ =ᶠ[𝓝 c] deriv f := j.first.mono fun _ hx ↦ hx.deriv.symm
  have hk : k.d₁ =ᶠ[𝓝 c] deriv g := k.first.mono fun _ hx ↦ hx.deriv.symm
  have hd := hj.trans (h.deriv.trans hk.symm)
  rw [norm, norm, h.self_of_nhds, hd.self_of_nhds,
    ← j.second.deriv, ← k.second.deriv, hd.deriv_eq]

private def expLinear (c a : ℝ) : Taylor2 c (fun x ↦ Real.exp (a * x)) where
  d₁ := fun x ↦ Real.exp (a * x) * a
  d₂ := Real.exp (a * c) * a * a
  first := Eventually.of_forall fun x ↦ by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul a).exp
  second := by
    have he : HasDerivAt (fun x : ℝ ↦ Real.exp (a * x)) (Real.exp (a * c) * a) c := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id c).const_mul a).exp
    exact he.mul_const a

private theorem norm_expLinear (c a : ℝ) :
    (expLinear c a).norm = (1 + |a| + a ^ 2 / 2) * Real.exp (a * c) := by
  dsimp [norm, expLinear]
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [mul_assoc (Real.exp _) |a| |a|, ← pow_two, sq_abs]
  ring

private def inv (j : Taylor2 c f) (hf : f c ≠ 0) : Taylor2 c (fun x ↦ (f x)⁻¹) where
  d₁ := fun x ↦ -j.d₁ x / f x ^ 2
  d₂ := 2 * (j.d₁ c)^2 / (f c)^3 - j.d₂ / (f c)^2
  first := by
    have hn := j.firstAt.continuousAt.eventually_ne hf
    filter_upwards [j.first, hn] with x hx hfx
    exact hx.inv hfx
  second := by
    apply (j.second.neg.div (j.firstAt.pow 2) (pow_ne_zero 2 hf)).congr_deriv
    simp only [Pi.neg_apply, Pi.pow_apply]
    field_simp [hf]
    ring

private theorem abs_div_le (x : ℝ) {d : ℝ} (hd : 1 ≤ d) : |x / d| ≤ |x| := by
  rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ d)]
  exact div_le_self (abs_nonneg _) hd

private theorem norm_inv_le (j : Taylor2 c f) (hf : 1 ≤ f c) :
    (j.inv (by linarith)).norm ≤ 1 + |j.d₁ c| + |j.d₂| / 2 + |j.d₁ c|^2 := by
  have h₀ : |(f c)⁻¹| ≤ 1 := by simpa [one_div] using abs_div_le 1 hf
  have h₁ := abs_div_le (-j.d₁ c) (one_le_pow₀ hf (n := 2))
  have h₂ := abs_div_le (2 * (j.d₁ c)^2) (one_le_pow₀ hf (n := 3))
  have h₂' := abs_div_le j.d₂ (one_le_pow₀ hf (n := 2))
  have ht := abs_sub (2 * (j.d₁ c)^2 / (f c)^3) (j.d₂ / (f c)^2)
  rw [abs_neg] at h₁
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (j.d₁ c)^2)] at h₂
  dsimp [norm, inv]
  rw [sq_abs]
  linarith only [h₀, h₁, h₂, h₂', ht]

private def oneSubSqrt (j : Taylor2 c f) (hf : 0 < 1 - f c) :
    Taylor2 c (fun x ↦ 1 - √(1 - f x)) where
  d₁ := fun x ↦ j.d₁ x / (2 * √(1 - f x))
  d₂ := j.d₂ / (2 * √(1 - f c)) + (j.d₁ c)^2 / (4 * (√(1 - f c))^3)
  first := by
    have hcont : ContinuousAt (fun x ↦ 1 - f x) c :=
      continuousAt_const.sub j.firstAt.continuousAt
    have hn : ∀ᶠ x in 𝓝 c, 0 < 1 - f x := hcont.eventually_mem (Ioi_mem_nhds hf)
    filter_upwards [j.first, hn] with x hx hfx
    have hs := ((hasDerivAt_const x (1 : ℝ)).fun_sub hx).sqrt hfx.ne'
    simpa only [zero_sub, neg_div, neg_neg] using (hasDerivAt_const x (1 : ℝ)).fun_sub hs
  second := by
    have hs : √(1 - f c) ≠ 0 := (Real.sqrt_pos.2 hf).ne'
    have hd := ((hasDerivAt_const c (1 : ℝ)).sub j.firstAt).sqrt hf.ne'
    apply (j.second.div (hd.const_mul 2) (mul_ne_zero two_ne_zero hs)).congr_deriv
    dsimp
    field_simp [hs]
    ring

private theorem norm_oneSubSqrt_le (j : Taylor2 c f) (hf : |f c| ≤ 1 / 4) :
    (j.oneSubSqrt (by linarith [le_abs_self (f c)])).norm ≤ j.norm + j.norm^2 := by
  let s := √(1 - f c)
  have hsq : s ^ 2 = 1 - f c := Real.sq_sqrt (by linarith [le_abs_self (f c)])
  have hs : (1/2 : ℝ) ≤ s := by
    have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
    by_contra! h
    have h' := mul_lt_mul_of_pos_right h (show 0 < (1/2 : ℝ) + s by positivity)
    nlinarith [le_abs_self (f c)]
  have hd : 1 ≤ 2 * s := by linarith
  have hd₃ : 1 ≤ 8 * s ^ 3 := by
    calc
      1 ≤ (2*s)^3 := one_le_pow₀ hd
      _ = _ := by ring
  have h₀ : |1-s| ≤ |f c| := by
    have h : 1 - s = f c / (1+s) := by
      apply (eq_div_iff (by linarith : 1+s ≠ 0)).2
      nlinarith
    rw [h]
    exact abs_div_le _ (by linarith)
  have h₁ := abs_div_le (j.d₁ c) hd
  have h₂ := abs_div_le j.d₂ hd
  have h₂' : |(j.d₁ c)^2 / (4*s^3)| ≤ 2 * |j.d₁ c|^2 := by
    calc
      _ = 2 * |(j.d₁ c)^2 / (8*s^3)| := by
        rw [← abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), ← abs_mul]
        congr 1
        ring
      _ ≤ _ := by
        have h := abs_div_le ((j.d₁ c)^2) hd₃
        rw [abs_pow] at h
        exact mul_le_mul_of_nonneg_left h (by norm_num)
  have htriangle := abs_add_le (j.d₂ / (2*s)) ((j.d₁ c)^2 / (4*s^3))
  have hpow := pow_le_pow_left₀ (abs_nonneg (j.d₁ c)) j.abs_first_le (2 : ℕ)
  change |1-s| + |j.d₁ c / (2*s)| +
    |j.d₂ / (2*s) + (j.d₁ c)^2 / (4*s^3)| / 2 ≤ j.norm + j.norm^2
  unfold norm at *
  linarith only [h₀, h₁, h₂, h₂', htriangle, hpow]

private theorem curvature_le (j : Taylor2 c f) :
    |(deriv^[2]) f c - deriv f c + f c / 4| ≤ 2 * j.norm := by
  have h : j.d₁ =ᶠ[𝓝 c] deriv f := j.first.mono fun _ hx ↦ hx.deriv.symm
  change |deriv (deriv f) c - deriv f c + f c / 4| ≤ _
  rw [← h.deriv_eq, j.second.deriv, h.self_of_nhds.symm]
  have h₁ := abs_sub j.d₂ (j.d₁ c)
  have h₂ := abs_add_le (j.d₂ - j.d₁ c) (f c / 4)
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at h₂
  unfold norm
  linarith [abs_nonneg (f c), abs_nonneg (j.d₁ c)]

end Taylor2

private def ramp (k h x : ℝ) : ℝ :=
  ((1 + k*h) / h) * (1 - Real.exp (-3*h*x))

private def rampTaylor (k : ℝ) {h : ℝ} (hh : 0 < h) (c : ℝ) : Taylor2 c (ramp k h) where
  d₁ := fun x ↦ (3 * (1 + k*h)) * Real.exp (-3*h*x)
  d₂ := -(9*h*(1 + k*h)) * Real.exp (-3*h*c)
  first := Eventually.of_forall fun x ↦ by
    have he := (Taylor2.expLinear x (-3*h)).firstAt
    apply (((hasDerivAt_const x (1 : ℝ)).sub he).const_mul ((1+k*h)/h)).congr_deriv
    dsimp [Taylor2.expLinear]
    field_simp [hh.ne']
    ring
  second := by
    apply ((Taylor2.expLinear c (-3*h)).firstAt.const_mul (3*(1+k*h))).congr_deriv
    dsimp [Taylor2.expLinear]
    ring

private theorem ramp_bounds {c h k : ℝ} (hc : 0 ≤ c) (hh : 0 < h)
    (hh' : h ≤ 1) (hk : 0 ≤ k) :
    let j := rampTaylor k hh c
    0 ≤ ramp k h c ∧ ramp k h c ≤ 3*(1+k)*c ∧
      |j.d₁ c| ≤ 3*(1+k) ∧ |j.d₂| ≤ 9*(1+k) := by
  have hkh : k*h ≤ k := mul_le_of_le_one_right hk hh'
  have h1kh : 0 ≤ 1 + k*h := by positivity
  have hq : Real.exp (-3*h*c) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hh.le hc])
  have hd : 1 - Real.exp (-3*h*c) ≤ 3*h*c := by
    linarith [Real.add_one_le_exp (-3*h*c)]
  have hmul : (1+k*h) / h * (1 - Real.exp (-3*h*c)) ≤ (1+k*h) / h * (3*h*c) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  have heq : (1+k*h) / h * (3*h*c) = 3*(1+k*h)*c := by
    field_simp [hh.ne']
  rw [heq] at hmul
  have ht : h * (1 + k*h) ≤ 1+k :=
    (mul_le_of_le_one_left h1kh hh').trans (by linarith)
  dsimp [rampTaylor]
  refine ⟨mul_nonneg (by positivity) (sub_nonneg.mpr hq), hmul.trans ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) hc
  · rw [abs_of_nonneg (by positivity)]
    exact (mul_le_of_le_one_right (by positivity) hq).trans (by linarith)
  · rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_neg, abs_of_nonneg (by positivity)]
    exact (mul_le_of_le_one_right (by positivity) hq).trans (by linarith)

private theorem one_le_ramp {c h : ℝ} (hc : 32 ≤ c) (hh : 0 < h) :
    1 ≤ ramp 1 h c := by
  let t := 3*h*c
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hq : Real.exp (-t) ≤ (1+t)⁻¹ := by
    rw [Real.exp_neg]
    apply inv_anti₀ (show 0 < 1+t by positivity)
    linarith [Real.add_one_le_exp t]
  have hfrac : 1 - (1+t)⁻¹ = t/(1+t) := by
    field_simp [show (1+t) ≠ 0 by positivity]
    ring
  have ha : 1 ≤ ((1+h)/h) * (t/(1+t)) := by
    have he : ((1+h)/h) * (t/(1+t)) = (3*c*(1+h))/(1+t) := by
      field_simp [hh.ne', show (1+t) ≠ 0 by positivity]
      dsimp [t]
      ring
    rw [he, le_div_iff₀ (by positivity : 0 < 1+t), one_mul]
    dsimp [t]
    nlinarith
  have hhq : t/(1+t) ≤ 1 - Real.exp (-t) := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hhq (show 0 ≤ (1+h)/h by positivity)
  simpa only [ramp, one_mul, t, neg_mul] using ha.trans hscaled

private def tailEpsilon (h x : ℝ) : ℝ :=
  Real.exp (-3 * (1+h) * x) * (1 + ramp 1 h x) +
    ((1/2) * (ramp 1 h x * ramp 2 h x)) * Real.exp (-2*x)

private def tailOffset (h x : ℝ) : ℝ :=
  Real.exp (-3 * (1+h) * x) + (1 - √(1 - tailEpsilon h x))

private def tailReciprocal (h x : ℝ) : ℝ := (2 - tailOffset h x)⁻¹

/-- The correction to one quarter of the principal factor in the rationalized profile. -/
def tailCorrection (h x : ℝ) : ℝ :=
  let q := Real.exp (-3*h*x)
  let a := ((1 + 1*h) / h) * (1-q)
  let b := ((1 + 2*h) / h) * (1-q)
  let z := Real.exp (-3*(1+h)*x)
  let ε := z*(1+a) + ((1/2)*(a*b)) * Real.exp (-2*x)
  let R := (2 - (z + (1 - √(1-ε))))⁻¹
  let η := Real.exp (-(1+3*h)*x) * (1 - (1-z)*a⁻¹)
  ((1/2)*b)*(R-1/2) + η*R

/-- The normalized curvature of the tail correction decays exponentially and is
uniformly smaller than one sixty-fourth for positive reciprocal degree at most one.
The local differentiability facts allow the correction to be added to the principal term. -/
theorem tail_correction_curvature {c h : ℝ} (hc : 32 ≤ c) (hh : 0 < h) (hh' : h ≤ 1) :
    let δ := tailCorrection h
    |(deriv^[2]) δ c - deriv δ c + δ c / 4| ≤ 13210 * Real.exp (-c) ∧
    |(deriv^[2]) δ c - deriv δ c + δ c / 4| < 1 / 64 ∧
    (∀ᶠ x in 𝓝 c, DifferentiableAt ℝ δ x) ∧ DifferentiableAt ℝ (deriv δ) c := by
  let E := Real.exp (-c)
  let P := c^2 * E^2
  have hc₀ : 0 ≤ c := by linarith
  have hc₁ : 1 ≤ c := by linarith
  have he : 0 < E := Real.exp_pos _
  have he₁ : E ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he₃₂ : E ≤ 1/(2:ℝ)^32 := calc
    E ≤ Real.exp (-32) := Real.exp_le_exp.mpr (by linarith)
    _ = ((Real.exp 1) ^ 32)⁻¹ := by
      rw [show (-32:ℝ) = -((32:ℕ)*(1:ℝ)) by norm_num, Real.exp_neg, Real.exp_nat_mul]
    _ ≤ _ := by
      rw [one_div]
      apply (inv_le_inv₀ (by positivity) (by positivity)).2
      apply pow_le_pow_left₀ (by norm_num)
      linarith [Real.add_one_le_exp 1]
  have hexp : c^3 ≤ Real.exp c := by
    have h4 := Real.pow_div_factorial_le_exp c hc₀ 4
    norm_num [Nat.factorial] at h4
    have h := mul_nonneg (sub_nonneg.mpr (show 24 ≤ c by linarith)) (pow_nonneg hc₀ 3)
    nlinarith only [h4, h]
  have hcube : c^3 * E^2 ≤ E := by
    have h := mul_le_mul_of_nonneg_right hexp he.le
    have hcancel : Real.exp c * E = 1 := by
      dsimp [E]
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [hcancel] at h
    calc
      _ = (c^3*E)*E := by ring
      _ ≤ E := by simpa only [one_mul] using mul_le_mul_of_nonneg_right h he.le
  have hp : P ≤ E := by
    have h := mul_le_mul_of_nonneg_right (show c^2 ≤ c^3 by
      simpa only [pow_succ, mul_one] using mul_le_mul_of_nonneg_left hc₁ (sq_nonneg c))
      (sq_nonneg E)
    exact h.trans hcube
  have hE3 : E^3 ≤ E^2 := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (sq_nonneg E) he₁
  have hCE3 : c*E^3 ≤ P := calc
    _ ≤ c*E^2 := mul_le_mul_of_nonneg_left hE3 hc₀
    _ ≤ P := mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hc₀ (sub_nonneg.mpr hc₁)])
      (sq_nonneg E)
  have hE3P : E^3 ≤ P := calc
    _ ≤ c*E^3 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc₁ (pow_nonneg he.le 3)
    _ ≤ _ := hCE3
  let ja := rampTaylor 1 hh c
  let jb := rampTaylor 2 hh c
  obtain ⟨ha₀, ha, ha₁, ha₂⟩ := ramp_bounds hc₀ hh hh' (show (0:ℝ) ≤ 1 by norm_num)
  obtain ⟨hb₀, hb, hb₁, hb₂⟩ := ramp_bounds hc₀ hh hh' (show (0:ℝ) ≤ 2 by norm_num)
  norm_num only at ha ha₁ ha₂ hb hb₁ hb₂
  have hna : ja.norm ≤ 7*c := by
    rw [Taylor2.norm, abs_of_nonneg ha₀]
    linarith
  have hnb : jb.norm ≤ 10*c := by
    rw [Taylor2.norm, abs_of_nonneg hb₀]
    linarith
  let jz := Taylor2.expLinear c (-3*(1+h))
  let je₂ := Taylor2.expLinear c (-2)
  let jt := Taylor2.expLinear c (-(1+3*h))
  have he₂ : je₂.norm = 5*E^2 := by
    rw [Taylor2.norm_expLinear]
    rw [show -2*c = (2:ℕ) * (-c) by push_cast; ring, Real.exp_nat_mul]
    norm_num [E]
  have hzExp : Real.exp (-3*(1+h)*c) ≤ E^3 := by
    change _ ≤ (Real.exp (-c))^3
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [mul_nonneg hh.le hc₀]
  have hz : jz.norm ≤ 25*E^3 := by
    rw [Taylor2.norm_expLinear, abs_of_nonpos (by linarith : -3*(1+h) ≤ 0)]
    have hk : 3*(1+h) ≤ 6 := by linarith
    have hsq := pow_le_pow_left₀ (show 0 ≤ 3*(1+h) by positivity) hk 2
    have hcoef : 1 + -(-3*(1+h)) + (-3*(1+h))^2/2 ≤ 25 := by
      nlinarith only [hk, hsq]
    exact (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hzExp (by norm_num))
  have ht : jt.norm ≤ 13*E := by
    rw [Taylor2.norm_expLinear, abs_of_nonpos (by linarith : -(1+3*h) ≤ 0)]
    have hk : 1+3*h ≤ 4 := by linarith
    have hsq := pow_le_pow_left₀ (show 0 ≤ 1+3*h by positivity) hk 2
    have he' : Real.exp (-(1+3*h)*c) ≤ E :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hh.le hc₀])
    have hcoef : 1 + -(-(1+3*h)) + (-(1+3*h))^2/2 ≤ 13 := by
      nlinarith only [hk, hsq]
    exact (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)).trans
      (mul_le_mul_of_nonneg_left he' (by norm_num))
  let one := Taylor2.const c 1
  let two := Taylor2.const c 2
  let half := Taylor2.const c (1/2)
  have hone : one.norm = 1 := by norm_num [one, Taylor2.norm_const]
  let je : Taylor2 c (tailEpsilon h) :=
    (jz.mul (one.add ja)).add (((ja.mul jb).scale (1/2)).mul je₂)
  have hea : (one.add ja).norm ≤ 8*c := by linarith [one.norm_add_le ja]
  have heab : (ja.mul jb).norm ≤ (7*c)*(10*c) :=
    (ja.norm_mul_le jb).trans (mul_le_mul hna hnb jb.norm_nonneg (by positivity))
  have hex : (jz.mul (one.add ja)).norm ≤ 200*P := calc
    _ ≤ (25*E^3)*(8*c) :=
      (jz.norm_mul_le (one.add ja)).trans
        (mul_le_mul hz hea (one.add ja).norm_nonneg (by positivity))
    _ = 200*(c*E^3) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hCE3 (by norm_num)
  have hey : (((ja.mul jb).scale (1/2)).mul je₂).norm ≤ 175*P := calc
    _ ≤ (ja.mul jb).norm * (1/2) * (5*E^2) := by
      have h := ((ja.mul jb).scale (1/2)).norm_mul_le je₂
      rw [Taylor2.norm_scale, he₂, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at h
      simpa only [mul_comm ((ja.mul jb).norm) (1/2)] using h
    _ ≤ ((7*c)*(10*c)) * (1/2) * (5*E^2) := by gcongr
    _ = _ := by dsimp [P]; ring
  have hne : je.norm ≤ 375*P := by
    have hj := (jz.mul (one.add ja)).norm_add_le (((ja.mul jb).scale (1/2)).mul je₂)
    change je.norm ≤ _ at hj
    linarith
  have hep : je.norm ≤ 1 / 4 := by
    linarith [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 375 by norm_num)]
  have hepp : |tailEpsilon h c| ≤ 1/4 := je.abs_value_le.trans hep
  let js := je.oneSubSqrt (by linarith [le_abs_self (tailEpsilon h c)])
  have hs : js.norm ≤ 2*je.norm := by
    have hj : js.norm ≤ je.norm + je.norm^2 := je.norm_oneSubSqrt_le hepp
    have hq := mul_le_of_le_one_right je.norm_nonneg (show je.norm ≤ 1 by linarith)
    nlinarith only [hj, hq]
  let ju : Taylor2 c (tailOffset h) := jz.add js
  have hnu : ju.norm ≤ 775*P := by
    have hj : ju.norm ≤ jz.norm + js.norm := jz.norm_add_le js
    linarith [mul_le_mul_of_nonneg_left hE3P (show (0:ℝ) ≤ 25 by norm_num)]
  have hnu' : ju.norm ≤ 1 / 4 := by
    linarith [mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 775 by norm_num)]
  let jd := two.sub ju
  have hden : 1 ≤ 2 - tailOffset h c := by
    linarith [ju.abs_value_le, le_abs_self (tailOffset h c)]
  have hden₀ : 2 - tailOffset h c ≠ 0 := by linarith
  let jr : Taylor2 c (tailReciprocal h) := jd.inv hden₀
  have hnr : jr.norm ≤ 2 := by
    have hr : jr.norm ≤ 1 + |ju.d₁ c| + |ju.d₂| / 2 + |ju.d₁ c|^2 := by
      have hj := jd.norm_inv_le hden
      change jr.norm ≤ _ at hj
      dsimp [jd, two, Taylor2.sub, Taylor2.const] at hj
      simpa only [zero_sub, abs_neg] using hj
    have hpow := pow_le_pow_left₀ (abs_nonneg (ju.d₁ c)) ju.abs_first_le 2
    have hsq := mul_le_of_le_one_right ju.norm_nonneg (show ju.norm ≤ 1 by linarith)
    unfold Taylor2.norm at hnu' hsq hpow
    linarith only [hr, hnu', hpow, hsq, abs_nonneg (tailOffset h c)]
  have hrsub : (jr.sub half).norm ≤ ju.norm := calc
    _ = ((ju.mul jr).scale (1/2)).norm := by
      apply Taylor2.norm_eq_of_eventuallyEq
      filter_upwards [jd.firstAt.continuousAt.eventually_ne hden₀] with x hx
      change (2-tailOffset h x)⁻¹ - 1/2 = (1/2) * (tailOffset h x * (2-tailOffset h x)⁻¹)
      change 2 - tailOffset h x ≠ 0 at hx
      field_simp [hx]
      ring
    _ = (1/2)*(ju.mul jr).norm := by rw [Taylor2.norm_scale, abs_of_nonneg (by norm_num)]
    _ ≤ _ := by
      have h := ju.norm_mul_le jr
      have h' := mul_le_mul_of_nonneg_left hnr ju.norm_nonneg
      linarith
  let jv := one.sub jz
  have hv : jv.norm ≤ 2 := by
    change (one.sub jz).norm ≤ 2
    have h := one.norm_sub_le jz
    have hz' := (hz.trans (mul_le_mul_of_nonneg_left hE3P (by norm_num : (0:ℝ) ≤ 25))).trans
      (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 25))
    linarith
  have hail : 1 ≤ ramp 1 h c := one_le_ramp hc hh
  let jai := ja.inv (by linarith)
  have hai : jai.norm ≤ 52 := by
    have h : jai.norm ≤ 1 + |ja.d₁ c| + |ja.d₂| / 2 + |ja.d₁ c|^2 := ja.norm_inv_le hail
    have hs := pow_le_pow_left₀ (abs_nonneg (ja.d₁ c)) ha₁ 2
    linarith
  let jeta := jt.mul (one.sub (jv.mul jai))
  have hve : (one.sub (jv.mul jai)).norm ≤ 105 := by
    have h := one.norm_sub_le (jv.mul jai)
    have h' := (jv.norm_mul_le jai).trans (mul_le_mul hv hai jai.norm_nonneg (by norm_num))
    linarith
  have hη : jeta.norm ≤ 1365*E := calc
    _ ≤ (13*E)*105 :=
      (jt.norm_mul_le _).trans
        (mul_le_mul ht hve (one.sub (jv.mul jai)).norm_nonneg (by positivity))
    _ = _ := by ring
  let jpart := (jb.scale (1/2)).mul (jr.sub half)
  let jδ : Taylor2 c (tailCorrection h) := jpart.add (jeta.mul jr)
  have hpart : jpart.norm ≤ 3875*E := calc
    _ ≤ ((1/2)*(10*c)) * (775*P) := by
      apply ((jb.scale (1/2)).norm_mul_le (jr.sub half)).trans
      rw [Taylor2.norm_scale, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hnb (by norm_num)) (hrsub.trans hnu)
        (jr.sub half).norm_nonneg (by positivity)
    _ = 3875*(c^3*E^2) := by dsimp [P]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcube (by norm_num)
  have hpart' : (jeta.mul jr).norm ≤ 2730*E := calc
    _ ≤ (1365*E)*2 :=
      (jeta.norm_mul_le jr).trans (mul_le_mul hη hnr jr.norm_nonneg (by positivity))
    _ = _ := by ring
  have hd : jδ.norm ≤ 6605*E := by
    have h : jδ.norm ≤ jpart.norm + (jeta.mul jr).norm := jpart.norm_add_le (jeta.mul jr)
    linarith
  have hbnd := jδ.curvature_le.trans (show 2*jδ.norm ≤ 13210*E by linarith)
  have hderiv : deriv (tailCorrection h) =ᶠ[𝓝 c] jδ.d₁ :=
    jδ.first.mono fun _ hx ↦ hx.deriv
  exact ⟨hbnd, hbnd.trans_lt (by linarith), jδ.first.mono fun _ hx ↦ hx.differentiableAt,
    (jδ.second.congr_of_eventuallyEq hderiv).differentiableAt⟩

#print axioms tail_correction_curvature

private theorem zeroProfile_eq_exp_mul_tail {p : ℕ} (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    let h : ℝ := 1 / p
    zeroProfile p x = Real.exp ((-1/2)*x) * ((1/4) * ramp 2 h x + tailCorrection h x) := by
  let h : ℝ := 1 / p
  let d := 1 - Real.exp (-3*h*x)
  let z := Real.exp (-3*(1+h)*x)
  have hpℝ : 0 < (p : ℝ) := by exact_mod_cast hp
  have ha : ramp 1 h x = (p+1 : ℝ) * d := by
    have hscale : (1+1*h)/h = (p+1 : ℝ) := by
      dsimp [h]
      field_simp [hpℝ.ne']
    rw [ramp, hscale]
  have hb : ramp 2 h x = (p+2 : ℝ) * d := by
    have hscale : (1+2*h)/h = (p+2 : ℝ) := by
      dsimp [h]
      field_simp [hpℝ.ne']
    rw [ramp, hscale]
  have hs : rationalizedRadicand x h = 1 - tailEpsilon h x := by
    unfold rationalizedRadicand tailEpsilon ramp
    simp only [one_mul]
    ring
  have hden : (1-z) + √(rationalizedRadicand x h) = 2 - tailOffset h x := by
    rw [hs]
    change (1-z) + √(1 - tailEpsilon h x) = 2 - (z + (1 - √(1 - tailEpsilon h x)))
    ring
  have hprofile := zeroProfile_eq_tail_formula hp hx
  change zeroProfile p x = Real.exp (-x/2) *
    (((p+2 : ℝ) * d / 2 + Real.exp (-(1+3*h)*x) * (1 - (1-z)/((p+1 : ℝ)*d))) /
      ((1-z) + √(rationalizedRadicand x h))) at hprofile
  rw [← ha, ← hb, hden, div_eq_mul_inv (1-z), div_eq_mul_inv _ (2 - tailOffset h x)] at hprofile
  change zeroProfile p x = Real.exp ((-1/2)*x) * ((1/4) * ramp 2 h x + tailCorrection h x)
  rw [hprofile, show -x/2 = (-1/2)*x by ring]
  let R := tailReciprocal h x
  let η := Real.exp (-(1+3*h)*x) * (1 - (1-z)*(ramp 1 h x)⁻¹)
  change Real.exp ((-1/2)*x) * ((ramp 2 h x / 2 + η) * R) =
    Real.exp ((-1/2)*x) * ((1/4) * ramp 2 h x + ((1/2) * ramp 2 h x * (R - 1/2) + η*R))
  congr 1
  ring

private theorem Taylor2.deriv_two {c : ℝ} {f : ℝ → ℝ} (j : Taylor2 c f) :
    deriv^[2] f c = j.d₂ := by
  have h : deriv f =ᶠ[𝓝 c] j.d₁ := j.first.mono fun _ hx ↦ hx.deriv
  change deriv (deriv f) c = j.d₂
  exact h.deriv_eq.trans j.second.deriv

/-- The zero-centered profile has strictly positive second derivative for gaps at least 32. -/
theorem zeroProfile_tail_curvature_pos {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 32 ≤ c) :
    0 < deriv^[2] (zeroProfile p) c := by
  let h : ℝ := 1 / p
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hh : 0 < h := div_pos one_pos (lt_of_lt_of_le zero_lt_one hp₁)
  have hh₁ : h ≤ 1 := div_le_one (lt_of_lt_of_le zero_lt_one hp₁) |>.mpr hp₁
  let b := ramp 2 h
  let δ := tailCorrection h
  have hb : 1/32 < (deriv^[2] b c - deriv b c + b c / 4) / 4 :=
    tail_principal_curvature hc hh hh₁
  obtain ⟨_, hδ, hδ₁, hδ₂⟩ := tail_correction_curvature hc hh hh₁
  have hcurv : 0 < (deriv^[2] b c - deriv b c + b c / 4) / 4 +
      (deriv^[2] δ c - deriv δ c + δ c / 4) := by
    change |deriv^[2] δ c - deriv δ c + δ c / 4| < 1/64 at hδ
    linarith only [hb, (abs_lt.mp hδ).1]
  have hprofile : zeroProfile p =ᶠ[𝓝 c]
      (fun x ↦ Real.exp ((-1/2)*x) * ((1/4) * b x + δ x)) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < c by linarith)] with x hx
    exact zeroProfile_eq_exp_mul_tail hp hx
  let jb : Taylor2 c b := rampTaylor 2 hh c
  let jδ : Taylor2 c δ := {
    d₁ := deriv δ
    d₂ := deriv (deriv δ) c
    first := hδ₁.mono fun _ hx ↦ hx.hasDerivAt
    second := hδ₂.hasDerivAt }
  let j := (Taylor2.expLinear c (-1/2)).mul ((jb.scale (1/4)).add jδ)
  have hsecond : j.d₂ = Real.exp ((-1/2)*c) *
      ((deriv^[2] b c - deriv b c + b c / 4) / 4 +
        (deriv^[2] δ c - deriv δ c + δ c / 4)) := by
    simp only [j, Taylor2.mul, Taylor2.expLinear, Taylor2.add, Taylor2.scale, jδ]
    rw [← jb.deriv_two, ← jb.firstAt.deriv]
    change _ = Real.exp ((-1/2)*c) *
      ((deriv^[2] b c - deriv b c + b c / 4) / 4 +
        (deriv (deriv δ) c - deriv δ c + δ c / 4))
    ring
  have hderiv : deriv^[2] (zeroProfile p) c = j.d₂ :=
    hprofile.deriv.deriv_eq.trans j.deriv_two
  rw [hderiv, hsecond]
  exact mul_pos (Real.exp_pos _) hcurv

#print axioms zeroProfile_tail_curvature_pos

end RefinedBMV.FourSpectrumLift
