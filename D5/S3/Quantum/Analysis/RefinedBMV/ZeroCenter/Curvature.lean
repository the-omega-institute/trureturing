/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Curvature
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The second derivative of the zero-centered profile via its stable positive-gap formula. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Profile
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue

open Filter Set
open scoped Topology

namespace RefinedBMV.FourSpectrumLift

/-- Value, first derivative, and half the second derivative. -/
structure CurvatureJet (R : Type) where
  value : R
  first : R
  second : R

namespace CurvatureJet

variable {R : Type}

def const [Zero R] (a : R) : CurvatureJet R := ⟨a, 0, 0⟩

def add [Add R] (a b : CurvatureJet R) : CurvatureJet R :=
  ⟨a.value + b.value, a.first + b.first, a.second + b.second⟩

def sub [Sub R] (a b : CurvatureJet R) : CurvatureJet R :=
  ⟨a.value - b.value, a.first - b.first, a.second - b.second⟩

def mul [Add R] [Mul R] (a b : CurvatureJet R) : CurvatureJet R :=
  ⟨a.value * b.value,
    a.value * b.first + a.first * b.value,
    a.value * b.second + a.first * b.first + a.second * b.value⟩

def scale [Mul R] (a : R) (b : CurvatureJet R) : CurvatureJet R :=
  ⟨a * b.value, a * b.first, a * b.second⟩

def quot [Sub R] [Add R] [Mul R] [Div R] (a b : CurvatureJet R) : CurvatureJet R :=
  let q := a.value / b.value
  let q₁ := (a.first - b.first * q) / b.value
  ⟨q, q₁, (a.second - (b.first * q₁ + b.second * q)) / b.value⟩

def sqrtFrom [OfNat R 2] [Sub R] [Mul R] [Div R] (a : CurvatureJet R) (r : R) :
    CurvatureJet R :=
  let r₁ := a.first / (2 * r)
  ⟨r, r₁, (a.second - r₁ * r₁) / (2 * r)⟩

def exponential [OfNat R 2] [Mul R] [Div R] (k e : R) : CurvatureJet R :=
  ⟨e, k * e, (k * k * e) / 2⟩

def IsJet (f : ℝ → CurvatureJet ℝ) (c : ℝ) : Prop :=
  HasDerivAt (fun x ↦ (f x).value) (f c).first c ∧
    HasDerivAt (fun x ↦ (f x).first) (2 * (f c).second) c

private theorem isJet_const (a c : ℝ) : IsJet (fun _ ↦ const a) c :=
  ⟨hasDerivAt_const c a, by simpa [const] using hasDerivAt_const c (0 : ℝ)⟩

private theorem IsJet.add {f g : ℝ → CurvatureJet ℝ} {c : ℝ}
    (hf : IsJet f c) (hg : IsJet g c) : IsJet (fun x ↦ add (f x) (g x)) c := by
  refine ⟨hf.1.add hg.1, ?_⟩
  change HasDerivAt (fun x ↦ (f x).first + (g x).first)
    (2 * ((f c).second + (g c).second)) c
  rw [mul_add]
  exact hf.2.add hg.2

private theorem IsJet.sub {f g : ℝ → CurvatureJet ℝ} {c : ℝ}
    (hf : IsJet f c) (hg : IsJet g c) : IsJet (fun x ↦ sub (f x) (g x)) c := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  change HasDerivAt (fun x ↦ (f x).first - (g x).first)
    (2 * ((f c).second - (g c).second)) c
  rw [mul_sub]
  exact hf.2.sub hg.2

theorem IsJet.mul {f g : ℝ → CurvatureJet ℝ} {c : ℝ}
    (hf : IsJet f c) (hg : IsJet g c) : IsJet (fun x ↦ mul (f x) (g x)) c := by
  refine ⟨?_, ?_⟩
  · change HasDerivAt (fun x ↦ (f x).value * (g x).value)
      ((f c).value * (g c).first + (f c).first * (g c).value) c
    rw [add_comm]
    exact hf.1.mul hg.1
  · change HasDerivAt (fun x ↦ (f x).value * (g x).first + (f x).first * (g x).value) _ c
    convert (hf.1.mul hg.2).add (hf.2.mul hg.1) using 1
    simp only [CurvatureJet.mul]
    ring

theorem IsJet.scale {f : ℝ → CurvatureJet ℝ} {c : ℝ}
    (hf : IsJet f c) (a : ℝ) : IsJet (fun x ↦ scale a (f x)) c := by
  refine ⟨hf.1.const_mul a, ?_⟩
  convert hf.2.const_mul a using 1 <;> simp only [CurvatureJet.scale] <;> ring

theorem IsJet.quot {f g : ℝ → CurvatureJet ℝ} {c : ℝ}
    (hf : IsJet f c) (hg : IsJet g c) (h : (g c).value ≠ 0) :
    IsJet (fun x ↦ quot (f x) (g x)) c := by
  have hq : HasDerivAt (fun x ↦ (f x).value / (g x).value) (CurvatureJet.quot (f c) (g c)).first c := by
    convert hf.1.div hg.1 h using 1
    simp only [CurvatureJet.quot]
    field_simp
  refine ⟨hq, ?_⟩
  change HasDerivAt
    (fun x ↦ ((f x).first - (g x).first * ((f x).value / (g x).value)) / (g x).value)
    _ c
  have hnum := hf.2.sub (hg.2.mul hq)
  change HasDerivAt
    (fun x ↦ (f x).first - (g x).first * ((f x).value / (g x).value)) _ c at hnum
  convert hnum.div hg.1 h using 1
  simp only [CurvatureJet.quot]
  field_simp
  <;> ring

theorem IsJet.sqrtFrom {f : ℝ → CurvatureJet ℝ} {c : ℝ}
    (hf : IsJet f c) (h : 0 < (f c).value) :
    IsJet (fun x ↦ sqrtFrom (f x) (Real.sqrt (f x).value)) c := by
  have hr := hf.1.sqrt h.ne'
  have hroot : Real.sqrt (f c).value ≠ 0 := (Real.sqrt_pos.2 h).ne'
  refine ⟨hr, ?_⟩
  change HasDerivAt (fun x ↦ (f x).first / (2 * Real.sqrt (f x).value)) _ c
  convert hf.2.div (hr.const_mul 2) (mul_ne_zero (by norm_num) hroot) using 1
  simp only [CurvatureJet.sqrtFrom]
  field_simp
  <;> ring

private theorem isJet_exponential (k c : ℝ) :
    IsJet (fun x ↦ exponential k (Real.exp (k * x))) c := by
  have he : HasDerivAt (fun x : ℝ ↦ Real.exp (k * x)) (k * Real.exp (k * c)) c := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id c).const_mul k).exp
  refine ⟨he, ?_⟩
  change HasDerivAt (fun x ↦ k * Real.exp (k * x)) (2 * (k * k * Real.exp (k * c) / 2)) c
  convert he.const_mul k using 1 <;> ring

end CurvatureJet

open CurvatureJet

noncomputable section

/-- The geometric quotient analytically continued in the parameter at zero. -/
def zeroCenterGeometric (c h : ℝ) : ℝ :=
  if h = 0 then 3 * c else (1 - Real.exp (-3 * h * c)) / h

def zeroCenterGeometricJet {R : Type} [OfNat R 3] [OfNat R 9] [OfNat R 2] [Neg R] [Mul R] [Div R]
    (h s q : R) : CurvatureJet R :=
  ⟨s, 3 * q, -(9 * h * q) / 2⟩

private theorem isJet_geometric (h c : ℝ) (hh : h ≠ 0) :
    IsJet (fun x ↦ zeroCenterGeometricJet h (zeroCenterGeometric x h)
      (Real.exp (-3 * h * x))) c := by
  have he : HasDerivAt (fun x ↦ Real.exp (-3 * h * x))
      ((-3 * h) * Real.exp (-3 * h * c)) c :=
    (isJet_exponential (-3 * h) c).1
  refine ⟨?_, ?_⟩
  · change HasDerivAt (fun x ↦ zeroCenterGeometric x h) (3 * Real.exp (-3 * h * c)) c
    simp only [zeroCenterGeometric, ite_eq_right hh]
    convert ((hasDerivAt_const c (1 : ℝ)).sub he).div_const h using 1
    field_simp
    <;> ring
  · change HasDerivAt (fun x ↦ 3 * Real.exp (-3 * h * x))
      (2 * (-(9 * h * Real.exp (-3 * h * c)) / 2)) c
    convert he.const_mul 3 using 1 <;> ring

section Formula

variable {R : Type} [Zero R] [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4] [OfNat R 9]
  [Add R] [Sub R] [Neg R] [Mul R] [Div R]

def zeroCenterAB (h s q : R) : CurvatureJet R × CurvatureJet R :=
  let t := zeroCenterGeometricJet h s q
  (scale (1 + h) t, scale (1 + 2 * h) t)

def zeroCenterV (h z : R) : CurvatureJet R :=
  sub (const 1) (exponential (-(3 * (1 + h))) z)

def zeroCenterRadicandJet (h s q z e : R) : CurvatureJet R :=
  let (a, b) := zeroCenterAB h s q
  sub (sub (const 1) (mul (exponential (-(3 * (1 + h))) z) (add (const 1) a)))
    (scale (1 / 2) (mul (mul a b) (exponential (-2) e)))

def zeroCenterQuotientJet (h s q z e u root : R) : CurvatureJet R :=
  let (a, b) := zeroCenterAB h s q
  let v := zeroCenterV h z
  let n := add (scale (1 / 2) b)
    (mul (exponential (-(1 + 3 * h)) u) (sub (const 1) (quot v a)))
  let d := add v (sqrtFrom (zeroCenterRadicandJet h s q z e) root)
  quot n d

/-- The curvature after removing the positive factor `exp (-c / 2)`. -/
def zeroCenterCurvature (h s q z e u root : R) : R :=
  let g := zeroCenterQuotientJet h s q z e u root
  2 * g.second - g.first + g.value / 4

end Formula

theorem zeroCenterRadicandJet_value (c h : ℝ) (hh : h ≠ 0) :
    (zeroCenterRadicandJet h (zeroCenterGeometric c h) (Real.exp (-3 * h * c))
      (Real.exp (-(3 * (1 + h)) * c)) (Real.exp (-2 * c))).value =
        rationalizedRadicand c h := by
  simp only [zeroCenterRadicandJet, zeroCenterAB, zeroCenterGeometric, ite_eq_right hh,
    rationalizedRadicand, zeroCenterGeometricJet, scale, sub, const, mul, exponential, add]
  ring_nf

private def geometryJet (h x : ℝ) : CurvatureJet ℝ :=
  zeroCenterGeometricJet h (zeroCenterGeometric x h) (Real.exp (-3 * h * x))

private def radicandJet (h x : ℝ) : CurvatureJet ℝ :=
  zeroCenterRadicandJet h (zeroCenterGeometric x h) (Real.exp (-3 * h * x))
    (Real.exp (-(3 * (1 + h)) * x)) (Real.exp (-2 * x))

private def quotientJet (h x : ℝ) : CurvatureJet ℝ :=
  zeroCenterQuotientJet h (zeroCenterGeometric x h) (Real.exp (-3 * h * x))
    (Real.exp (-(3 * (1 + h)) * x)) (Real.exp (-2 * x))
    (Real.exp (-(1 + 3 * h) * x)) (Real.sqrt (rationalizedRadicand x h))

private theorem isJet_quotient (h c : ℝ) (hh : 0 < h) (hc : 0 < c) :
    IsJet (quotientJet h) c := by
  have hgeom : IsJet (geometryJet h) c := isJet_geometric h c hh.ne'
  have ha := hgeom.scale (1 + h)
  have hb := hgeom.scale (1 + 2 * h)
  have hz := isJet_exponential (-(3 * (1 + h))) c
  have hv := (isJet_const 1 c).sub hz
  have he := isJet_exponential (-2) c
  have hu := isJet_exponential (-(1 + 3 * h)) c
  have hr : IsJet (radicandJet h) c :=
    ((isJet_const 1 c).sub (hz.mul ((isJet_const 1 c).add ha))).sub
      (((ha.mul hb).mul he).scale (1 / 2))
  have hrad (x : ℝ) : (radicandJet h x).value = rationalizedRadicand x h :=
    zeroCenterRadicandJet_value x h hh.ne'
  have hpos : 0 < (radicandJet h c).value := by
    rw [hrad]
    apply pos_of_mul_pos_right _ (Real.exp_pos ((3 + 6*h)*c)).le
    exact (by positivity : 0 < 27 * (1+h) * (1+2*h) * (1+3*h) * c^4 / 24).trans_le
      (rationalized_radicand_lower hc.le hh)
  have hA : 0 < (scale (1 + h) (geometryJet h c)).value := by
    change 0 < (1 + h) * zeroCenterGeometric c h
    unfold zeroCenterGeometric
    rw [ite_eq_right hh.ne']
    exact mul_pos (by positivity) (div_pos
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr
        (mul_neg_of_neg_of_pos (by linarith) hc))) hh)
  have hD : 0 < (add (zeroCenterV h (Real.exp (-(3 * (1 + h)) * c)))
      (sqrtFrom (radicandJet h c) (Real.sqrt (radicandJet h c).value))).value := by
    change 0 < (1 - Real.exp (-(3 * (1 + h)) * c)) + Real.sqrt (radicandJet h c).value
    exact add_pos_of_pos_of_nonneg
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) hc)))
      (Real.sqrt_nonneg _)
  have hN := (hb.scale (1 / 2)).add (hu.mul ((isJet_const 1 c).sub (hv.quot ha hA.ne')))
  have hQ := hN.quot (hv.add (hr.sqrtFrom hpos)) hD.ne'
  unfold quotientJet zeroCenterQuotientJet
  simp only [← hrad]
  exact hQ

private theorem profile_eq_quotient (p : ℕ) (hp : 0 < p) {c : ℝ} (hc : 0 < c) :
    zeroProfile p c = Real.exp (-c / 2) * (quotientJet (1 / (p : ℝ)) c).value := by
  rw [zeroProfile_eq_tail_formula hp hc]
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hh : (1 / (p : ℝ)) ≠ 0 := div_ne_zero one_ne_zero hp'
  simp only [quotientJet, zeroCenterQuotientJet, zeroCenterAB, zeroCenterV, zeroCenterGeometricJet,
    zeroCenterGeometric, ite_eq_right hh, quot, sqrtFrom, const, sub, add, scale, mul, exponential]
  congr 1
  rw [show (1 + 1 / (p : ℝ)) * ((1 - Real.exp (-3 * (1 / (p : ℝ)) * c)) / (1 / (p : ℝ))) =
      (p + 1 : ℝ) * (1 - Real.exp (-3 * (1 / (p : ℝ)) * c)) by field_simp,
    show (1 + 2 * (1 / (p : ℝ))) * ((1 - Real.exp (-3 * (1 / (p : ℝ)) * c)) / (1 / (p : ℝ))) =
      (p + 2 : ℝ) * (1 - Real.exp (-3 * (1 / (p : ℝ)) * c)) by field_simp]
  ring_nf

/-- The second derivative of the actual profile on positive gaps. -/
theorem zeroProfile_deriv2_eq_curvature {p : ℕ} (hp : 0 < p) {c : ℝ} (hc : 0 < c) :
    let h : ℝ := 1 / p
    deriv^[2] (zeroProfile p) c = Real.exp (-c / 2) *
      zeroCenterCurvature h (zeroCenterGeometric c h) (Real.exp (-3 * h * c))
        (Real.exp (-(3 * (1 + h)) * c)) (Real.exp (-2 * c))
        (Real.exp (-(1 + 3 * h) * c)) (Real.sqrt (rationalizedRadicand c h)) := by
  let h : ℝ := 1 / p
  let f (x : ℝ) := mul (exponential (-1 / 2) (Real.exp ((-1 / 2) * x))) (quotientJet h x)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hjet (x : ℝ) (hx : 0 < x) : IsJet f x :=
    (isJet_exponential _ x).mul (isJet_quotient h x hh hx)
  have hnhds : ∀ᶠ x : ℝ in 𝓝 c, 0 < x := lt_mem_nhds hc
  have hf : zeroProfile p =ᶠ[𝓝 c] (fun x ↦ (f x).value) := by
    filter_upwards [hnhds] with x hx
    rw [profile_eq_quotient p hp hx]
    change Real.exp (-x / 2) * (quotientJet h x).value =
      Real.exp ((-1 / 2) * x) * (quotientJet h x).value
    rw [show (-1 / 2 : ℝ) * x = -x / 2 by ring]
  have hf' : deriv (fun x ↦ (f x).value) =ᶠ[𝓝 c] (fun x ↦ (f x).first) := by
    filter_upwards [hnhds] with x hx
    exact (hjet x hx).1.deriv
  change deriv (deriv (zeroProfile p)) c = _
  rw [hf.deriv.deriv_eq, hf'.deriv_eq, (hjet c hc).2.deriv]
  change 2 * (f c).second = Real.exp (-c / 2) * _
  unfold zeroCenterCurvature
  change 2 * (f c).second = Real.exp (-c / 2) *
    (2 * (quotientJet h c).second - (quotientJet h c).first + (quotientJet h c).value / 4)
  simp only [f, mul, exponential, show (-1 / 2 : ℝ) * c = -c / 2 by ring]
  ring

#print axioms zeroProfile_deriv2_eq_curvature

/-- A third-order coefficient together with its value and first two coefficients. -/
structure CurvatureCubic (R : Type) where
  lower : CurvatureJet R
  third : R

namespace CurvatureCubic

variable {R : Type}

def const [Zero R] (a : R) : CurvatureCubic R := ⟨CurvatureJet.const a, 0⟩

def add [Add R] (a b : CurvatureCubic R) : CurvatureCubic R :=
  ⟨CurvatureJet.add a.lower b.lower, a.third + b.third⟩

def sub [Sub R] (a b : CurvatureCubic R) : CurvatureCubic R :=
  ⟨CurvatureJet.sub a.lower b.lower, a.third - b.third⟩

def scale [Mul R] (a : R) (b : CurvatureCubic R) : CurvatureCubic R :=
  ⟨CurvatureJet.scale a b.lower, a * b.third⟩

def mul [Add R] [Mul R] (a b : CurvatureCubic R) : CurvatureCubic R :=
  ⟨CurvatureJet.mul a.lower b.lower, a.lower.value * b.third + a.lower.first * b.lower.second +
    a.lower.second * b.lower.first + a.third * b.lower.value⟩

def quot [Add R] [Sub R] [Mul R] [Div R] (a b : CurvatureCubic R) : CurvatureCubic R :=
  let v := CurvatureJet.quot a.lower b.lower
  ⟨v, (a.third - (b.lower.first * v.second + b.lower.second * v.first +
      b.third * v.value)) / b.lower.value⟩

def root [OfNat R 2] [Sub R] [Mul R] [Div R] (a : CurvatureCubic R) (r : R) :
    CurvatureCubic R :=
  let v := CurvatureJet.sqrtFrom a.lower r
  ⟨v, (a.third - 2 * v.first * v.second) / (2 * r)⟩

def exp [OfNat R 2] [OfNat R 6] [Mul R] [Div R] (k e : R) : CurvatureCubic R :=
  ⟨CurvatureJet.exponential k e, k * k * k * e / 6⟩

private def IsCubic (f : ℝ → CurvatureCubic ℝ) (c : ℝ) : Prop :=
  CurvatureJet.IsJet (fun x ↦ (f x).lower) c ∧
    HasDerivAt (fun x ↦ (f x).lower.second) (3 * (f c).third) c

private theorem isCubic_const (a c : ℝ) : IsCubic (fun _ ↦ const a) c := by
  refine ⟨CurvatureJet.isJet_const a c, ?_⟩
  simpa [const, CurvatureJet.const] using hasDerivAt_const c (0 : ℝ)

private theorem IsCubic.add {f g : ℝ → CurvatureCubic ℝ} {c : ℝ}
    (hf : IsCubic f c) (hg : IsCubic g c) : IsCubic (fun x ↦ add (f x) (g x)) c := by
  refine ⟨hf.1.add hg.1, ?_⟩
  change HasDerivAt (fun x ↦ (f x).lower.second + (g x).lower.second)
    (3 * ((f c).third + (g c).third)) c
  rw [mul_add]
  exact hf.2.add hg.2

private theorem IsCubic.sub {f g : ℝ → CurvatureCubic ℝ} {c : ℝ}
    (hf : IsCubic f c) (hg : IsCubic g c) : IsCubic (fun x ↦ sub (f x) (g x)) c := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  change HasDerivAt (fun x ↦ (f x).lower.second - (g x).lower.second)
    (3 * ((f c).third - (g c).third)) c
  rw [mul_sub]
  exact hf.2.sub hg.2

private theorem IsCubic.scale {f : ℝ → CurvatureCubic ℝ} {c : ℝ}
    (hf : IsCubic f c) (a : ℝ) : IsCubic (fun x ↦ scale a (f x)) c := by
  refine ⟨hf.1.scale a, ?_⟩
  change HasDerivAt (fun x ↦ a * (f x).lower.second) (3 * (a * (f c).third)) c
  convert hf.2.const_mul a using 1 <;> ring

private theorem IsCubic.mul {f g : ℝ → CurvatureCubic ℝ} {c : ℝ}
    (hf : IsCubic f c) (hg : IsCubic g c) : IsCubic (fun x ↦ mul (f x) (g x)) c := by
  refine ⟨hf.1.mul hg.1, ?_⟩
  change HasDerivAt (fun x ↦ (f x).lower.value * (g x).lower.second +
      (f x).lower.first * (g x).lower.first + (f x).lower.second * (g x).lower.value) _ c
  convert ((hf.1.1.mul hg.2).add (hf.1.2.mul hg.1.2)).add (hf.2.mul hg.1.1) using 1
  simp only [CurvatureCubic.mul]
  ring

private theorem IsCubic.quot {f g : ℝ → CurvatureCubic ℝ} {c : ℝ}
    (hf : IsCubic f c) (hg : IsCubic g c) (hn : (g c).lower.value ≠ 0) :
    IsCubic (fun x ↦ quot (f x) (g x)) c := by
  let v (x : ℝ) := CurvatureJet.quot (f x).lower (g x).lower
  have hv : CurvatureJet.IsJet v c := hf.1.quot hg.1 hn
  refine ⟨hv, ?_⟩
  have hnum := hf.2.sub ((hg.1.2.mul hv.2).add (hg.2.mul hv.1))
  -- The first term here differentiates `g₁ * v₁`. Its derivative needs the
  -- derivative of the first component of each jet, supplied by `IsJet`.
  change HasDerivAt (fun x ↦ ((f x).lower.second -
      ((g x).lower.first * (v x).first + (g x).lower.second * (v x).value)) /
        (g x).lower.value) _ c
  change HasDerivAt (fun x ↦ (f x).lower.second -
      ((g x).lower.first * (v x).first + (g x).lower.second * (v x).value)) _ c at hnum
  convert hnum.div hg.1.1 hn using 1
  change 3 * (CurvatureCubic.quot (f c) (g c)).third = _
  simp only [CurvatureCubic.quot, v, CurvatureJet.quot]
  field_simp
  <;> ring

private theorem IsCubic.root {f : ℝ → CurvatureCubic ℝ} {c : ℝ}
    (hf : IsCubic f c) (hp : 0 < (f c).lower.value) :
    IsCubic (fun x ↦ root (f x) (Real.sqrt (f x).lower.value)) c := by
  let v (x : ℝ) := CurvatureJet.sqrtFrom (f x).lower (Real.sqrt (f x).lower.value)
  have hv : CurvatureJet.IsJet v c := hf.1.sqrtFrom hp
  refine ⟨hv, ?_⟩
  have hnum := hf.2.sub (hv.2.mul hv.2)
  have hden := hv.1.const_mul 2
  have h0 : (v c).value ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  change HasDerivAt (fun x ↦ ((f x).lower.second - (v x).first * (v x).first) /
    (2 * (v x).value)) _ c
  change HasDerivAt (fun x ↦ (f x).lower.second - (v x).first * (v x).first) _ c at hnum
  convert hnum.div hden (mul_ne_zero (by norm_num) h0) using 1
  simp only [CurvatureCubic.root, v, CurvatureJet.sqrtFrom]
  field_simp
  <;> ring

private theorem isCubic_exp (k c : ℝ) : IsCubic (fun x ↦ exp k (Real.exp (k * x))) c := by
  have he := CurvatureJet.isJet_exponential k c
  refine ⟨he, ?_⟩
  change HasDerivAt (fun x ↦ k*k*Real.exp (k*x)/2) (3 * (k*k*k*Real.exp (k*c)/6)) c
  convert (he.1.const_mul (k*k)).div_const 2 using 1
  · rfl
  · change _ = (k*k * (k * Real.exp (k*c))) / 2
    ring

end CurvatureCubic

def zeroCenterQuotientCubic {R : Type} [Zero R] [OfNat R 1] [OfNat R 2] [OfNat R 3]
    [OfNat R 6] [OfNat R 9] [Add R] [Sub R] [Neg R] [Mul R] [Div R]
    (h s q z e u root : R) : CurvatureCubic R :=
  let t : CurvatureCubic R := ⟨zeroCenterGeometricJet h s q, 9*h*h*q/2⟩
  let a := CurvatureCubic.scale (1+h) t
  let b := CurvatureCubic.scale (1+2*h) t
  let zj := CurvatureCubic.exp (-(3*(1+h))) z
  let v := (CurvatureCubic.const 1).sub zj
  let e₂ := CurvatureCubic.exp (-2) e
  let r := ((CurvatureCubic.const 1).sub (zj.mul ((CurvatureCubic.const 1).add a))).sub
    (CurvatureCubic.scale (1/2) ((a.mul b).mul e₂))
  let num := (CurvatureCubic.scale (1/2) b).add
    ((CurvatureCubic.exp (-(1+3*h)) u).mul ((CurvatureCubic.const 1).sub (v.quot a)))
  num.quot (v.add (r.root root))

/-- Gap derivative of the normalized curvature used by the fixed-degree mean-value bound. -/
def zeroCenterCurvatureSlope {R : Type} [Zero R] [OfNat R 1] [OfNat R 2] [OfNat R 3]
    [OfNat R 4] [OfNat R 6] [OfNat R 9] [Add R] [Sub R] [Neg R] [Mul R] [Div R]
    (h s q z e u root : R) : R :=
  let g := zeroCenterQuotientCubic h s q z e u root
  6 * g.third - 2 * g.lower.second + g.lower.first / 4

private theorem isCubic_geometric {h c : ℝ} (hh : h ≠ 0) :
    CurvatureCubic.IsCubic (fun x ↦ ⟨geometryJet h x, 9*h*h*Real.exp (-3*h*x)/2⟩) c := by
  refine ⟨isJet_geometric h c hh, ?_⟩
  have he : HasDerivAt (fun x ↦ Real.exp (-3*h*x))
      (-3*h*Real.exp (-3*h*c)) c := (CurvatureJet.isJet_exponential (-3*h) c).1
  change HasDerivAt (fun x ↦ -(9*h*Real.exp (-3*h*x))/2)
    (3 * (9*h*h*Real.exp (-3*h*c)/2)) c
  convert (he.const_mul (-9*h)).div_const 2 using 1
  · funext x
    change -(9*h*Real.exp (-3*h*x))/2 = ((-9*h)*Real.exp (-3*h*x))/2
    ring
  · ring

private theorem isCubic_quotient {h c : ℝ} (hh : 0 < h) (hc : 0 < c) :
    CurvatureCubic.IsCubic
      (fun x ↦ zeroCenterQuotientCubic h (zeroCenterGeometric x h) (Real.exp (-3*h*x))
        (Real.exp (-(3*(1+h))*x)) (Real.exp (-2*x)) (Real.exp (-(1+3*h)*x))
        (Real.sqrt (rationalizedRadicand x h))) c := by
  have ht := isCubic_geometric (c := c) hh.ne'
  have ha := ht.scale (1+h)
  have hb := ht.scale (1+2*h)
  have hz := CurvatureCubic.isCubic_exp (-(3*(1+h))) c
  have hv := (CurvatureCubic.isCubic_const 1 c).sub hz
  have he := CurvatureCubic.isCubic_exp (-2) c
  have hu := CurvatureCubic.isCubic_exp (-(1+3*h)) c
  have hr := ((CurvatureCubic.isCubic_const 1 c).sub
      (hz.mul ((CurvatureCubic.isCubic_const 1 c).add ha))).sub
    (((ha.mul hb).mul he).scale (1/2))
  have hrad (x : ℝ) : (radicandJet h x).value = rationalizedRadicand x h :=
    zeroCenterRadicandJet_value x h hh.ne'
  have hrpos : 0 < (radicandJet h c).value := by
    rw [hrad]
    apply pos_of_mul_pos_right _ (Real.exp_pos ((3+6*h)*c)).le
    exact (by positivity : 0 < 27 * (1+h) * (1+2*h) * (1+3*h) * c^4 / 24).trans_le
      (rationalized_radicand_lower hc.le hh)
  have hA : 0 < (1+h) * zeroCenterGeometric c h := by
    unfold zeroCenterGeometric
    rw [ite_eq_right hh.ne']
    exact mul_pos (by positivity) (div_pos
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr
        (mul_neg_of_neg_of_pos (by linarith) hc))) hh)
  have hD : 0 < (1 - Real.exp (-(3*(1+h))*c)) + Real.sqrt (radicandJet h c).value :=
    add_pos_of_pos_of_nonneg
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) hc)))
      (Real.sqrt_nonneg _)
  have hN := (hb.scale (1/2)).add
    (hu.mul ((CurvatureCubic.isCubic_const 1 c).sub (hv.quot ha hA.ne')))
  have hQ := hN.quot (hv.add (hr.root hrpos)) hD.ne'
  unfold zeroCenterQuotientCubic
  simp only [← hrad]
  exact hQ

/-- The exact derivative of the normalized curvature on the positive gap axis. -/
theorem hasDerivAt_zeroCenterCurvature {h c : ℝ} (hh : 0 < h) (hc : 0 < c) :
    HasDerivAt (fun x ↦ zeroCenterCurvature h (zeroCenterGeometric x h) (Real.exp (-3*h*x))
      (Real.exp (-(3*(1+h))*x)) (Real.exp (-2*x)) (Real.exp (-(1+3*h)*x))
      (Real.sqrt (rationalizedRadicand x h)))
      (zeroCenterCurvatureSlope h (zeroCenterGeometric c h) (Real.exp (-3*h*c))
      (Real.exp (-(3*(1+h))*c)) (Real.exp (-2*c)) (Real.exp (-(1+3*h)*c))
      (Real.sqrt (rationalizedRadicand c h))) c := by
  let g (x : ℝ) := zeroCenterQuotientCubic h (zeroCenterGeometric x h) (Real.exp (-3*h*x))
    (Real.exp (-(3*(1+h))*x)) (Real.exp (-2*x)) (Real.exp (-(1+3*h)*x))
    (Real.sqrt (rationalizedRadicand x h))
  have hj : CurvatureCubic.IsCubic g c := isCubic_quotient hh hc
  change HasDerivAt (fun x ↦ 2*(g x).lower.second - (g x).lower.first + (g x).lower.value/4)
    (6*(g c).third - 2*(g c).lower.second + (g c).lower.first/4) c
  have hd := ((hj.2.const_mul 2).sub hj.1.2).add (hj.1.1.div_const 4)
  change HasDerivAt
    (fun x ↦ 2*(g x).lower.second - (g x).lower.first + (g x).lower.value/4)
    (2*(3*(g c).third) - 2*(g c).lower.second + (g c).lower.first/4) c at hd
  convert hd using 1
  ring

#print axioms hasDerivAt_zeroCenterCurvature


/-- The normalized curvature at fixed reciprocal degree. -/
def zeroCenterCurvatureAt (h c : ℝ) : ℝ :=
  zeroCenterCurvature h (zeroCenterGeometric c h) (Real.exp (-3*h*c))
    (Real.exp (-(3*(1+h))*c)) (Real.exp (-2*c)) (Real.exp (-(1+3*h)*c))
    (Real.sqrt (rationalizedRadicand c h))

/-- The gap derivative of the normalized curvature at fixed reciprocal degree. -/
def zeroCenterCurvatureSlopeAt (h c : ℝ) : ℝ :=
  zeroCenterCurvatureSlope h (zeroCenterGeometric c h) (Real.exp (-3*h*c))
    (Real.exp (-(3*(1+h))*c)) (Real.exp (-2*c)) (Real.exp (-(1+3*h)*c))
    (Real.sqrt (rationalizedRadicand c h))

/-- A lower bound at the center and an absolute slope bound over the interval
give a lower bound for the normalized curvature at every gap in the interval. -/
theorem zeroCenterCurvatureAt_pos_of_slope {h a b x L M : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hx : x ∈ Icc a b)
    (hL : L ≤ zeroCenterCurvatureAt h ((a+b)/2)) (hM : 0 ≤ M)
    (hs : ∀ c ∈ Icc a b, |zeroCenterCurvatureSlopeAt h c| ≤ M)
    (hsep : M * ((b-a)/2) < L) :
    0 < zeroCenterCurvatureAt h x := by
  let m := (a+b)/2
  have hab : a ≤ b := hx.1.trans hx.2
  have hm : m ∈ Icc a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hd (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivWithinAt (zeroCenterCurvatureAt h) (zeroCenterCurvatureSlopeAt h y) (Icc a b) y :=
    (hasDerivAt_zeroCenterCurvature hh (ha.trans_le hy.1)).hasDerivWithinAt
  have hbound := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hd
    (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hs y hy) hm hx
  simp only [Real.norm_eq_abs] at hbound
  have hdist : |x-m| ≤ (b-a)/2 := abs_le.mpr ⟨by dsimp [m]; linarith [hx.1],
    by dsimp [m]; linarith [hx.2]⟩
  have hout := hbound.trans (mul_le_mul_of_nonneg_left hdist hM)
  linarith [(abs_le.mp hout).1]

#print axioms zeroCenterCurvatureAt_pos_of_slope

end
end RefinedBMV.FourSpectrumLift
