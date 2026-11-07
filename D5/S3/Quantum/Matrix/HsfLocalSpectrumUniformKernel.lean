/- GID: D5/S3/Quantum/Matrix/HsfLocalSpectrumUniformKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfLocalSpectrumUniformKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: Uniform scalar spectral kernel and cyclic residual bounds. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Matrix.HsfLocalSpectrumCoefficients

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier

variable {n : Type*} [Fintype n] [DecidableEq n]

open private spectralDen_pos spectralTau_gap spectralTau_bounds
  from D5.S3.Quantum.Matrix.HsfLocalSpectrumCoefficients

section Uniform
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

private theorem spectralDen_comm (a b : ℝ) : spectralDen a b = spectralDen b a := by
  unfold spectralDen; ring

private theorem spectralTau_comm (a b : ℝ) : spectralTau a b = spectralTau b a := by
  unfold spectralTau
  rw [mul_comm a b, add_comm a b, spectralDen_comm a b]

private def spectralRho (a b : ℝ) : ℝ := Real.sqrt (1-spectralTau a b^2)

private theorem spectralRho_nonneg (a b : ℝ) : 0 ≤ spectralRho a b :=
  Real.sqrt_nonneg _

private theorem spectralRho_comm (a b : ℝ) : spectralRho a b = spectralRho b a := by
  unfold spectralRho; rw [spectralTau_comm a b]

private theorem spectralRho_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    spectralRho a b^2 = 1-spectralTau a b^2 := by
  have ht := spectralTau_bounds ha hb
  have hs : spectralTau a b^2 ≤ 1 := by
    simpa only [one_pow] using
      (sq_le_sq₀ ht.1.le (by norm_num : (0 : ℝ) ≤ 1)).mpr ht.2
  exact Real.sq_sqrt (sub_nonneg.mpr hs)

private def gramPolynomial (a b c : ℝ) : ℝ :=
  4*a^4*b^2+7*a^4*b*c+4*a^4*c^2+7*a^3*b^3+26*a^3*b^2*c+
  26*a^3*b*c^2+7*a^3*c^3+4*a^2*b^4+26*a^2*b^3*c+48*a^2*b^2*c^2+
  26*a^2*b*c^3+4*a^2*c^4+7*a*b^4*c+26*a*b^3*c^2+26*a*b^2*c^3+
  7*a*b*c^4+4*b^4*c^2+7*b^3*c^3+4*b^2*c^4

private theorem spectralTau_gram {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ 1-spectralTau a b^2-spectralTau b c^2-spectralTau a c^2+
      2*spectralTau a b*spectralTau b c*spectralTau a c := by
  have hd := (spectralDen_pos ha hb).ne'
  have he := (spectralDen_pos hb hc).ne'
  have hf := (spectralDen_pos ha hc).ne'
  have hs₁ := Real.sq_sqrt ha.le
  have hs₂ := Real.sq_sqrt hb.le
  have hs₃ := Real.sq_sqrt hc.le
  have hid : 1-spectralTau a b^2-spectralTau b c^2-spectralTau a c^2+
      2*spectralTau a b*spectralTau b c*spectralTau a c =
      (a-b)^2*(a-c)^2*(b-c)^2*gramPolynomial a b c /
        (4*(spectralDen a b)^2*(spectralDen a c)^2*(spectralDen b c)^2) := by
    unfold spectralTau
    rw [Real.sqrt_mul ha.le, Real.sqrt_mul hb.le, Real.sqrt_mul ha.le]
    field_simp [hd, he, hf]
    ring_nf
    rw [hs₁, hs₂, hs₃]
    unfold spectralDen gramPolynomial
    ring
  rw [hid]
  unfold gramPolynomial
  positivity

private theorem spectralRho_triangle {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    spectralRho a c ≤ spectralRho a b+spectralRho b c := by
  let u := spectralTau a b
  let v := spectralTau b c
  let w := spectralTau a c
  let x := spectralRho a b
  let y := spectralRho b c
  let z := spectralRho a c
  have hu := spectralTau_bounds ha hb
  have hv := spectralTau_bounds hb hc
  have hw := spectralTau_bounds ha hc
  have hx : 0 ≤ x := spectralRho_nonneg _ _
  have hy : 0 ≤ y := spectralRho_nonneg _ _
  have hz : 0 ≤ z := spectralRho_nonneg _ _
  have hx₂ : x^2 = 1-u^2 := spectralRho_sq ha hb
  have hy₂ : y^2 = 1-v^2 := spectralRho_sq hb hc
  have hz₂ : z^2 = 1-w^2 := spectralRho_sq ha hc
  have hg := spectralTau_gram ha hb hc
  change 0 ≤ 1-u^2-v^2-w^2+2*u*v*w at hg
  change z ≤ x+y
  have hxy : 0 ≤ x*y := mul_nonneg hx hy
  by_cases h : u^2+v^2 ≤ 1
  · apply (sq_le_sq₀ hz (add_nonneg hx hy)).mp
    nlinarith only [hx₂, hy₂, hz₂, h, hxy, sq_nonneg w]
  · have huv : x*y ≤ u*v := by
      have hid : (u*v)^2-(x*y)^2 = u^2+v^2-1 := by rw [mul_pow, mul_pow, hx₂, hy₂]; ring
      have hp : 0 ≤ u*v := mul_nonneg hu.1.le hv.1.le
      apply (sq_le_sq₀ hxy hp).mp
      nlinarith only [hid, h]
    have hsq : (w-u*v)^2 ≤ (x*y)^2 := by rw [mul_pow, hx₂, hy₂]; nlinarith only [hg]
    have hwlow : u*v-x*y ≤ w := by
      have habs : |w-u*v| ≤ x*y := (sq_le_sq₀ (abs_nonneg _) hxy).mp (by simpa using hsq)
      linarith only [(abs_le.mp habs).1]
    have hlow : 0 ≤ u*v-x*y := sub_nonneg.mpr huv
    have hbound : (u*v-x*y)^2 ≤ w^2 :=
      (sq_le_sq₀ hlow hw.1.le).mpr hwlow
    have hid : 1-(u*v-x*y)^2 = (u*y+v*x)^2 := by
      have heq : (u*v-x*y)^2+(u*y+v*x)^2 = 1 := by
        calc
          _ = (u^2+x^2)*(v^2+y^2) := by ring
          _ = 1 := by rw [hx₂, hy₂]; ring
      linarith only [heq]
    have hnonneg : 0 ≤ u*y+v*x := add_nonneg (mul_nonneg hu.1.le hy) (mul_nonneg hv.1.le hx)
    have hzbound : z ≤ u*y+v*x := by
      apply (sq_le_sq₀ hz hnonneg).mp
      linarith only [hz₂, hbound, hid]
    have hu' : u*y ≤ y := by nlinarith [mul_le_mul_of_nonneg_right hu.2 hy]
    have hv' : v*x ≤ x := by nlinarith [mul_le_mul_of_nonneg_right hv.2 hx]
    linarith

private def cyclicPolynomial (a b c : ℝ) : ℝ :=
  a^2*b^2*(a+b)*(4*a^2+5*a*b+4*b^2)+
  a*b*c*(4*(a^4+b^4)+4*a*b*(a^2+b^2)+2*a^2*b^2)+
  14*a*b*c^2*(a+b)*spectralDen a b+a^2*b^2*c^3+3*(a^3+b^3)*c^4

private def cyclicResidual (a b c : ℝ) : ℝ :=
  let U := a^2+b^2
  let V := a*b
  let s := a+b
  let R := 4*U+7*V
  R*V^4+4*V^4*s*c+V^2*(4*U^2+29*U*V+40*V^2)*c^2+
  2*V*s*U*(4*U+V)*c^3+(4*U^3+23*U^2*V+56*U*V^2+47*V^3)*c^4+
  2*s*(4*U^2+12*U*V+17*V^2)*c^5+R*(3*U+4*V)*c^6+2*R*s*c^7+R*c^8

private theorem cyclicResidual_identity (a b c : ℝ) :
    (4*a^2+7*a*b+4*b^2)*(spectralDen a c)^2*(spectralDen b c)^2-
      2*a*b*c*cyclicPolynomial a b c = cyclicResidual a b c := by
  unfold cyclicResidual cyclicPolynomial spectralDen
  ring

private def cyclicGamma (a b c : ℝ) : ℝ :=
  spectralTau a b*spectralKernel a b c+
  spectralTau b c*spectralKernel b c a+
  spectralTau c a*spectralKernel c a b-
  spectralTau a b*spectralTau b c*spectralTau c a/3

private theorem cyclicGamma_bounds {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ cyclicGamma a b c ∧ cyclicGamma a b c ≤
      (3/4)*(spectralRho a b^2+spectralRho b c^2+spectralRho c a^2) := by
  have hd := (spectralDen_pos ha hb).ne'
  have he := (spectralDen_pos hb hc).ne'
  have hf := (spectralDen_pos hc ha).ne'
  have hd' := (spectralDen_pos hb ha).ne'
  have he' := (spectralDen_pos hc hb).ne'
  have hf' := (spectralDen_pos ha hc).ne'
  have hs₁ := Real.sq_sqrt ha.le
  have hs₂ := Real.sq_sqrt hb.le
  have hs₃ := Real.sq_sqrt hc.le
  let denomProduct := spectralDen a b*spectralDen b c*spectralDen c a
  have hdenomProduct : 0 < denomProduct := mul_pos (mul_pos (spectralDen_pos ha hb) (spectralDen_pos hb hc))
    (spectralDen_pos hc ha)
  have hformula : cyclicGamma a b c = 3*a*b*c/(8*denomProduct^2)*
      ((a-b)^2*cyclicPolynomial a b c+(b-c)^2*cyclicPolynomial b c a+
        (c-a)^2*cyclicPolynomial c a b) := by
    unfold cyclicGamma spectralTau spectralKernel denomProduct
    simp only [Real.sqrt_mul ha.le, Real.sqrt_mul hb.le, Real.sqrt_mul hc.le,
      show spectralDen b a = spectralDen a b from spectralDen_comm _ _,
      show spectralDen c b = spectralDen b c from spectralDen_comm _ _,
      show spectralDen a c = spectralDen c a from spectralDen_comm _ _]
    field_simp [hd, he, hf, hd', he', hf']
    ring_nf
    rw [hs₁, hs₂, hs₃]
    unfold cyclicPolynomial spectralDen
    ring
  have hres : (3/4)*(spectralRho a b^2+spectralRho b c^2+spectralRho c a^2)-
      cyclicGamma a b c = 3/(16*denomProduct^2)*
      ((a-b)^2*cyclicResidual a b c+(b-c)^2*cyclicResidual b c a+
        (c-a)^2*cyclicResidual c a b) := by
    rw [spectralRho_sq ha hb, spectralRho_sq hb hc, spectralRho_sq hc ha,
      spectralTau_gap ha hb, spectralTau_gap hb hc, spectralTau_gap hc ha, hformula]
    rw [← cyclicResidual_identity, ← cyclicResidual_identity, ← cyclicResidual_identity]
    dsimp only [denomProduct]
    field_simp [hd, he, hf, hd', he', hf']
    unfold spectralDen
    ring
  constructor
  · rw [hformula]
    unfold cyclicPolynomial spectralDen
    positivity
  · have hnonneg : 0 ≤ (3/4)*(spectralRho a b^2+spectralRho b c^2+spectralRho c a^2)-
        cyclicGamma a b c := by
      rw [hres]
      unfold cyclicResidual
      positivity
    linarith

private theorem spectralRho_distance {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a-b| ≤ spectralRho a b*(a+b) := by
  have hd : 0 < 4*(spectralDen a b)^2 := by have := spectralDen_pos ha hb; positivity
  have hgap := spectralRho_sq ha hb
  rw [spectralTau_gap ha hb] at hgap
  have hm := (eq_div_iff hd.ne').mp hgap
  have hp : 0 ≤ (a-b)^2*((a+b)^2*(4*a^2+7*a*b+4*b^2)-4*(spectralDen a b)^2) := by
    rw [show (a+b)^2*(4*a^2+7*a*b+4*b^2)-4*(spectralDen a b)^2 =
      a*b*(7*a^2+10*a*b+7*b^2) by unfold spectralDen; ring]
    positivity
  have hid : (spectralRho a b^2*(a+b)^2-(a-b)^2)*(4*(spectralDen a b)^2) =
      (a-b)^2*((a+b)^2*(4*a^2+7*a*b+4*b^2)-4*(spectralDen a b)^2) := by
    linear_combination (a+b)^2*hm
  have hs : (a-b)^2 ≤ spectralRho a b^2*(a+b)^2 := by
    have hscaled : 0 ≤ (spectralRho a b^2*(a+b)^2-(a-b)^2)*
        (4*(spectralDen a b)^2) := by
      rw [hid]
      exact hp
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hscaled hd)
  have hn := mul_nonneg (spectralRho_nonneg a b) (add_pos ha hb).le
  apply (sq_le_sq₀ (abs_nonneg _) hn).mp
  simpa only [sq_abs, mul_pow] using hs

private def linearPolynomial (a b c : ℝ) : ℝ :=
  a^2*b+a*b^2/2+a^2*c+(7/2)*a*b*c+2*a*c^2+2*b*c^2

private theorem defect_kernel_uniform {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    |3*spectralKernel a b c-spectralTau a c*spectralTau c b/3| ≤
      (16/9)*(spectralRho a c+spectralRho c b) := by
  let denomProduct := spectralDen a b*spectralDen a c*spectralDen b c
  let W := (a+b)*(a+c)*(b+c)
  let f := 3*c*Real.sqrt (a*b)/(4*denomProduct)
  have hd := spectralDen_pos ha hb
  have he := spectralDen_pos ha hc
  have hf := spectralDen_pos hb hc
  have hf' := spectralDen_pos hc hb
  have hdenomProduct : 0 < denomProduct := mul_pos (mul_pos hd he) hf
  have hW : 0 < W := mul_pos (mul_pos (add_pos ha hb) (add_pos ha hc)) (add_pos hb hc)
  have hfn : 0 ≤ f := by dsimp [f]; positivity
  have hpoly (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      0 ≤ linearPolynomial a b c ∧ linearPolynomial a b c ≤ 2*((a+b)*(a+c)*(b+c)) := by
    constructor
    · unfold linearPolynomial; positivity
    · have hp : 0 ≤ a^2*b+(3/2)*a*b^2+a^2*c+(1/2)*a*b*c+2*b^2*c := by positivity
      unfold linearPolynomial
      linarith only [hp, show 2*((a+b)*(a+c)*(b+c))-
        (a^2*b+a*b^2/2+a^2*c+(7/2)*a*b*c+2*a*c^2+2*b*c^2) =
        a^2*b+(3/2)*a*b^2+a^2*c+(1/2)*a*b*c+2*b^2*c by ring]
  have hB := hpoly a b c ha hb hc
  have hB' := hpoly b a c hb ha hc
  have hid : 3*spectralKernel a b c-spectralTau a c*spectralTau c b/3 =
      f*((c-a)*linearPolynomial a b c+(c-b)*linearPolynomial b a c) := by
    unfold spectralKernel spectralTau f denomProduct
    simp only [Real.sqrt_mul ha.le, Real.sqrt_mul hc.le,
      show spectralDen c b = spectralDen b c from spectralDen_comm _ _]
    have hs := Real.sq_sqrt hc.le
    field_simp [hd.ne', he.ne', hf.ne', hf'.ne']
    ring_nf
    rw [hs]
    unfold spectralDen linearPolynomial
    ring
  have hq (u v : ℝ) : (3/4)*(u+v)^2 ≤ spectralDen u v := by
    unfold spectralDen; nlinarith [sq_nonneg (u-v)]
  have hprod : (27/64)*W^2 ≤ denomProduct := by
    have h := mul_le_mul (mul_le_mul (hq a b) (hq a c)
      (by positivity : 0 ≤ (3/4)*(a+c)^2) hd.le) (hq b c)
      (by positivity : 0 ≤ (3/4)*(b+c)^2) (mul_nonneg hd.le he.le)
    dsimp [W, denomProduct]
    nlinarith only [h]
  have hsqrt : 2*Real.sqrt (a*b) ≤ a+b := by
    have hs := Real.sq_sqrt (mul_pos ha hb).le
    have hn := Real.sqrt_nonneg (a*b)
    apply (sq_le_sq₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn) (add_pos ha hb).le).mp
    nlinarith only [hs, sq_nonneg (a-b)]
  have hfW : f*(2*W)*(a+c) ≤ 16/9 ∧ f*(2*W)*(b+c) ≤ 16/9 := by
    have hf₁ : f*(2*W) ≤ (16/9)*(a+b)*c/W := by
      dsimp only [f]
      apply (le_div_iff₀ hW).mpr
      have hid : 3*c*Real.sqrt (a*b)/(4*denomProduct)*(2*W)*W =
          (3/2)*c*Real.sqrt (a*b)*W^2/denomProduct := by
        field_simp [hdenomProduct.ne'] <;> ring
      rw [hid]
      apply (div_le_iff₀ hdenomProduct).mpr
      have h₁ := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ (3/4)*c*W^2)
      have h₂ := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (16/9)*(a+b)*c)
      nlinarith only [h₁, h₂]
    constructor
    · have h := mul_le_mul_of_nonneg_right hf₁ (add_pos ha hc).le
      have hid : ((16/9)*(a+b)*c/W)*(a+c) = (16/9)*c/(b+c) := by
        dsimp only [W]
        field_simp [(add_pos ha hb).ne', (add_pos ha hc).ne', (add_pos hb hc).ne']
      rw [hid] at h
      exact h.trans ((div_le_iff₀ (add_pos hb hc)).mpr (by linarith))
    · have h := mul_le_mul_of_nonneg_right hf₁ (add_pos hb hc).le
      have hid : ((16/9)*(a+b)*c/W)*(b+c) = (16/9)*c/(a+c) := by
        dsimp only [W]
        field_simp [(add_pos ha hb).ne', (add_pos ha hc).ne', (add_pos hb hc).ne']
      rw [hid] at h
      exact h.trans ((div_le_iff₀ (add_pos ha hc)).mpr (by linarith))
  have hd₁ := spectralRho_distance ha hc
  have hd₂ := spectralRho_distance hb hc
  rw [hid, abs_mul, abs_of_nonneg hfn]
  calc
    _ ≤ f*(|c-a| *linearPolynomial a b c+|c-b| *linearPolynomial b a c) := by
      apply mul_le_mul_of_nonneg_left _ hfn
      simpa only [abs_mul, abs_of_nonneg hB.1, abs_of_nonneg hB'.1] using
        abs_add_le ((c-a)*linearPolynomial a b c) ((c-b)*linearPolynomial b a c)
    _ ≤ f*(2*W)*(|a-c|+|b-c|) := by
      rw [abs_sub_comm c a, abs_sub_comm c b]
      have hB'' : linearPolynomial b a c ≤ 2*W := by dsimp [W]; nlinarith only [hB'.2]
      have h₁ := mul_le_mul_of_nonneg_left hB.2 (abs_nonneg (a-c))
      have h₂ := mul_le_mul_of_nonneg_left hB'' (abs_nonneg (b-c))
      nlinarith only [mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hfn]
    _ ≤ f*(2*W)*(spectralRho a c*(a+c)+spectralRho b c*(b+c)) :=
      mul_le_mul_of_nonneg_left (add_le_add hd₁ hd₂) (mul_nonneg hfn (by positivity))
    _ ≤ (16/9)*(spectralRho a c+spectralRho c b) := by
      rw [spectralRho_comm c b]
      have h₁ := mul_le_mul_of_nonneg_right hfW.1 (spectralRho_nonneg a c)
      have h₂ := mul_le_mul_of_nonneg_right hfW.2 (spectralRho_nonneg b c)
      nlinarith only [h₁, h₂]



end Uniform

end D5.S3.Quantum.Matrix.HsfLocalSpectrumSupplier
