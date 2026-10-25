import Mathlib.Analysis.Calculus.Deriv.Inv
import D5.S3.Geometry.Hyperideal.CFMPTriangleDivergence435Transient

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped MeasureTheory Interval

namespace CFMPPlaneMomentDivergence435Transient
open CFMPSimplexDirection435Transient CFMPTriangleDivergence435Transient

-- Gram entry order: 00, 01, 02, 11, 12, 22.
def Q (g : Fin 6 → ℝ) (z : ℝ × ℝ) : ℝ :=
  -(g 0+2*g 1*z.1+2*g 2*z.2+g 3*z.1^2+2*g 4*z.1*z.2+g 5*z.2^2)

def moment (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (z : ℝ × ℝ) : ℝ :=
  a 0*(g 0+g 1*z.1+g 2*z.2)+
    a 1*(g 1+g 3*z.1+g 4*z.2)+a 2*(g 2+g 4*z.1+g 5*z.2)

def Qx (g : Fin 6 → ℝ) (z : ℝ × ℝ) : ℝ :=
  -(2*g 1+2*g 3*z.1+2*g 4*z.2)

def Qy (g : Fin 6 → ℝ) (z : ℝ × ℝ) : ℝ :=
  -(2*g 2+2*g 4*z.1+2*g 5*z.2)

def fluxX (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (C : ℝ) (z : ℝ × ℝ) : ℝ :=
  C*(a 1-a 0*z.1)/Q g z

def fluxY (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (C : ℝ) (z : ℝ × ℝ) : ℝ :=
  C*(a 2-a 0*z.2)/Q g z

def derivX (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (C : ℝ) (z : ℝ × ℝ) : ℝ :=
  ((-C*a 0)*Q g z-(C*(a 1-a 0*z.1))*Qx g z)/(Q g z)^2

def derivY (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (C : ℝ) (z : ℝ × ℝ) : ℝ :=
  ((-C*a 0)*Q g z-(C*(a 2-a 0*z.2))*Qy g z)/(Q g z)^2

theorem Q_hasDerivAt_x (g : Fin 6 → ℝ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => Q g (t,y)) (Qx g (x,y)) x := by
  have h := (((((hasDerivAt_const x (g 0)).add
    ((hasDerivAt_id x).const_mul (2*g 1))).add
    (hasDerivAt_const x (2*g 2*y))).add
    (((hasDerivAt_id x).pow 2).const_mul (g 3))).add
    ((hasDerivAt_id x).const_mul (2*g 4*y))).add
    (hasDerivAt_const x (g 5*y^2))
  convert h.neg using 1 <;> (try funext t) <;> dsimp [Q, Qx] <;> ring

theorem Q_hasDerivAt_y (g : Fin 6 → ℝ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => Q g (x,t)) (Qy g (x,y)) y := by
  have h := (((((hasDerivAt_const y (g 0)).add
    (hasDerivAt_const y (2*g 1*x))).add
    ((hasDerivAt_id y).const_mul (2*g 2))).add
    (hasDerivAt_const y (g 3*x^2))).add
    ((hasDerivAt_id y).const_mul (2*g 4*x))).add
    (((hasDerivAt_id y).pow 2).const_mul (g 5))
  convert h.neg using 1 <;> (try funext t) <;> dsimp [Q, Qy] <;> ring

theorem flux_hasDerivAt_x (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (C x y : ℝ)
    (hq : Q g (x,y) ≠ 0) :
    HasDerivAt (fun t : ℝ => fluxX g a C (t,y)) (derivX g a C (x,y)) x := by
  have hn := ((hasDerivAt_const x (a 1)).sub
    ((hasDerivAt_id x).const_mul (a 0))).const_mul C
  convert hn.div (Q_hasDerivAt_x g x y) hq using 1 <;> (try funext t) <;> dsimp [fluxX, derivX] <;> ring

theorem flux_hasDerivAt_y (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (C x y : ℝ)
    (hq : Q g (x,y) ≠ 0) :
    HasDerivAt (fun t : ℝ => fluxY g a C (x,t)) (derivY g a C (x,y)) y := by
  have hn := ((hasDerivAt_const y (a 2)).sub
    ((hasDerivAt_id y).const_mul (a 0))).const_mul C
  convert hn.div (Q_hasDerivAt_y g x y) hq using 1 <;> (try funext t) <;> dsimp [fluxY, derivY] <;> ring

theorem divergence_moment (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (C : ℝ)
    (z : ℝ × ℝ) (hq : Q g z ≠ 0) :
    derivX g a C z+derivY g a C z = 2*C*moment g a z/(Q g z)^2 := by
  dsimp only [derivX,derivY]
  field_simp [hq]
  dsimp [Q,Qx,Qy,moment]
  ring

-- This is a coordinate integral identity; identifying native edge traces is separate.
theorem triangle_moment (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (C : ℝ)
    (hq : ∀ z ∈ triangle 1, Q g z ≠ 0) :
    (∫ z in triangle 1, 2*C*moment g a z/(Q g z)^2) =
      (∫ r in (0 : ℝ)..1, fluxX g a C (1-r,r)-fluxX g a C (0,r)) +
      (∫ r in (0 : ℝ)..1, fluxY g a C (r,1-r)-fluxY g a C (r,0)) := by
  have hQ : Continuous (Q g) := by unfold Q;fun_prop
  have hP₀ : ContinuousOn (fluxX g a C) (triangle 1) := by
    unfold fluxX
    exact (by fun_prop : Continuous (fun z : ℝ × ℝ => C*(a 1-a 0*z.1))).continuousOn.div
      hQ.continuousOn hq
  have hP₁ : ContinuousOn (fluxY g a C) (triangle 1) := by
    unfold fluxY
    exact (by fun_prop : Continuous (fun z : ℝ × ℝ => C*(a 2-a 0*z.2))).continuousOn.div
      hQ.continuousOn hq
  have hD₀ : ContinuousOn (derivX g a C) (triangle 1) := by
    unfold derivX
    apply ContinuousOn.div (by unfold Q Qx;fun_prop) (hQ.pow 2).continuousOn
    intro z hz
    exact pow_ne_zero 2 (hq z hz)
  have hD₁ : ContinuousOn (derivY g a C) (triangle 1) := by
    unfold derivY
    apply ContinuousOn.div (by unfold Q Qy;fun_prop) (hQ.pow 2).continuousOn
    intro z hz
    exact pow_ne_zero 2 (hq z hz)
  calc
    _ = ∫ z in triangle 1, derivX g a C z+derivY g a C z := by
      apply setIntegral_congr_fun (triangle_compact 1).measurableSet
      intro z hz
      exact (divergence_moment g a C z (hq z hz)).symm
    _ = _ := triangle_divergence 1 (by norm_num) _ _ _ _ hP₀ hP₁ hD₀ hD₁
      (by
        intro y hy x hx
        exact flux_hasDerivAt_x g a C x y (hq (x,y) ⟨hx.1.le,hy.1.le,by linarith [hx.2]⟩))
      (by
        intro x hx y hy
        exact flux_hasDerivAt_y g a C x y (hq (x,y) ⟨hx.1.le,hy.1.le,by linarith [hy.2]⟩))

end CFMPPlaneMomentDivergence435Transient

#print axioms CFMPPlaneMomentDivergence435Transient.triangle_moment
run_cmd do
  let name := ``CFMPPlaneMomentDivergence435Transient.triangle_moment
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP223 target absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP223 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP223 CHECKED CFMPPlaneMomentDivergence435Transient.triangle_moment axioms={axioms}"
