/- GID: D5/S3/Analytic/AbelRatioSchwarzian
   generality: G
   mirror-B: D5/B/S3/Analytic/AbelRatioSchwarzian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.Mul, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Inv]
   utility: none
   digest: Actual second and third derivatives and Schwarzian from a second-order ODE and Abel ratio data. -/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The classical ODE-to-Schwarzian inference, with only two derivatives of
the denominator solution and one derivative of the Abel factor. All identities
used for differentiation hold on neighborhoods inside the given open set.
No derivative of the ODE coefficient q is needed. -/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace D5.S3.Analytic.AbelRatioSchwarzian

/-- The quotient of the actual second and first derivatives. -/
def preSchwarzian (t : ℂ → ℂ) (x : ℂ) : ℂ := deriv (deriv t) x / deriv t x

/-- The classical Schwarzian, using actual derivatives throughout. -/
def schwarzian (t : ℂ → ℂ) (x : ℂ) : ℂ :=
  deriv (deriv (deriv t)) x / deriv t x - (3 / 2 : ℂ) * preSchwarzian t x ^ 2

/-- An Abel ratio with a nonvanishing ODE solution has three actual derivatives.
The conclusion includes the second and third derivative formulas, rather than
assuming their existence. -/
theorem abel_ratio_schwarzian (U : Set ℂ) (hU : IsOpen U)
    (y p q W t : ℂ → ℂ)
    (hy : ∀ x ∈ U, DifferentiableAt ℂ y x ∧ DifferentiableAt ℂ (deriv y) x)
    (hy0 : ∀ x ∈ U, y x ≠ 0)
    (hp : ∀ x ∈ U, DifferentiableAt ℂ p x)
    (hW : ∀ x ∈ U, HasDerivAt W (-p x * W x) x)
    (hW0 : ∀ x ∈ U, W x ≠ 0)
    (ht : ∀ x ∈ U, HasDerivAt t (W x / y x ^ 2) x)
    (hODE : ∀ x ∈ U,
      deriv (deriv y) x + p x * deriv y x + q x * y x = 0)
    {x : ℂ} (hx : x ∈ U) :
    deriv t x ≠ 0 ∧
      HasDerivAt (deriv t)
        ((-p x - 2 * (deriv y x / y x)) * deriv t x) x ∧
      HasDerivAt (deriv (deriv t))
        ((-deriv p x - 2 * (-p x * (deriv y x / y x) - q x -
          (deriv y x / y x) ^ 2) + (-p x - 2 * (deriv y x / y x)) ^ 2) *
            deriv t x) x ∧
      preSchwarzian t x = -p x - 2 * (deriv y x / y x) ∧
      schwarzian t x = 2 * q x - deriv p x - (1 / 2 : ℂ) * p x ^ 2 := by
  let L : ℂ → ℂ := fun z => deriv y z / y z
  let G : ℂ → ℂ := fun z => -p z - 2 * L z
  have hdt (z : ℂ) (hz : z ∈ U) : deriv t z = W z / y z ^ 2 := (ht z hz).deriv
  have hn (z : ℂ) (hz : z ∈ U) : deriv t z ≠ 0 := by
    rw [hdt z hz]
    exact div_ne_zero (hW0 z hz) (pow_ne_zero 2 (hy0 z hz))
  have hsecond (z : ℂ) (hz : z ∈ U) :
      HasDerivAt (deriv t) (G z * deriv t z) z := by
    have he : deriv t =ᶠ[𝓝 z] (fun w => W w / y w ^ 2) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact hdt w hw
    have hd := (hW z hz).div ((hy z hz).1.hasDerivAt.pow 2)
      (pow_ne_zero 2 (hy0 z hz))
    convert hd.congr_of_eventuallyEq he using 1
    dsimp [G, L]
    rw [hdt z hz]
    field_simp [hy0 z hz]
    <;> ring
  have hL : HasDerivAt L (-p x * L x - q x - L x ^ 2) x := by
    have he : deriv (deriv y) x = -p x * deriv y x - q x * y x := by
      linear_combination hODE x hx
    have hd := (hy x hx).2.hasDerivAt.div (hy x hx).1.hasDerivAt (hy0 x hx)
    convert hd using 1
    dsimp [L]
    rw [he]
    field_simp [hy0 x hx]
    <;> ring
  have hG : HasDerivAt G
      (-deriv p x - 2 * (-p x * L x - q x - L x ^ 2)) x :=
    (hp x hx).hasDerivAt.neg.sub (hL.const_mul 2)
  have he2 : deriv (deriv t) =ᶠ[𝓝 x] (fun z => G z * deriv t z) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact (hsecond z hz).deriv
  have hthird : HasDerivAt (deriv (deriv t))
      ((-deriv p x - 2 * (-p x * L x - q x - L x ^ 2) + G x ^ 2) *
        deriv t x) x := by
    convert (hG.mul (hsecond x hx)).congr_of_eventuallyEq he2 using 1 <;> ring
  have hg : preSchwarzian t x = G x := by
    rw [preSchwarzian, (hsecond x hx).deriv]
    exact mul_div_cancel_right₀ _ (hn x hx)
  refine ⟨hn x hx, hsecond x hx, hthird, hg, ?_⟩
  rw [schwarzian, hthird.deriv, hg, mul_div_cancel_right₀ _ (hn x hx)]
  dsimp [G]
  ring

end D5.S3.Analytic.AbelRatioSchwarzian
