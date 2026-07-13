/- GID: D5/S3/Weil/TestFunctions
   generality: I
   mirror-B: none(waiver:formal-analysis-foundation-only)
   mirror-E: none(waiver:structural-closure-properties-only)
   anchors: [pzg/v170/26.4]
   digest: Bundle even smooth compact tests and close them under involution and convolution. -/

import D5.S3.Weil.Convention
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.Basic

namespace D5.S3.Weil.TestFunctions

open MeasureTheory
open scoped ComplexConjugate Convolution ContDiff

/--
Even smooth compactly supported complex test functions on the additive real line.
Pinned mathlib writes `C^infinity` as `ContDiff real infinity`; its outer `omega`
order denotes analyticity and would make compact support degenerate.
-/
structure WeilTestFunction where
  toFun : ℝ → ℂ
  contDiff' : ContDiff ℝ ∞ toFun
  hasCompactSupport' : HasCompactSupport toFun
  even' : ∀ x, toFun (-x) = toFun x

instance : FunLike WeilTestFunction ℝ ℂ where
  coe := WeilTestFunction.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

@[ext]
theorem WeilTestFunction.ext {f g : WeilTestFunction} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

protected theorem WeilTestFunction.contDiff (g : WeilTestFunction) :
    ContDiff ℝ ∞ (g : ℝ → ℂ) :=
  g.contDiff'

protected theorem WeilTestFunction.hasCompactSupport (g : WeilTestFunction) :
    HasCompactSupport (g : ℝ → ℂ) :=
  g.hasCompactSupport'

protected theorem WeilTestFunction.even (g : WeilTestFunction) (x : ℝ) :
    g (-x) = g x :=
  g.even' x

protected theorem WeilTestFunction.continuous (g : WeilTestFunction) :
    Continuous (g : ℝ → ℂ) :=
  g.contDiff.continuous

protected theorem WeilTestFunction.locallyIntegrable (g : WeilTestFunction) :
    LocallyIntegrable (g : ℝ → ℂ) :=
  g.continuous.locallyIntegrable

protected theorem WeilTestFunction.integrable (g : WeilTestFunction) :
    Integrable (g : ℝ → ℂ) :=
  g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

/-- A fixed radius-one/radius-two smooth bump centered at zero. -/
noncomputable def standardBump : ContDiffBump (0 : ℝ) := default

/-- A concrete nonzero member of the Weil test bundle. -/
noncomputable def standardTestFunction : WeilTestFunction where
  toFun := Complex.ofRealCLM ∘ standardBump
  contDiff' := Complex.ofRealCLM.contDiff.comp standardBump.contDiff
  hasCompactSupport' := standardBump.hasCompactSupport.comp_left (by simp)
  even' x := by
    change (standardBump (-x) : ℂ) = (standardBump x : ℂ)
    rw [standardBump.neg]

/-- The concrete test is nonzero: it equals one at its center. -/
@[simp]
theorem standardTestFunction_zero : standardTestFunction 0 = 1 := by
  change (standardBump 0 : ℂ) = 1
  have hreal : standardBump 0 = 1 :=
    standardBump.one_of_mem_closedBall (by simp [standardBump.rIn_pos.le])
  exact_mod_cast hreal

/-- The Weil involution `g tilde (x) = conj (g (-x))`. -/
noncomputable def involution (g : WeilTestFunction) : WeilTestFunction where
  toFun x := Complex.conjCLE (g (-x))
  contDiff' := by
    have hneg : ContDiff ℝ ∞ (fun x : ℝ => g (-x)) :=
      g.contDiff.comp contDiff_neg
    change ContDiff ℝ ∞ (Complex.conjCLE ∘ fun x : ℝ => g (-x))
    exact Complex.conjCLE.contDiff.comp hneg
  hasCompactSupport' := by
    have hneg := g.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)
    have hconj := hneg.comp_left (by simp : conj (0 : ℂ) = 0)
    simpa [Function.comp_def, Homeomorph.neg] using hconj
  even' x := by
    simp only [neg_neg, g.even x]

@[simp]
theorem involution_apply (g : WeilTestFunction) (x : ℝ) :
    involution g x = conj (g (-x)) :=
  Complex.conjCLE_apply _

@[simp]
theorem involution_involution (g : WeilTestFunction) : involution (involution g) = g := by
  ext x
  simp

/-- Complex multiplication as a continuous real-bilinear map. -/
noncomputable abbrev complexMul : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.mul ℝ ℂ

/-- Convolution with respect to Lebesgue/Haar volume on the additive real line. -/
noncomputable def convolve (f g : WeilTestFunction) : WeilTestFunction where
  toFun := MeasureTheory.convolution f g complexMul volume
  contDiff' :=
    g.hasCompactSupport.contDiff_convolution_right (n := (⊤ : ℕ∞))
      complexMul f.locallyIntegrable g.contDiff
  hasCompactSupport' :=
    f.hasCompactSupport.convolution complexMul g.hasCompactSupport
  even' _x :=
    convolution_neg_of_neg_eq complexMul
      (Filter.Eventually.of_forall f.even)
      (Filter.Eventually.of_forall g.even)

theorem convolve_apply (f g : WeilTestFunction) (x : ℝ) :
    convolve f g x = ∫ t : ℝ, f t * g (x - t) :=
  rfl

/-- The concrete convolution square used by Weil positivity: `g star g tilde`. -/
noncomputable def convolutionSquare (g : WeilTestFunction) : WeilTestFunction :=
  convolve g (involution g)

@[simp]
theorem convolutionSquare_apply (g : WeilTestFunction) (x : ℝ) :
    convolutionSquare g x = ∫ t : ℝ, g t * conj (g (t - x)) := by
  rw [convolutionSquare, convolve_apply]
  simp only [involution_apply, neg_sub]

theorem convolutionSquare_contDiff (g : WeilTestFunction) :
    ContDiff ℝ ∞ (convolutionSquare g : ℝ → ℂ) :=
  (convolutionSquare g).contDiff

theorem convolutionSquare_hasCompactSupport (g : WeilTestFunction) :
    HasCompactSupport (convolutionSquare g : ℝ → ℂ) :=
  (convolutionSquare g).hasCompactSupport

theorem convolutionSquare_even (g : WeilTestFunction) (x : ℝ) :
    convolutionSquare g (-x) = convolutionSquare g x :=
  (convolutionSquare g).even x

end D5.S3.Weil.TestFunctions
