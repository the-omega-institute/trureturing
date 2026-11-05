/- GID: D5/S3/Geometry/Hyperideal/LengthGramStrictOpen
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramStrictOpen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Maps.Basic]
   utility: none
   digest: The strict dual/cap Lorentz sign region is open in hyperbolic three-space. -/

/-
Escape audit unfinished: issue https://github.com/the-omega-institute/trureturing/issues/24965
tracks the missing faithful four-slot Reg mirror.
-/

import D5.S3.Geometry.Hyperideal.LengthGramStrictRegion
import Mathlib.Topology.Maps.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix Topology
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramDualPairing
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.Hyperideal.LengthGramStrictRegion
open D5.S3.Geometry.HyperbolicUpperHalfSpace
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.LengthGramStrictOpen

private theorem lift_continuous : Continuous lift := by
  have hc : Continuous (fun p : HyperbolicThreeSpace => p.coordinates) :=
    (D5.S3.Geometry.HyperbolicTopology.coordinatesHomeomorph (E := ℂ)).continuous
  have hh : Continuous (fun p : HyperbolicThreeSpace => height p.coordinates) :=
    (WithLp.continuous_snd 2 ℂ ℝ).comp (continuous_subtype_val.comp hc)
  have hx : Continuous (fun p : HyperbolicThreeSpace => p.coordinates.val.fst.re) :=
    Complex.continuous_re.comp ((WithLp.continuous_fst 2 ℂ ℝ).comp
      (continuous_subtype_val.comp hc))
  have hy : Continuous (fun p : HyperbolicThreeSpace => p.coordinates.val.fst.im) :=
    Complex.continuous_im.comp ((WithLp.continuous_fst 2 ℂ ℝ).comp
      (continuous_subtype_val.comp hc))
  have hn (p : HyperbolicThreeSpace) : height p.coordinates ≠ 0 :=
    p.coordinates.property.ne'
  apply continuous_pi
  intro i
  fin_cases i
  · exact hx.div hh hn
  · exact hy.div hh hn
  · exact ((((hx.pow 2).add (hy.pow 2)).add (hh.pow 2)).sub continuous_const).div
      (continuous_const.mul hh) (fun p => mul_ne_zero (by norm_num) (hn p))
  · exact ((((hx.pow 2).add (hy.pow 2)).add (hh.pow 2)).add continuous_const).div
      (continuous_const.mul hh) (fun p => mul_ne_zero (by norm_num) (hn p))

private theorem lorentz_left_continuous (z : Fin 4 → ℝ) :
    Continuous (fun p : HyperbolicThreeSpace => lorentz (lift p) z) := by
  dsimp only [lorentz]
  exact continuous_finsetSum _ fun k _ =>
    (continuous_const.mul ((continuous_apply k).comp lift_continuous)).mul continuous_const

theorem strictDualCapRegion_isOpen
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    IsOpen (strictDualCapRegion l M) := by
  change IsOpen {p : HyperbolicThreeSpace |
    ∀ i, 0 < lorentz (lift p) (dualVector (lengthGram l) M i) ∧
      lorentz (lift p) (M i) < 0}
  rw [show {p : HyperbolicThreeSpace |
      ∀ i, 0 < lorentz (lift p) (dualVector (lengthGram l) M i) ∧
        lorentz (lift p) (M i) < 0} =
      ⋂ i, {p : HyperbolicThreeSpace |
        0 < lorentz (lift p) (dualVector (lengthGram l) M i) ∧
          lorentz (lift p) (M i) < 0} by
    ext p
    simp]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (lorentz_left_continuous _)).inter
    (isOpen_lt (lorentz_left_continuous _) continuous_const)

#print axioms strictDualCapRegion_isOpen
end D5.S3.Geometry.Hyperideal.LengthGramStrictOpen
