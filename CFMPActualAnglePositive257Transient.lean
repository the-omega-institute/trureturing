import CFMPOriginalAngleInverseCore309Transient
import D5.S3.Geometry.ODE.UniformLocalGlobalPasting
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.Connected.Clopen
import D5.S3.Geometry.Hyperideal.GramDomainContraction
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import D5.S3.Geometry.Hyperideal.S4OppositePairAction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import D5.S3.Geometry.Hyperideal.LengthGramBody
import D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
import D5.S3.Geometry.Hyperideal.FourCycleCurvature
import D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Lean.Util.CollectAxioms

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix.Norms.Operator

namespace CFMPNormalizedInverseTangent107

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℝ

def inverseVariation (G E : Mat) : Mat := -(G⁻¹ * E * G⁻¹)

def correction (G E : Mat) : Mat :=
  Matrix.diagonal (fun i => inverseVariation G E i i / (2 * G⁻¹ i i))

def normalizedTangent (G E : Mat) : Mat :=
  normalScale G *
    (inverseVariation G E - correction G E * G⁻¹ - G⁻¹ * correction G E) *
    normalScale G

private def entryCLM (i j : n) : Mat →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

private def diagonalCLM : (n → ℝ) →L[ℝ] Mat :=
  (Matrix.diagonalLinearMap n ℝ ℝ).toContinuousLinearMap

private theorem diagonalCLM_apply (v : n → ℝ) :
    diagonalCLM v = Matrix.diagonal v := by
  rfl

private theorem inverse_hasFDerivAt (G : Mat) (hG : IsUnit G) :
    HasFDerivAt (fun M : Mat => M⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ Mat G⁻¹ G⁻¹) G := by
  have hi : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ Mat (Ring.inverse G) (Ring.inverse G)) G := by
    rcases hG with ⟨u, hu⟩
    simpa only [← Ring.inverse_unit, hu] using
      hasFDerivAt_ringInverse (𝕜 := ℝ) u
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using hi

private theorem scale_differentiableAt (G : Mat) (hG : IsUnit G)
    (hpos : ∀ i, 0 < G⁻¹ i i) : DifferentiableAt ℝ normalScale G := by
  have hi := (inverse_hasFDerivAt G hG).differentiableAt
  have hv : DifferentiableAt ℝ
      (fun M : Mat => fun i => (Real.sqrt (M⁻¹ i i))⁻¹) G := by
    apply differentiableAt_pi.mpr
    intro i
    have he : DifferentiableAt ℝ (fun M : Mat => M⁻¹ i i) G := by
      simpa only [entryCLM, LinearMap.coe_toContinuousLinearMap',
        Matrix.entryLinearMap_apply, Function.comp_def] using!
        (entryCLM i i).differentiableAt.comp G hi
    exact (he.sqrt (hpos i).ne').inv (Real.sqrt_pos.mpr (hpos i)).ne'
  simpa only [normalScale, diagonalCLM, LinearMap.coe_toContinuousLinearMap',
    Matrix.diagonalLinearMap_apply, Function.comp_def] using!
    diagonalCLM.differentiableAt.comp G hv

theorem normalizedInverse_hasFDerivAt (G : Mat) (hG : IsUnit G)
    (hpos : ∀ i, 0 < G⁻¹ i i) :
    HasFDerivAt normalizedInverse (fderiv ℝ normalizedInverse G) G := by
  have hs := scale_differentiableAt G hG hpos
  have hi := (inverse_hasFDerivAt G hG).differentiableAt
  exact ((hs.mul hi).mul hs).hasFDerivAt

private theorem inverse_line_hasDerivAt (G E : Mat) (hG : IsUnit G) :
    HasDerivAt (fun s : ℝ => (G + s • E)⁻¹) (inverseVariation G E) 0 := by
  have hl : HasDerivAt (fun s : ℝ => G + s • E) E 0 := by
    apply (hasDerivAt_const_add_iff G).mpr
    simpa only [one_smul] using! (hasDerivAt_id (0 : ℝ)).smul_const E
  simpa only [Function.comp_def, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, inverseVariation] using!
    (inverse_hasFDerivAt G hG).comp_hasDerivAt_of_eq 0 hl (by simp)

private theorem scale_line_hasDerivAt (G E : Mat) (hG : IsUnit G)
    (hpos : ∀ i, 0 < G⁻¹ i i) :
    HasDerivAt (fun s : ℝ => normalScale (G + s • E))
      (-(correction G E * normalScale G)) 0 := by
  have hi := inverse_line_hasDerivAt G E hG
  have hv : HasDerivAt
      (fun s : ℝ => fun i => (Real.sqrt ((G + s • E)⁻¹ i i))⁻¹)
      (fun i => -(inverseVariation G E i i / (2 * G⁻¹ i i)) *
        (Real.sqrt (G⁻¹ i i))⁻¹) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have he : HasDerivAt (fun s : ℝ => (G + s • E)⁻¹ i i)
        (inverseVariation G E i i) 0 := by
      simpa only [Function.comp_def, entryCLM, LinearMap.coe_toContinuousLinearMap',
        Matrix.entryLinearMap_apply] using!
        (entryCLM i i).hasFDerivAt.comp_hasDerivAt 0 hi
    have he0 : (G + (0 : ℝ) • E)⁻¹ i i ≠ 0 := by
      simpa only [zero_smul, add_zero] using (hpos i).ne'
    have hroot : Real.sqrt ((G + (0 : ℝ) • E)⁻¹ i i) ≠ 0 := by
      simpa only [zero_smul, add_zero] using (Real.sqrt_pos.mpr (hpos i)).ne'
    convert (he.sqrt he0).inv hroot using 1 <;> try rfl
    simp only [zero_smul, add_zero]
    rw [Real.sq_sqrt (hpos i).le]
    field_simp [(hpos i).ne', (Real.sqrt_pos.mpr (hpos i)).ne']
    <;> ring
  have hd := diagonalCLM.hasFDerivAt.comp_hasDerivAt 0 hv
  convert hd using 1 <;> try rfl
  erw [diagonalCLM_apply]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [correction, normalScale, Matrix.diagonal_mul]
  · simp [correction, normalScale, Matrix.diagonal_mul, Matrix.diagonal_apply, hij]

private theorem normalizedInverse_line_hasDerivAt (G E : Mat) (hG : IsUnit G)
    (hpos : ∀ i, 0 < G⁻¹ i i) :
    HasDerivAt (fun s : ℝ => normalizedInverse (G + s • E))
      (normalizedTangent G E) 0 := by
  have hi := inverse_line_hasDerivAt G E hG
  have hs := scale_line_hasDerivAt G E hG hpos
  have hcomm : correction G E * normalScale G = normalScale G * correction G E := by
    dsimp [correction, normalScale]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  convert (hs.mul hi).mul hs using 1 <;> try rfl
  simp only [Pi.mul_apply, zero_smul, add_zero]
  change normalScale G *
      (inverseVariation G E - correction G E * G⁻¹ - G⁻¹ * correction G E) *
      normalScale G =
    ((-(correction G E * normalScale G)) * G⁻¹ +
      normalScale G * inverseVariation G E) * normalScale G +
      (normalScale G * G⁻¹) * (-(correction G E * normalScale G))
  nth_rw 1 [hcomm]
  noncomm_ring

theorem normalizedInverse_fderiv_apply (G E : Mat) (hG : IsUnit G)
    (hpos : ∀ i, 0 < G⁻¹ i i) :
    fderiv ℝ normalizedInverse G E = normalizedTangent G E := by
  have hl : HasDerivAt (fun s : ℝ => G + s • E) E 0 := by
    apply (hasDerivAt_const_add_iff G).mpr
    simpa only [one_smul] using! (hasDerivAt_id (0 : ℝ)).smul_const E
  have hc := (normalizedInverse_hasFDerivAt G hG hpos).comp_hasDerivAt_of_eq
    0 hl (by simp)
  have hd := normalizedInverse_line_hasDerivAt G E hG hpos
  exact hc.unique hd

private theorem normalizedTangent_kernel
    (G A E D : Mat) (c : n → ℝ)
    (hGA : G * A = 1) (hAG : A * G = 1)
    (hdiag : ∀ i, G i i = 1) (hE : ∀ i, E i i = 0)
    (hD : IsUnit D)
    (hzero : D * (-(A * E * A) - Matrix.diagonal c * A -
        A * Matrix.diagonal c) * D = 0) : E = 0 := by
  have hleft : D * (-(A * E * A) - Matrix.diagonal c * A -
      A * Matrix.diagonal c) = 0 := by
    apply hD.mul_right_cancel
    simpa only [zero_mul] using hzero
  have hinner : -(A * E * A) - Matrix.diagonal c * A -
      A * Matrix.diagonal c = 0 := by
    apply hD.mul_left_cancel
    simpa only [mul_zero] using hleft
  have hconj := congrArg (fun K : Mat => G * K * G) hinner
  have hexpand :
      G * (-(A * E * A) - Matrix.diagonal c * A - A * Matrix.diagonal c) * G =
        -E - G * Matrix.diagonal c - Matrix.diagonal c * G := by
    calc
      _ = -(G * A) * E * (A * G) - G * Matrix.diagonal c * (A * G) -
          (G * A) * Matrix.diagonal c * G := by noncomm_ring
      _ = _ := by rw [hGA, hAG]; simp
  rw [hexpand] at hconj
  simp only [mul_zero, zero_mul] at hconj
  have hrel : -E = G * Matrix.diagonal c + Matrix.diagonal c * G := by
    calc
      -E = (-E - G * Matrix.diagonal c - Matrix.diagonal c * G) +
          (G * Matrix.diagonal c + Matrix.diagonal c * G) := by noncomm_ring
      _ = _ := by rw [hconj]; simp
  have hc : ∀ i, c i = 0 := by
    intro i
    have hi := congrArg (fun K : Mat => K i i) hrel
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul, hE i, hdiag i, neg_zero, one_mul, mul_one] at hi
    linarith
  have hC : Matrix.diagonal c = (0 : Mat) := by
    apply Matrix.diagonal_eq_zero.mpr
    funext i
    exact hc i
  simpa only [hC, mul_zero, zero_mul, add_zero, neg_eq_zero] using hrel

private theorem scale_isUnit (G : Mat) (hpos : ∀ i, 0 < G⁻¹ i i) :
    IsUnit (normalScale G) := by
  apply Matrix.isUnit_diagonal.mpr
  apply Pi.isUnit_iff.mpr
  intro i
  exact isUnit_iff_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (hpos i)).ne')

private theorem normalizedInverse_fderiv_kernel (G E : Mat) (hG : IsUnit G)
    (hpos : ∀ i, 0 < G⁻¹ i i) (hdiag : ∀ i, G i i = 1)
    (hE : ∀ i, E i i = 0) (hzero : fderiv ℝ normalizedInverse G E = 0) :
    E = 0 := by
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have ht : normalizedTangent G E = 0 := by
    rw [← normalizedInverse_fderiv_apply G E hG hpos]
    exact hzero
  apply normalizedTangent_kernel G G⁻¹ E (normalScale G)
    (fun i => inverseVariation G E i i / (2 * G⁻¹ i i))
    (Matrix.mul_nonsing_inv G hdet) (Matrix.nonsing_inv_mul G hdet)
    hdiag hE (scale_isUnit G hpos)
  exact ht

/-- The actual normalized inverse derivative is injective on zero-diagonal directions. -/
theorem normalizedInverse_unit_diagonal_tangent_injective
    (G : Mat) (hG : IsUnit G) (hpos : ∀ i, 0 < G⁻¹ i i)
    (hdiag : ∀ i, G i i = 1) :
    Function.Injective
      (fun E : {E : Mat // ∀ i, E i i = 0} => fderiv ℝ normalizedInverse G E.val) := by
  intro E F hEF
  change fderiv ℝ normalizedInverse G E.val =
    fderiv ℝ normalizedInverse G F.val at hEF
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply normalizedInverse_fderiv_kernel G (E.val - F.val) hG hpos hdiag
  · intro i
    change E.val i i - F.val i i = 0
    rw [E.property i, F.property i, sub_self]
  · rw [map_sub]
    exact sub_eq_zero.mpr hEF

#print axioms normalizedInverse_unit_diagonal_tangent_injective

end CFMPNormalizedInverseTangent107

end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology
open Set Filter
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)

end



noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology
open Set Filter
open scoped ContDiff Matrix.Norms.Elementwise
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open CFMPGenuineLengthNeighborhood435Transient
open CFMPOriginalSixPairedAngles435Transient
namespace CFMPOriginalGlobalSmoothCovolume103Transient

theorem sourceCosine_smooth (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (q : Fin 6) : ContDiffAt ℝ ∞ (fun p => sourceCosine p q) l := by
  have hcosh (i : Fin 6) : 1 < Real.cosh (l i) :=
    Real.one_lt_cosh.mpr (hl i).ne'
  have hleft : 0 < rad
      (Real.cosh (l (frame q 0)))
      (Real.cosh (l (frame q 1)))
      (Real.cosh (l (frame q 5))) :=
    D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.rad_positive _ _ _ (hcosh _) (hcosh _) (hcosh _)
  have hright : 0 < rad
      (Real.cosh (l (frame q 0)))
      (Real.cosh (l (frame q 2)))
      (Real.cosh (l (frame q 4))) :=
    D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.rad_positive _ _ _ (hcosh _) (hcosh _) (hcosh _)
  have hn : ContDiffAt ℝ ∞ (fun p : Fin 6 → ℝ =>
      numerator
        (Real.cosh (p (frame q 0)))
        (Real.cosh (p (frame q 1)))
        (Real.cosh (p (frame q 2)))
        (Real.cosh (p (frame q 3)))
        (Real.cosh (p (frame q 4)))
        (Real.cosh (p (frame q 5)))) l := by
    unfold numerator
    fun_prop
  have hL : ContDiffAt ℝ ∞ (fun p : Fin 6 → ℝ =>
      rad
        (Real.cosh (p (frame q 0)))
        (Real.cosh (p (frame q 1)))
        (Real.cosh (p (frame q 5)))) l := by
    unfold rad
    fun_prop
  have hR : ContDiffAt ℝ ∞ (fun p : Fin 6 → ℝ =>
      rad
        (Real.cosh (p (frame q 0)))
        (Real.cosh (p (frame q 2)))
        (Real.cosh (p (frame q 4)))) l := by
    unfold rad
    fun_prop
  exact (hn.div (hL.sqrt hleft.ne') (Real.sqrt_pos.mpr hleft).ne').div
    (hR.sqrt hright.ne') (Real.sqrt_pos.mpr hright).ne'

theorem sourceAngle_smooth (l : Fin 6 → ℝ) (hl : genuine l) (q : Fin 6) :
    ContDiffAt ℝ ∞ (fun p => sourceAngle p q) l :=
  (Real.contDiffAt_arccos (ne_of_gt (hl.2 q).1) (ne_of_lt (hl.2 q).2)).comp l
    (sourceCosine_smooth l hl.1 q)

end CFMPOriginalGlobalSmoothCovolume103Transient
end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Topology Matrix.Norms.Operator
open Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody (lengthGram)
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
open D5.S3.Geometry.Hyperideal.S4OppositePairAction (edgeIndex)
open CFMPGenuineLengthNeighborhood435Transient (genuine sourceCosine genuine_open)
open CFMPOriginalSixPairedAngles435Transient (sourceAngle vertexPerm original_relabel_cosine)
open CFMPOriginalAllSideCosines435Transient (relabel gram_relabel)
open CFMPOriginalUnitSideCosine435Transient (original_gram_cofactors inverse_gram_cosine)
open CFMPNormalizedInverseTangent107 (normalizedInverse normalScale)

namespace CFMPSourceAngleKernel111

private theorem normalized_source_angle (l : Lengths) (hl : genuine l) (q : Fin 6) :
    normalizedInverse (lengthGram l) (vertexPerm q 2) (vertexPerm q 3) =
      -Real.cos (sourceAngle l q) := by
  have hcos : Real.cos (sourceAngle l q) = sourceCosine l q :=
    Real.cos_arccos (hl.2 q).1.le (hl.2 q).2.le
  rw [hcos]
  exact normalized_source_cosine l hl q

private theorem normalized_diagonal (l : Lengths) (hl : genuine l) (i : Fin 4) :
    normalizedInverse (lengthGram l) i i = 1 := by
  have hp := inverse_diagonal_positive l hl i
  rw [normalized_entry, Real.mul_self_sqrt hp.le, div_self hp.ne']

private theorem lengthGram_symmetric (l : Lengths) : (lengthGram l).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem normalized_gram_symmetric (l : Lengths) :
    (normalizedInverse (lengthGram l)).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [normalized_entry, normalized_entry, (lengthGram_symmetric l).inv.apply i j]
  rw [mul_comm (Real.sqrt ((lengthGram l)⁻¹ j j))]

private def edgeBasis (k : Fin 6) : Mat := fun i j =>
  if i = j then 0 else if edgeIndex i j = k then 1 else 0

private theorem lengthGram_expansion (l : Lengths) :
    lengthGram l = (1 : Mat) - ∑ k : Fin 6, Real.cosh (l k) • edgeBasis k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lengthGram, edgeBasis, edgeIndex, Fin.sum_univ_succ,
      Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply]

def gramDirection (l v : Lengths) : Mat :=
  -(∑ k : Fin 6, (Real.sinh (l k) * v k) • edgeBasis k)

private theorem gramDirection_diagonal (l v : Lengths) (i : Fin 4) :
    gramDirection l v i i = 0 := by
  simp [gramDirection, Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply,
    edgeBasis]

private def edgeFirst : Fin 6 → Fin 4 := ![0, 0, 0, 2, 1, 1]
private def edgeSecond : Fin 6 → Fin 4 := ![1, 2, 3, 3, 3, 2]

private theorem gramDirection_edge (l v : Lengths) (k : Fin 6) :
    gramDirection l v (edgeFirst k) (edgeSecond k) = -(Real.sinh (l k) * v k) := by
  fin_cases k <;>
    norm_num [gramDirection, edgeBasis, edgeIndex, edgeFirst, edgeSecond,
      Fin.sum_univ_succ, Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]

private theorem lengthGram_line_hasDerivAt (l v : Lengths) :
    HasDerivAt (fun s : ℝ => lengthGram (l + s • v)) (gramDirection l v) 0 := by
  have hs : HasDerivAt
      (fun s : ℝ => ∑ k : Fin 6, Real.cosh ((l + s • v) k) • edgeBasis k)
      (∑ k : Fin 6, (Real.sinh (l k) * v k) • edgeBasis k) 0 := by
    apply HasDerivAt.fun_sum
    intro k _
    have hk : HasDerivAt (fun s : ℝ => l k + s * v k) (v k) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v k)).const_add (l k)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero] using
      hk.cosh.smul_const (edgeBasis k)
  simpa only [← lengthGram_expansion, gramDirection] using hs.const_sub (1 : Mat)

private theorem angle_kernel (l : Lengths) (hl : genuine l) (v : Lengths)
    (hv : ∀ q, fderiv ℝ (fun p => sourceAngle p q) l v = 0) : v = 0 := by
  let G := lengthGram l
  let E := gramDirection l v
  let Z := fderiv ℝ normalizedInverse G E
  have hline : HasDerivAt (fun s : ℝ => l + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add l
  have hgen : ∀ᶠ s in 𝓝 (0 : ℝ), genuine (l + s • v) := by
    exact CFMPGenuineLengthNeighborhood435Transient.path_eventually_genuine
      (fun s => l + s • v) 0 hline.continuousAt (by simpa using hl)
  have hN : HasDerivAt
      (fun s : ℝ => normalizedInverse (lengthGram (l + s • v))) Z 0 := by
    exact (CFMPNormalizedInverseTangent107.normalizedInverse_hasFDerivAt
      G (genuine_gram_isUnit l hl) (inverse_diagonal_positive l hl)).comp_hasDerivAt_of_eq
        0 (lengthGram_line_hasDerivAt l v) (by simp [G])
  have hentry (i j : Fin 4) : HasDerivAt
      (fun s : ℝ => normalizedInverse (lengthGram (l + s • v)) i j) (Z i j) 0 := by
    convert! (entryCLM i j).hasFDerivAt.comp_hasDerivAt 0 hN using 1 <;>
      simp only [Function.comp_def, entryCLM, Matrix.entryLinearMap_apply]
  have hangle (q : Fin 6) : HasDerivAt
      (fun s : ℝ => sourceAngle (l + s • v) q) 0 0 := by
    have hd := ((CFMPOriginalGlobalSmoothCovolume103Transient.sourceAngle_smooth
      l hl q).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
        0 hline (by simp)
    simpa only [Function.comp_def, hv q] using hd
  have hcos (q : Fin 6) : HasDerivAt
      (fun s : ℝ => -Real.cos (sourceAngle (l + s • v) q)) 0 0 := by
    convert! (hangle q).cos.neg using 1 <;> simp
  have hp (q : Fin 6) : Z (vertexPerm q 2) (vertexPerm q 3) = 0 := by
    have he : (fun s : ℝ => normalizedInverse (lengthGram (l + s • v))
        (vertexPerm q 2) (vertexPerm q 3)) =ᶠ[𝓝 0]
        (fun s => -Real.cos (sourceAngle (l + s • v) q)) := by
      filter_upwards [hgen] with s hs
      exact normalized_source_angle _ hs q
    exact (hentry _ _).unique ((hcos q).congr_of_eventuallyEq he)
  have hpr (q : Fin 6) : Z (vertexPerm q 3) (vertexPerm q 2) = 0 := by
    have he : (fun s : ℝ => normalizedInverse (lengthGram (l + s • v))
        (vertexPerm q 3) (vertexPerm q 2)) =ᶠ[𝓝 0]
        (fun s => -Real.cos (sourceAngle (l + s • v) q)) := by
      filter_upwards [hgen] with s hs
      exact ((normalized_gram_symmetric _).apply _ _).trans
        (normalized_source_angle _ hs q)
    exact (hentry _ _).unique ((hcos q).congr_of_eventuallyEq he)
  have hd (i : Fin 4) : Z i i = 0 := by
    have he : (fun s : ℝ => normalizedInverse (lengthGram (l + s • v)) i i) =ᶠ[𝓝 0]
        (fun _ => (1 : ℝ)) := by
      filter_upwards [hgen] with s hs
      exact normalized_diagonal _ hs i
    exact (hentry i i).unique ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq he)
  have hZ : Z = 0 := by
    ext i j
    change Z i j = 0
    fin_cases i <;> fin_cases j <;>
      first | exact hd _ | exact hp 0 | exact hp 1 | exact hp 2 | exact hp 3 |
        exact hp 4 | exact hp 5 | exact hpr 0 | exact hpr 1 | exact hpr 2 |
        exact hpr 3 | exact hpr 4 | exact hpr 5
  have hEd : ∀ i, E i i = 0 := gramDirection_diagonal l v
  have hsub : (⟨E, hEd⟩ : {E : Mat // ∀ i, E i i = 0}) = ⟨0, by simp⟩ := by
    apply CFMPNormalizedInverseTangent107.normalizedInverse_unit_diagonal_tangent_injective
      G (genuine_gram_isUnit l hl) (inverse_diagonal_positive l hl)
      (by intro i; fin_cases i <;> rfl)
    simpa only [map_zero] using hZ
  have hE : gramDirection l v = 0 := congrArg Subtype.val hsub
  funext k
  have he := congrArg (fun M : Mat => M (edgeFirst k) (edgeSecond k)) hE
  rw [gramDirection_edge] at he
  have hsinh : Real.sinh (l k) ≠ 0 := (Real.sinh_pos_iff.mpr (hl.1 k)).ne'
  change -(Real.sinh (l k) * v k) = 0 at he
  have hm : Real.sinh (l k) * v k = 0 := neg_eq_zero.mp he
  exact (mul_eq_zero.mp hm).resolve_left hsinh

private def angleDerivative (l : Lengths) : Lengths →L[ℝ] Lengths :=
  ContinuousLinearMap.pi (fun q => fderiv ℝ (fun p => sourceAngle p q) l)

private theorem sourceAngles_hasFDerivAt (l : Lengths) (hl : genuine l) :
    HasFDerivAt (fun p : Lengths => fun q => sourceAngle p q) (angleDerivative l) l := by
  apply hasFDerivAt_pi.mpr
  intro q
  exact ((CFMPOriginalGlobalSmoothCovolume103Transient.sourceAngle_smooth
    l hl q).differentiableAt (by simp)).hasFDerivAt

/-- The original six-length source-angle map has injective derivative throughout its genuine domain. -/
theorem sourceAngle_jacobian_injective (l : Lengths) (hl : genuine l) :
    Function.Injective (fderiv ℝ (fun p : Lengths => fun q => sourceAngle p q) l) := by
  rw [(sourceAngles_hasFDerivAt l hl).fderiv]
  intro v w hvw
  apply sub_eq_zero.mp
  apply angle_kernel l hl (v - w)
  intro q
  rw [map_sub]
  have hq := congrFun hvw q
  change fderiv ℝ (fun p => sourceAngle p q) l v =
    fderiv ℝ (fun p => sourceAngle p q) l w at hq
  rw [hq, sub_self]

#print axioms sourceAngle_jacobian_injective

end CFMPSourceAngleKernel111

end

example (l : Fin 6 → ℝ) (hl : CFMPGenuineLengthNeighborhood435Transient.genuine l) :
    Function.Injective
      (fderiv ℝ (fun p : Fin 6 → ℝ => fun q =>
        CFMPOriginalSixPairedAngles435Transient.sourceAngle p q) l) :=
  CFMPSourceAngleKernel111.sourceAngle_jacobian_injective l hl

run_cmd do
  let name := ``CFMPSourceAngleKernel111.sourceAngle_jacobian_injective
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "SOURCE_ANGLE128: final theorem absent from checked environment"
  let axioms ← Lean.collectAxioms name
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for a in axioms do
    unless allowed.contains a do
      Lean.throwError m!"SOURCE_ANGLE128: forbidden axiom {a}"
  let names := String.intercalate ", " (axioms.toList.mergeSort Lean.Name.lt |>.map toString)
  Lean.logInfo m!"CFMP_SOURCE_ANGLE128 exact_axioms=[{names}]"


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped Matrix BigOperators Topology
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos)
open CFMPGenuineLengthNeighborhood435Transient (genuine sourceCosine)
open CFMPOriginalSixPairedAngles435Transient (sourceAngle)

namespace CFMPRegularJacobian110Transient

abbrev Lengths := Fin 6 → ℝ
abbrev Covector := Lengths →L[ℝ] ℝ

def regularPoint (t : ℝ) : Lengths := fun _ => t
private def π (i : Fin 6) : Covector := ContinuousLinearMap.proj i
private def adjacent (q : Fin 6) : Covector :=
  π (frame q 1) + π (frame q 2) + π (frame q 4) + π (frame q 5)
private def R (x : ℝ) := (x+1)^2*(2*x-1)
private def P (x : ℝ) := x*(x+1)^2
private def phi (x : ℝ) := x/(2*x-1)

private theorem rad_regular (x : ℝ) : rad x x x = R x := by unfold rad R; ring
private theorem num_regular (x : ℝ) : numerator x x x x x x = P x := by
  unfold numerator P
  ring

private theorem regular_bounds (x : ℝ) (hx : 1 < x) :
    0 < phi x ∧ phi x < 1 := by
  have hd : 0 < 2*x-1 := by linarith
  refine ⟨div_pos (by linarith) hd, ?_⟩
  exact (div_lt_one hd).mpr (by linarith)

private theorem R_pos (x : ℝ) (hx : 1 < x) : 0 < R x := by
  unfold R
  have hp : 0 < x+1 := by linarith
  exact mul_pos (sq_pos_of_pos hp) (by linarith)

private theorem regular_cosine (x : ℝ) (hx : 1 < x) :
    cosine x x x x x x = phi x := by
  have hr := R_pos x hx
  have hs : Real.sqrt (R x) * Real.sqrt (R x) = R x := by
    simpa only [pow_two] using Real.sq_sqrt hr.le
  simp only [cosine, rad_regular, num_regular, div_div, hs]
  have hxp : x+1 ≠ 0 := (show 0 < x+1 by linarith).ne'
  have htwo : 2*x-1 ≠ 0 := (show 0 < 2*x-1 by linarith).ne'
  unfold P R phi
  field_simp [hxp, htwo]
  <;> ring

private def sourcePoly (q : Fin 6) (l : Lengths) : ℝ :=
  numerator (Real.cosh (l (frame q 0))) (Real.cosh (l (frame q 1)))
    (Real.cosh (l (frame q 2))) (Real.cosh (l (frame q 3)))
    (Real.cosh (l (frame q 4))) (Real.cosh (l (frame q 5)))
private def sourceDen (q : Fin 6) (l : Lengths) : ℝ :=
  Real.sqrt (rad (Real.cosh (l (frame q 0))) (Real.cosh (l (frame q 1)))
      (Real.cosh (l (frame q 5)))) *
    Real.sqrt (rad (Real.cosh (l (frame q 0))) (Real.cosh (l (frame q 2)))
      (Real.cosh (l (frame q 4))))

private theorem poly_regular (q : Fin 6) (t : ℝ) :
    sourcePoly q (regularPoint t) = P (Real.cosh t) := by
  simpa only [sourcePoly, regularPoint] using num_regular (Real.cosh t)
private theorem den_regular (q : Fin 6) (t : ℝ) (ht : 0 < t) :
    sourceDen q (regularPoint t) = R (Real.cosh t) := by
  have hx := Real.one_lt_cosh.mpr ht.ne'
  simpa only [sourceDen, regularPoint, rad_regular, pow_two] using
    Real.sq_sqrt (R_pos (Real.cosh t) hx).le

theorem sourceCosine_regular (q : Fin 6) (t : ℝ) (ht : 0 < t) :
    sourceCosine (regularPoint t) q = phi (Real.cosh t) := by
  simpa only [sourceCosine, rawCos, regularPoint] using
    regular_cosine (Real.cosh t) (Real.one_lt_cosh.mpr ht.ne')

theorem regular_genuine (t : ℝ) (ht : 0 < t) : genuine (regularPoint t) := by
  refine ⟨fun _ => ht, fun q => ?_⟩
  rw [sourceCosine_regular q t ht]
  have hb := regular_bounds (Real.cosh t) (Real.one_lt_cosh.mpr ht.ne')
  exact ⟨by linarith [hb.1], hb.2⟩

private theorem regular_root_pos (t : ℝ) (ht : 0 < t) :
    0 < Real.sqrt (1-(phi (Real.cosh t))^2) := by
  have hb := regular_bounds (Real.cosh t) (Real.one_lt_cosh.mpr ht.ne')
  apply Real.sqrt_pos.mpr
  nlinarith only [hb.1, hb.2, mul_pos hb.1 (sub_pos.mpr hb.2)]

/-- The original arccos branch has strictly positive sine. -/
theorem sin_sourceAngle_regular (q : Fin 6) (t : ℝ) (ht : 0 < t) :
    0 < Real.sin (sourceAngle (regularPoint t) q) := by
  simp only [sourceAngle, sourceCosine_regular q t ht, Real.sin_arccos]
  exact regular_root_pos t ht

private def numDerivative (t : ℝ) (q : Fin 6) : Covector :=
  Real.sinh t •
    ((Real.cosh t*(Real.cosh t+1)) • adjacent q -
      ((Real.cosh t)^2-1) • π (frame q 3))
private def denDerivative (t : ℝ) (q : Fin 6) : Covector :=
  (2*Real.cosh t*(Real.cosh t+1)*Real.sinh t/2) •
    ((2 : ℝ) • π (frame q 0) + adjacent q)

/-- A three-variable polynomial derivative on the full six-dimensional length space. -/
private theorem rad_hasFDerivAt_regular (t : ℝ) (i j k : Fin 6) :
    HasFDerivAt (fun l : Lengths => rad (Real.cosh (l i))
      (Real.cosh (l j)) (Real.cosh (l k)))
      ((2*Real.cosh t*(Real.cosh t+1)*Real.sinh t) • (π i+π j+π k))
      (regularPoint t) := by
  have hi := (hasFDerivAt_apply (𝕜 := ℝ) i (regularPoint t)).cosh
  have hj := (hasFDerivAt_apply (𝕜 := ℝ) j (regularPoint t)).cosh
  have hk := (hasFDerivAt_apply (𝕜 := ℝ) k (regularPoint t)).cosh
  have h := ((((((hi.const_mul 2).mul hj).mul hk).add (hi.pow 2)).add
    (hj.pow 2)).add (hk.pow 2)).sub_const 1
  exact h.congr_fderiv (by
    ext v
    simp [π, regularPoint, smul_eq_mul]
    <;> ring)

private theorem poly_hasFDerivAt_regular (t : ℝ) (q : Fin 6) :
    HasFDerivAt (sourcePoly q) (numDerivative t q) (regularPoint t) := by
  have hc (j : Fin 6) :=
    (hasFDerivAt_apply (𝕜 := ℝ) (frame q j) (regularPoint t)).cosh
  have h := ((((hc 1).mul (hc 2)).add ((hc 4).mul (hc 5))).add
    (((hc 0).mul (hc 1)).mul (hc 4))).add
    (((hc 0).mul (hc 2)).mul (hc 5))
  have h' := h.sub ((((hc 0).pow 2).sub_const 1).mul (hc 3))
  exact h'.congr_fderiv (by
    ext v
    simp [numDerivative, π, adjacent, regularPoint, smul_eq_mul]
    <;> ring)

private theorem den_hasFDerivAt_regular (t : ℝ) (ht : 0 < t) (q : Fin 6) :
    HasFDerivAt (sourceDen q) (denDerivative t q) (regularPoint t) := by
  have hx : 1 < Real.cosh t := Real.one_lt_cosh.mpr ht.ne'
  have hR := R_pos (Real.cosh t) hx
  have hne : Real.sqrt (R (Real.cosh t)) ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
  have hL := (rad_hasFDerivAt_regular t (frame q 0) (frame q 1) (frame q 5)).sqrt
    (by simpa only [regularPoint, rad_regular] using hR.ne')
  have hR' := (rad_hasFDerivAt_regular t (frame q 0) (frame q 2) (frame q 4)).sqrt
    (by simpa only [regularPoint, rad_regular] using hR.ne')
  exact (hL.mul hR').congr_fderiv (by
    ext v
    simp [denDerivative, π, adjacent, regularPoint, rad_regular, smul_eq_mul]
    <;> field_simp [hne]
    <;> ring)

/-- The six coefficients use the actual frame of output q. -/
def row (x : ℝ) (q : Fin 6) : Covector :=
  (2*x^2) • π (frame q 0) - (x*(x-1)) • adjacent q +
    ((x-1)*(2*x-1)) • π (frame q 3)

private theorem cosine_hasFDerivAt_regular (t : ℝ) (ht : 0 < t) (q : Fin 6) :
    HasFDerivAt (fun l => sourceCosine l q)
      (-(Real.sinh t / ((Real.cosh t+1)*(2*Real.cosh t-1)^2)) •
        row (Real.cosh t) q) (regularPoint t) := by
  have hx : 1 < Real.cosh t := Real.one_lt_cosh.mpr ht.ne'
  have hxp : Real.cosh t+1 ≠ 0 := (show 0 < Real.cosh t+1 by linarith).ne'
  have htwo : 2*Real.cosh t-1 ≠ 0 := (show 0 < 2*Real.cosh t-1 by linarith).ne'
  have hd : sourceDen q (regularPoint t) ≠ 0 := by
    rw [den_regular q t ht]
    exact (R_pos (Real.cosh t) hx).ne'
  have hinv := (hasDerivAt_inv hd).comp_hasFDerivAt (regularPoint t)
    (den_hasFDerivAt_regular t ht q)
  have h := (poly_hasFDerivAt_regular t q).mul hinv
  have heq : (fun l => sourceCosine l q) =
      fun l => sourcePoly q l * (sourceDen q l)⁻¹ := by
    funext l
    simp only [sourceCosine, rawCos, cosine, sourcePoly, sourceDen,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  exact h.congr_fderiv (by
    ext v
    simp [numDerivative, denDerivative, row, π, adjacent,
      poly_regular, den_regular q t ht, smul_eq_mul]
    <;> dsimp only [R, P]
    <;> field_simp [hxp, htwo]
    <;> ring)

/-- A manifestly positive factor without changing the arccos branch. -/
def regularF (t : ℝ) : ℝ :=
  (1 / Real.sqrt (1-(phi (Real.cosh t))^2)) *
    (Real.sinh t / ((Real.cosh t+1)*(2*Real.cosh t-1)^2))

theorem regularF_pos (t : ℝ) (ht : 0 < t) : 0 < regularF t := by
  have hx : 1 < Real.cosh t := Real.one_lt_cosh.mpr ht.ne'
  unfold regularF
  exact mul_pos (one_div_pos.mpr (regular_root_pos t ht))
    (div_pos (Real.sinh_pos_iff.mpr ht)
      (mul_pos (by linarith) (sq_pos_of_pos (by linarith))))

/-- Full Frechet derivative, rather than differentiation along the regular line. -/
theorem sourceAngle_hasFDerivAt_regular (t : ℝ) (ht : 0 < t) (q : Fin 6) :
    HasFDerivAt (fun l => sourceAngle l q)
      (regularF t • row (Real.cosh t) q) (regularPoint t) := by
  have hb := (regular_genuine t ht).2 q
  have h := (Real.hasDerivAt_arccos (ne_of_gt hb.1) (ne_of_lt hb.2)).comp_hasFDerivAt
    (regularPoint t) (cosine_hasFDerivAt_regular t ht q)
  exact h.congr_fderiv (by
    ext v
    simp [regularF, sourceCosine_regular q t ht, smul_eq_mul]
    <;> ring)

/-- Actual Jacobian: output q and independently varying input j. -/
def actualJacobian (l : Lengths) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun q j => fderiv ℝ (fun p => sourceAngle p q) l (Pi.single j 1)

/-- Original opposite pairs are (0,3), (1,4), and (2,5). -/
def B (x : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  let a := 2*x^2
  let b := -x*(x-1)
  let c := (x-1)*(2*x-1)
  !![a,b,b,c,b,b; b,a,b,b,c,b; b,b,a,b,b,c;
     c,b,b,a,b,b; b,c,b,b,a,b; b,b,c,b,b,a]

private theorem row_basis (x : ℝ) (q j : Fin 6) :
    row x q (Pi.single j 1) = B x q j := by
  fin_cases q <;> fin_cases j <;>
    simp [row, π, adjacent, frame, B, smul_eq_mul]
    <;> ring

theorem actualJacobian_regular_entries (t : ℝ) (ht : 0 < t) :
    actualJacobian (regularPoint t) = regularF t • B (Real.cosh t) := by
  ext q j
  simp only [actualJacobian, (sourceAngle_hasFDerivAt_regular t ht q).fderiv,
    ContinuousLinearMap.smul_apply, smul_eq_mul, row_basis, Matrix.smul_apply]

private def Dsum (v : Lengths) : ℝ :=
  (v 0-v 3)^2+(v 1-v 4)^2+(v 2-v 5)^2
private def Esum (v : Lengths) : ℝ :=
  ((v 0+v 3)-(v 1+v 4))^2 + ((v 0+v 3)-(v 2+v 5))^2 +
    ((v 1+v 4)-(v 2+v 5))^2
private def S (v : Lengths) : ℝ := v 0+v 3+(v 1+v 4)+(v 2+v 5)

private theorem B_sos (x : ℝ) (v : Lengths) :
    v ⬝ᵥ (B x *ᵥ v) = (3*x-1)/2 * Dsum v +
      (3*x-1)*(2*x-1)/6 * Esum v + (x+1)/6 * (S v)^2 := by
  simp [B, dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Dsum, Esum, S]
  <;> ring

private theorem B_posDef (x : ℝ) (hx : 1 < x) : (B x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, B]
  · intro v hv
    simp only [star_trivial]
    rw [B_sos]
    have ha : 0 < (3*x-1)/2 := by linarith
    have hx3 : 0 < 3*x-1 := by linarith
    have hx2 : 0 < 2*x-1 := by linarith
    have hb : 0 < (3*x-1)*(2*x-1)/6 := by positivity
    have hc : 0 < (x+1)/6 := by linarith
    have hd : 0 ≤ Dsum v := by unfold Dsum; positivity
    have he : 0 ≤ Esum v := by unfold Esum; positivity
    have hs : 0 ≤ (S v)^2 := sq_nonneg _
    by_contra hn
    have hle := le_of_not_gt hn
    have hd0 : Dsum v ≤ 0 := by
      have hp := mul_nonneg hb.le he
      have hq := mul_nonneg hc.le hs
      have h : (3*x-1)/2 * Dsum v ≤ 0 := by linarith
      exact nonpos_of_mul_nonpos_right h ha
    have he0 : Esum v ≤ 0 := by
      have hp := mul_nonneg ha.le hd
      have hq := mul_nonneg hc.le hs
      have h : (3*x-1)*(2*x-1)/6 * Esum v ≤ 0 := by linarith
      exact nonpos_of_mul_nonpos_right h hb
    have hs0 : (S v)^2 ≤ 0 := by
      have hp := mul_nonneg ha.le hd
      have hq := mul_nonneg hb.le he
      have h : (x+1)/6 * (S v)^2 ≤ 0 := by linarith
      exact nonpos_of_mul_nonpos_right h hc
    have hS : S v = 0 := (sq_nonpos_iff _).mp hs0
    unfold Dsum at hd0
    unfold Esum at he0
    have hd03 : v 0-v 3 = 0 := (sq_nonpos_iff _).mp (by
      nlinarith only [hd0,sq_nonneg (v 1-v 4),sq_nonneg (v 2-v 5)])
    have hd14 : v 1-v 4 = 0 := (sq_nonpos_iff _).mp (by
      nlinarith only [hd0,sq_nonneg (v 0-v 3),sq_nonneg (v 2-v 5)])
    have hd25 : v 2-v 5 = 0 := (sq_nonpos_iff _).mp (by
      nlinarith only [hd0,sq_nonneg (v 0-v 3),sq_nonneg (v 1-v 4)])
    have he01 : (v 0+v 3)-(v 1+v 4) = 0 := (sq_nonpos_iff _).mp (by
      nlinarith only [he0,sq_nonneg ((v 0+v 3)-(v 2+v 5)),sq_nonneg ((v 1+v 4)-(v 2+v 5))])
    have he02 : (v 0+v 3)-(v 2+v 5) = 0 := (sq_nonpos_iff _).mp (by
      nlinarith only [he0,sq_nonneg ((v 0+v 3)-(v 1+v 4)),sq_nonneg ((v 1+v 4)-(v 2+v 5))])
    dsimp only [S] at hS
    have hz0 : v 0 = 0 := by linarith only [hS, hd03, hd14, hd25, he01, he02]
    have hz1 : v 1 = 0 := by linarith only [hz0, hd03, hd14, he01]
    have hz2 : v 2 = 0 := by linarith only [hz0, hd03, hd25, he02]
    have hz3 : v 3 = 0 := by linarith only [hz0, hd03]
    have hz4 : v 4 = 0 := by linarith only [hz1, hd14]
    have hz5 : v 5 = 0 := by linarith only [hz2, hd25]
    apply hv
    funext i
    fin_cases i
    · exact hz0
    · exact hz1
    · exact hz2
    · exact hz3
    · exact hz4
    · exact hz5

/-- Positive definiteness of the actual six-output, six-independent-input Jacobian. -/
theorem actualJacobian_regular_posDef (t : ℝ) (ht : 0 < t) :
    (actualJacobian (regularPoint t)).PosDef := by
  rw [actualJacobian_regular_entries t ht]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · have hB := (B_posDef (Real.cosh t) (Real.one_lt_cosh.mpr ht.ne')).isHermitian
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial] using
      congrArg (fun M => regularF t • M) hB.eq
  · intro v hv
    have hB := (B_posDef (Real.cosh t) (Real.one_lt_cosh.mpr ht.ne')).dotProduct_mulVec_pos hv
    simpa only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] using
      mul_pos (regularF_pos t ht) hB

end CFMPRegularJacobian110Transient

end

run_cmd do
  let name := ``CFMPRegularJacobian110Transient.actualJacobian_regular_posDef
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "REGULAR184: final theorem absent from checked environment"
  let axioms ← Lean.collectAxioms name
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for a in axioms do
    unless allowed.contains a do
      Lean.throwError m!"REGULAR184: forbidden axiom {a}"
  let names := String.intercalate ", " (axioms.toList.mergeSort Lean.Name.lt |>.map toString)
  Lean.logInfo m!"CFMP_REGULAR184 exact_axioms=[{names}]"

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Topology Matrix.Norms.Operator
open Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody (lengthGram)
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
open CFMPGenuineLengthNeighborhood435Transient (genuine genuine_open sourceCosine)
open CFMPOriginalSixPairedAngles435Transient (sourceAngle vertexPerm)
open CFMPOriginalUnitSideCosine435Transient (original_gram_cofactors)
open CFMPNormalizedInverseTangent107
namespace CFMPSourceAngleKernel111

private def delta136 (l : Lengths) : ℝ := -(lengthGram l).det
private def compFirst136 (e : Fin 6) : Fin 4 := vertexPerm e 2
private def compSecond136 (e : Fin 6) : Fin 4 := vertexPerm e 3
private def basis136 (f : Fin 6) : Lengths := Pi.single f 1
private def minor136 (A : Mat) (a b : Fin 4) : ℝ :=
  A a a * A b b - (A a b)^2
private def t136 (A : Mat) (a b p q : Fin 4) : ℝ :=
  A a p * A b q + A a q * A b p - A a b *
    (A a p * A a q / A a a + A b p * A b q / A b b)
private def edgeT136 (A : Mat) (e f : Fin 6) : ℝ :=
  t136 A (compFirst136 e) (compSecond136 e) (edgeFirst f) (edgeSecond f)
private def j136 (l : Lengths) (e f : Fin 6) : ℝ :=
  fderiv ℝ (fun p => sourceAngle p e) l (basis136 f)

private theorem delta136_pos (l : Lengths) (hl : genuine l) : 0 < delta136 l := by
  exact neg_pos.mpr
    (((CFMPGenuineDomain108Transient.genuine_iff_lengthGram_det_neg l).mp hl).2)

private theorem sinh136_pos (l : Lengths) (hl : genuine l) (e : Fin 6) :
    0 < Real.sinh (l e) := Real.sinh_pos_iff.mpr (hl.1 e)

private theorem minor_unit136 (r a b o c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hc : 1 < c) (hd : 1 < d) (hdet : (gram r a b o c d).det < 0) :
    minor136 (gram r a b o c d)⁻¹ 2 3 =
      (r^2 - 1) / (-(gram r a b o c d).det) := by
  let G := gram r a b o c d
  have hi (i j : Fin 4) : G⁻¹ i j = G.adjugate i j / G.det := by
    rw [Matrix.inv_def]
    simp only [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    ring
  have hcof := original_gram_cofactors r a b o c d
  have hid := (original_cosine_interface r a b o c d hr ha hb ho hc hd).2.1
  change D1 r a d * D2 r b c - N r a b o c d ^ 2 =
    -(r^2 - 1) * G.det at hid
  change minor136 G⁻¹ 2 3 = (r^2 - 1) / (-G.det)
  dsimp only [minor136]
  rw [hi, hi, hi, hcof.1, hcof.2.1, hcof.2.2]
  calc
    (-D2 r b c / G.det) * (-D1 r a d / G.det) -
        (N r a b o c d / G.det)^2 =
        (D1 r a d * D2 r b c - N r a b o c d^2) / G.det^2 := by ring
    _ = (-(r^2 - 1) * G.det) / G.det^2 := by rw [hid]
    _ = (r^2 - 1) / (-G.det) := by field_simp [hdet.ne] <;> ring

private theorem complementary_minor136 (l : Lengths) (hl : genuine l) (e : Fin 6) :
    minor136 (lengthGram l)⁻¹ (compFirst136 e) (compSecond136 e) =
      (Real.sinh (l e))^2 / delta136 l := by
  let σ := vertexPerm e
  have hy (k : Fin 6) : 1 < y l σ k := by
    fin_cases k <;> exact Real.one_lt_cosh.mpr (hl.1 _).ne'
  have hdet := (relabeled_domain l hl σ).2.2
  have h := minor_unit136 (y l σ 0) (y l σ 1) (y l σ 2)
    (y l σ 3) (y l σ 4) (y l σ 5)
    (hy 0) (hy 1) (hy 2) (hy 3) (hy 4) (hy 5) hdet
  change minor136 (Q l σ)⁻¹ 2 3 = ((y l σ 0)^2 - 1) / (-(Q l σ).det) at h
  have hroot : y l σ 0 = Real.cosh (l e) := by
    fin_cases e <;> rfl
  have hdetQ : (Q l σ).det = (lengthGram l).det := by
    rw [← relabeled_gram, Matrix.det_submatrix_equiv_self]
  rw [hroot, ← Real.sinh_sq, hdetQ, relabeled_inverse] at h
  simpa only [minor136, Matrix.submatrix_apply, compFirst136,
    compSecond136, delta136, σ] using h

private theorem root_product136_pos (l : Lengths) (hl : genuine l) (a b : Fin 4) :
    0 < Real.sqrt ((lengthGram l)⁻¹ a a) * Real.sqrt ((lengthGram l)⁻¹ b b) :=
  mul_pos (Real.sqrt_pos.mpr (inverse_diagonal_positive l hl a))
    (Real.sqrt_pos.mpr (inverse_diagonal_positive l hl b))

private theorem sine_product136 (l : Lengths) (hl : genuine l) (e : Fin 6) :
    Real.sin (sourceAngle l e) *
      (Real.sqrt ((lengthGram l)⁻¹ (compFirst136 e) (compFirst136 e)) *
       Real.sqrt ((lengthGram l)⁻¹ (compSecond136 e) (compSecond136 e))) =
      Real.sinh (l e) / Real.sqrt (delta136 l) := by
  let A := (lengthGram l)⁻¹
  let k := compFirst136 e
  let m := compSecond136 e
  let R := Real.sqrt (A k k) * Real.sqrt (A m m)
  have hR : 0 < R := root_product136_pos l hl k m
  have hΔ := delta136_pos l hl
  have hs := sinh136_pos l hl e
  have hc := hl.2 e
  have hinside : 0 ≤ 1 - (sourceCosine l e)^2 := by
    have hp : 0 ≤ (1 - sourceCosine l e) * (1 + sourceCosine l e) :=
      mul_nonneg (sub_nonneg.mpr hc.2.le) (by linarith [hc.1])
    nlinarith only [hp]
  have hsin : Real.sin (sourceAngle l e)^2 = 1 - (sourceCosine l e)^2 := by
    rw [sourceAngle, Real.sin_arccos, Real.sq_sqrt hinside]
  have hsinpos : 0 < Real.sin (sourceAngle l e) := by
    exact Real.sin_pos_of_pos_of_lt_pi
      (Real.arccos_pos.mpr hc.2) (Real.arccos_lt_pi.mpr hc.1)
  have hR2 : R^2 = A k k * A m m := by
    dsimp only [R]
    rw [mul_pow, Real.sq_sqrt (inverse_diagonal_positive l hl k).le,
      Real.sq_sqrt (inverse_diagonal_positive l hl m).le]
  have hn : A k m / R = -sourceCosine l e := by
    simpa only [A, k, m, R, compFirst136, compSecond136, normalized_entry] using
      normalized_source_cosine l hl e
  have he : A k m = -sourceCosine l e * R := (div_eq_iff hR.ne').mp hn
  have he2 := congrArg (fun x : ℝ => x^2) he
  have hL2 : (Real.sin (sourceAngle l e) * R)^2 = minor136 A k m := by
    rw [mul_pow, hsin]
    dsimp only [minor136]
    nlinarith [he2, hR2]
  have hM := complementary_minor136 l hl e
  change minor136 A k m = Real.sinh (l e)^2 / delta136 l at hM
  have hright2 : (Real.sinh (l e) / Real.sqrt (delta136 l))^2 =
      Real.sinh (l e)^2 / delta136 l := by
    rw [div_pow, Real.sq_sqrt hΔ.le]
  change Real.sin (sourceAngle l e) * R = _
  apply (sq_eq_sq₀ (mul_pos hsinpos hR).le
    (div_pos hs (Real.sqrt_pos.mpr hΔ)).le).mp
  exact hL2.trans (hM.trans hright2.symm)

private theorem t_adjacent136 (A : Mat) (hA : A.IsSymm)
    (hdiag : ∀ i, A i i ≠ 0) (i k m : Fin 4) :
    t136 A k m i k = A i m / A m m * minor136 A k m := by
  have hmk := hA.apply k m
  have hmi := hA.apply i m
  have hki := hA.apply i k
  dsimp only [t136, minor136]
  rw [hmk, hmi, hki]
  field_simp [hdiag k, hdiag m]
  <;> ring

private theorem t_opposite136 (A : Mat) (hA : A.IsSymm)
    (hdiag : ∀ i, A i i ≠ 0) (k m : Fin 4) :
    t136 A k m k m = minor136 A k m := by
  have hmk := hA.apply k m
  dsimp only [t136, minor136]
  rw [hmk]
  field_simp [hdiag k, hdiag m]
  <;> ring

private theorem adjacent_balance136 (A : Mat) (hA : A.IsSymm)
    (hdiag : ∀ i, A i i ≠ 0) (i j k m : Fin 4) :
    minor136 A j m * t136 A k m i k =
      minor136 A k m * t136 A j m i j := by
  rw [t_adjacent136 A hA hdiag i k m, t_adjacent136 A hA hdiag i j m]
  ring

private theorem opposite_balance136 (A : Mat) (hA : A.IsSymm)
    (hdiag : ∀ i, A i i ≠ 0) (i j k m : Fin 4) :
    minor136 A i j * t136 A k m k m =
      minor136 A k m * t136 A i j i j := by
  rw [t_opposite136 A hA hdiag, t_opposite136 A hA hdiag]
  ring

private theorem finite_edge_balance_ordered136 (A : Mat) (hA : A.IsSymm)
    (hdiag : ∀ i, A i i ≠ 0) (e f : Fin 6) (hef : e.val < f.val) :
    minor136 A (compFirst136 f) (compSecond136 f) * edgeT136 A e f =
      minor136 A (compFirst136 e) (compSecond136 e) * edgeT136 A f e := by
  have h10 := hA.apply 0 1
  have h20 := hA.apply 0 2
  have h30 := hA.apply 0 3
  have h21 := hA.apply 1 2
  have h31 := hA.apply 1 3
  have h32 := hA.apply 2 3
  fin_cases e <;> fin_cases f <;> try omega
  all_goals
    norm_num [minor136, edgeT136, t136, compFirst136, compSecond136,
      vertexPerm, edgeFirst, edgeSecond, h10, h20, h30, h21, h31, h32] <;>
    field_simp [hdiag 0, hdiag 1, hdiag 2, hdiag 3] <;> ring


private theorem finite_edge_balance136 (A : Mat) (hA : A.IsSymm)
    (hdiag : ∀ i, A i i ≠ 0) (e f : Fin 6) :
    minor136 A (compFirst136 f) (compSecond136 f) * edgeT136 A e f =
      minor136 A (compFirst136 e) (compSecond136 e) * edgeT136 A f e := by
  rcases lt_trichotomy e.val f.val with h | h | h
  · exact finite_edge_balance_ordered136 A hA hdiag e f h
  · have hef : e = f := Fin.ext h
    subst f
    rfl
  · exact (finite_edge_balance_ordered136 A hA hdiag f e h).symm

private def pulse136 (p q : Fin 4) : Mat := fun a b =>
  (if a = p then if b = q then 1 else 0 else 0) +
  (if a = q then if b = p then 1 else 0 else 0)

private theorem gramDirection_basis136 (l : Lengths) (f : Fin 6) :
    gramDirection l (basis136 f) =
      -(Real.sinh (l f) • pulse136 (edgeFirst f) (edgeSecond f)) := by
  have hsum : gramDirection l (basis136 f) = -(Real.sinh (l f) • edgeBasis f) := by
    simp [gramDirection, basis136, Pi.single_apply, ite_smul]
  rw [hsum]
  congr 2
  fin_cases f <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [edgeBasis, pulse136, edgeFirst, edgeSecond,
      D5.S3.Geometry.Hyperideal.S4OppositePairAction.edgeIndex]

private theorem inverseVariation_basis136 (l : Lengths) (f : Fin 6) (a b : Fin 4) :
    inverseVariation (lengthGram l) (gramDirection l (basis136 f)) a b =
      Real.sinh (l f) *
        (((lengthGram l)⁻¹ a (edgeFirst f)) * ((lengthGram l)⁻¹ b (edgeSecond f)) +
         ((lengthGram l)⁻¹ a (edgeSecond f)) * ((lengthGram l)⁻¹ b (edgeFirst f))) := by
  rw [gramDirection_basis136]
  have hA := (lengthGram_symmetric l).inv
  have hsum (A : Mat) (p q x z : Fin 4) :
      (A * pulse136 p q * A) x z = A x p * A q z + A x q * A p z := by
    simp [Matrix.mul_apply, pulse136, Finset.sum_add_distrib, Finset.sum_mul,
      Finset.mul_sum, mul_add, add_mul, mul_ite, ite_mul]
  simp only [inverseVariation, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [hsum, hA.apply b (edgeSecond f), hA.apply b (edgeFirst f)]

private theorem normalized_basis_entry136 (l : Lengths) (hl : genuine l)
    (f : Fin 6) (a b : Fin 4) :
    fderiv ℝ normalizedInverse (lengthGram l) (gramDirection l (basis136 f)) a b =
      Real.sinh (l f) /
        (Real.sqrt ((lengthGram l)⁻¹ a a) * Real.sqrt ((lengthGram l)⁻¹ b b)) *
        t136 (lengthGram l)⁻¹ a b (edgeFirst f) (edgeSecond f) := by
  rw [normalizedInverse_fderiv_apply (lengthGram l) _
    (genuine_gram_isUnit l hl) (inverse_diagonal_positive l hl)]
  have ha := inverse_diagonal_positive l hl a
  have hb := inverse_diagonal_positive l hl b
  have hsa := (Real.sqrt_pos.mpr ha).ne'
  have hsb := (Real.sqrt_pos.mpr hb).ne'
  simp only [normalizedTangent, normalScale, correction, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_apply_eq, Matrix.sub_apply]
  rw [inverseVariation_basis136 l f a b, inverseVariation_basis136 l f a a,
    inverseVariation_basis136 l f b b]
  dsimp only [t136]
  field_simp [ha.ne', hb.ne', hsa, hsb]
  <;> ring

private theorem angle_basis_chain136 (l : Lengths) (hl : genuine l) (e f : Fin 6) :
    fderiv ℝ normalizedInverse (lengthGram l) (gramDirection l (basis136 f))
        (compFirst136 e) (compSecond136 e) =
      Real.sin (sourceAngle l e) * j136 l e f := by
  let v := basis136 f
  let Z := fderiv ℝ normalizedInverse (lengthGram l) (gramDirection l v)
  have hline : HasDerivAt (fun s : ℝ => l + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add l
  have hgen : ∀ᶠ s in 𝓝 (0 : ℝ), genuine (l + s • v) :=
    CFMPGenuineLengthNeighborhood435Transient.path_eventually_genuine
      (fun s : ℝ => l + s • v) 0 hline.continuousAt (by simpa using hl)
  have hN : HasDerivAt
      (fun s : ℝ => normalizedInverse (lengthGram (l + s • v))) Z 0 := by
    exact (normalizedInverse_hasFDerivAt (lengthGram l)
      (genuine_gram_isUnit l hl) (inverse_diagonal_positive l hl)).comp_hasDerivAt_of_eq
      0 (lengthGram_line_hasDerivAt l v) (by simp)
  have hentry : HasDerivAt
      (fun s : ℝ => normalizedInverse (lengthGram (l + s • v))
        (compFirst136 e) (compSecond136 e))
      (Z (compFirst136 e) (compSecond136 e)) 0 := by
    convert! (entryCLM (compFirst136 e) (compSecond136 e)).hasFDerivAt.comp_hasDerivAt 0 hN using 1 <;>
      simp only [Function.comp_def, entryCLM, Matrix.entryLinearMap_apply]
  have hθ : HasDerivAt (fun s : ℝ => sourceAngle (l + s • v) e) (j136 l e f) 0 := by
    simpa only [Function.comp_def, j136, v] using
      ((CFMPOriginalGlobalSmoothCovolume103Transient.sourceAngle_smooth l hl e).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hcos : HasDerivAt (fun s : ℝ => -Real.cos (sourceAngle (l + s • v) e))
      (Real.sin (sourceAngle l e) * j136 l e f) 0 := by
    convert! hθ.cos.neg using 1 <;> simp
  have he : (fun s : ℝ => normalizedInverse (lengthGram (l + s • v))
        (compFirst136 e) (compSecond136 e)) =ᶠ[𝓝 0]
      (fun s : ℝ => -Real.cos (sourceAngle (l + s • v) e)) := by
    filter_upwards [hgen] with s hs
    exact normalized_source_angle (l + s • v) hs e
  exact hentry.unique (hcos.congr_of_eventuallyEq he)

private theorem actual_entry_formula136 (l : Lengths) (hl : genuine l) (e f : Fin 6) :
    j136 l e f = Real.sqrt (delta136 l) * Real.sinh (l f) /
      Real.sinh (l e) * edgeT136 (lengthGram l)⁻¹ e f := by
  let R := Real.sqrt ((lengthGram l)⁻¹ (compFirst136 e) (compFirst136 e)) *
    Real.sqrt ((lengthGram l)⁻¹ (compSecond136 e) (compSecond136 e))
  have hR : R ≠ 0 := (root_product136_pos l hl (compFirst136 e) (compSecond136 e)).ne'
  have hΔ := (Real.sqrt_pos.mpr (delta136_pos l hl)).ne'
  have hse := (sinh136_pos l hl e).ne'
  have hN := normalized_basis_entry136 l hl f (compFirst136 e) (compSecond136 e)
  have hchain := angle_basis_chain136 l hl e f
  have hT : Real.sinh (l f) / R * edgeT136 (lengthGram l)⁻¹ e f =
      Real.sin (sourceAngle l e) * j136 l e f := hN.symm.trans hchain
  have hsine := sine_product136 l hl e
  change Real.sin (sourceAngle l e) * R = _ at hsine
  have hmul : Real.sinh (l f) * edgeT136 (lengthGram l)⁻¹ e f =
      (Real.sinh (l e) / Real.sqrt (delta136 l)) * j136 l e f := by
    calc
      _ = (Real.sinh (l f) / R * edgeT136 (lengthGram l)⁻¹ e f) * R := by
        field_simp [hR] <;> ring
      _ = (Real.sin (sourceAngle l e) * j136 l e f) * R := by rw [hT]
      _ = (Real.sin (sourceAngle l e) * R) * j136 l e f := by ring
      _ = _ := by rw [hsine]
  field_simp [hse, hΔ] at hmul ⊢
  <;> nlinarith [hmul]

private theorem actual_entry_symmetric136 (l : Lengths) (hl : genuine l) (e f : Fin 6) :
    j136 l e f = j136 l f e := by
  have hA := (lengthGram_symmetric l).inv
  have hdiag (i : Fin 4) : (lengthGram l)⁻¹ i i ≠ 0 :=
    (inverse_diagonal_positive l hl i).ne'
  have hb := finite_edge_balance136 (lengthGram l)⁻¹ hA hdiag e f
  rw [complementary_minor136 l hl f, complementary_minor136 l hl e] at hb
  have hΔ := (delta136_pos l hl).ne'
  have hse := (sinh136_pos l hl e).ne'
  have hsf := (sinh136_pos l hl f).ne'
  have hm : Real.sinh (l f)^2 * edgeT136 (lengthGram l)⁻¹ e f =
      Real.sinh (l e)^2 * edgeT136 (lengthGram l)⁻¹ f e := by
    field_simp [hΔ] at hb
    exact hb
  rw [actual_entry_formula136 l hl e f, actual_entry_formula136 l hl f e]
  field_simp [hse, hsf]
  <;> linear_combination Real.sqrt (delta136 l) * hm

private theorem actual_matrix_symmetric136 (l : Lengths) (hl : genuine l) :
    Matrix.IsSymm (fun e f : Fin 6 =>
      (fderiv ℝ (fun p : Lengths => fun q => sourceAngle p q) l (basis136 f)) e) := by
  rw [(sourceAngles_hasFDerivAt l hl).fderiv]
  apply Matrix.IsSymm.ext
  intro e f
  change j136 l f e = j136 l e f
  exact actual_entry_symmetric136 l hl f e

private theorem all_directions136 (L : Lengths →L[ℝ] Lengths)
    (hL : Matrix.IsSymm (fun e f : Fin 6 => L (basis136 f) e)) (v w : Lengths) :
    (∑ e, v e * L w e) = ∑ e, w e * L v e := by
  have hdecomp (x : Lengths) : x = ∑ f : Fin 6, x f • basis136 f := by
    ext e
    simp [basis136, Pi.single_apply]
  have hentry (x : Lengths) (e : Fin 6) : L x e = ∑ f : Fin 6, x f * L (basis136 f) e := by
    calc
      L x e = L (∑ f : Fin 6, x f • basis136 f) e := by rw [← hdecomp x]
      _ = _ := by simp [map_sum, map_smul, Finset.sum_apply]
  simp_rw [hentry w, hentry v, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  have h := hL.apply e f
  change L (basis136 e) f = L (basis136 f) e at h
  rw [h]
  ring

example (l : Fin 6 → ℝ) (hl : genuine l) :
    Matrix.IsSymm (fun e f : Fin 6 =>
      (fderiv ℝ (fun p : Fin 6 → ℝ => fun q => sourceAngle p q) l (Pi.single f 1)) e) ∧
    ∀ v w : Fin 6 → ℝ,
      (∑ e, v e * (fderiv ℝ (fun p : Fin 6 → ℝ => fun q => sourceAngle p q) l w) e) =
        ∑ e, w e * (fderiv ℝ (fun p : Fin 6 → ℝ => fun q => sourceAngle p q) l v) e := by
  let hwhole :
      Matrix.IsSymm (fun e f : Fin 6 =>
        (fderiv ℝ (fun p : Fin 6 → ℝ => fun q => sourceAngle p q) l (Pi.single f 1)) e) ∧
      ∀ v w : Fin 6 → ℝ,
        (∑ e, v e * (fderiv ℝ (fun p : Fin 6 → ℝ => fun q => sourceAngle p q) l w) e) =
          ∑ e, w e * (fderiv ℝ (fun p : Fin 6 → ℝ => fun q => sourceAngle p q) l v) e := by
    have hs := actual_matrix_symmetric136 l hl
    refine ⟨hs, ?_⟩
    intro v w
    exact all_directions136 _ hs v w
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let whole ← Lean.Meta.getLocalDeclFromUserName `hwhole
      let some raw := whole.value? |
        Lean.throwError "SOURCE_ANGLE_SYMMETRY136: hwhole must have a visible let value"
      let raw ← Lean.instantiateMVars raw
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let wholeType ← Lean.instantiateMVars whole.type
      if raw.hasMVar || target.hasMVar || wholeType.hasMVar then
        Lean.throwError "SOURCE_ANGLE_SYMMETRY136: unresolved expression or universe metavariables"
      unless ← Lean.Meta.isDefEq wholeType target do
        Lean.throwError "SOURCE_ANGLE_SYMMETRY136: hwhole type differs from the original conclusion"
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType raw) target do
        Lean.throwError "SOURCE_ANGLE_SYMMETRY136: whole proof has the wrong conclusion"
      let originalNames : Array Lean.Name :=
        #[`l, `hl]
      let mut params : Array Lean.Expr := #[]
      for originalName in originalNames do
        let decl ← Lean.Meta.getLocalDeclFromUserName originalName
        if (decl.value? (allowNondep := true)).isSome then
          Lean.throwError m!"SOURCE_ANGLE_SYMMETRY136: original parameter is a local let: {originalName}"
        params := params.push (Lean.mkFVar decl.fvarId)
      unless params.size == 2 do
        Lean.throwError m!"SOURCE_ANGLE_SYMMETRY136: expected original 2 parameters, got {params.size}"
      let proof ← Lean.instantiateMVars (← Lean.Meta.mkLambdaFVars params raw)
      let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let expectedType ← Lean.instantiateMVars (← Lean.Meta.mkForallFVars params target)
      if proof.hasMVar || proofType.hasMVar || expectedType.hasMVar then
        Lean.throwError "SOURCE_ANGLE_SYMMETRY136: closed proof or type still has metavariables"
      if proof.hasFVar || proofType.hasFVar || expectedType.hasFVar then
        Lean.throwError "SOURCE_ANGLE_SYMMETRY136: proof has assumptions beyond the original parameters"
      if proof.hasLooseBVars || proofType.hasLooseBVars || expectedType.hasLooseBVars then
        Lean.throwError "SOURCE_ANGLE_SYMMETRY136: closed proof or type has loose bound variables"
      unless ← Lean.Meta.isDefEq proofType expectedType do
        Lean.throwError "SOURCE_ANGLE_SYMMETRY136: closed proof does not have the original full telescope"
      let mut constants : Lean.NameSet := {}
      for constant in proof.getUsedConstants do
        constants := constants.insert constant
      for constant in proofType.getUsedConstants do
        constants := constants.insert constant
      let env := (← Lean.getEnv).setExporting false
      let mut axioms : Lean.NameSet := {}
      for constant in constants.toArray.qsort Lean.Name.lt do
        if (env.checked.get.find? constant).isNone then
          Lean.throwError m!"SOURCE_ANGLE_SYMMETRY136: constant absent from checked environment: {constant}"
        for axiomName in ← Lean.collectAxioms constant do
          axioms := axioms.insert axiomName
      let axiomNames := axioms.toArray.qsort Lean.Name.lt
      let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
      for axiomName in axiomNames do
        unless allowed.contains axiomName do
          Lean.throwError m!"SOURCE_ANGLE_SYMMETRY136: disallowed axiom dependency: {axiomName}"
      let names := String.intercalate ", " (axiomNames.toList.map toString)
      Lean.logInfo m!"CFMP_SOURCE_ANGLE_SYMMETRY136 exact_axioms=[{names}] constant_count={constants.toArray.size} original_parameter_count={params.size}"
  exact hwhole

end CFMPSourceAngleKernel111
end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open D5.S3.Geometry.Hyperideal.LengthGramBody (lengthGram)
open CFMPGenuineLengthNeighborhood435Transient (genuine)
namespace CFMPGenuineConnected146

abbrev GenuineLengths := {l : Fin 6 → ℝ // genuine l}
abbrev Raw := D5.S3.Geometry.Hyperideal.GramDomainContraction.X

private def fromCosh (x : Raw) : GenuineLengths := by
  let l : Fin 6 → ℝ := fun i => Real.arcosh (x.val i)
  have hcosh (i : Fin 6) : Real.cosh (l i) = x.val i :=
    Real.cosh_arcosh (x.property.1 i).le
  refine ⟨l, (CFMPGenuineDomain108Transient.genuine_iff_lengthGram_det_neg l).mpr
    ⟨fun i => Real.arcosh_pos (x.property.1 i), ?_⟩⟩
  have hd := x.property.2
  change 0 < -(D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram
    (x.val 0) (x.val 1) (x.val 2) (x.val 3) (x.val 4) (x.val 5)).det at hd
  have hG : lengthGram l =
      D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram
        (x.val 0) (x.val 1) (x.val 2) (x.val 3) (x.val 4) (x.val 5) := by
    simp only [lengthGram, hcosh,
      D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram]
  rw [hG]
  exact neg_pos.mp hd

private theorem fromCosh_continuous : Continuous fromCosh := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun x : Raw => Real.arcosh (x.val i))
  exact Real.continuousOn_arcosh.comp_continuous
    ((continuous_apply i).comp continuous_subtype_val)
    (fun x => (x.property.1 i).le)

private theorem fromCosh_surjective : Function.Surjective fromCosh := by
  intro l
  let x : Fin 6 → ℝ := fun i => Real.cosh (l.val i)
  have hx : x ∈ D5.S3.Geometry.Hyperideal.GramDomainContraction.rawDomain := by
    refine ⟨fun i => Real.one_lt_cosh.mpr (l.property.1 i).ne', ?_⟩
    have hd := ((CFMPGenuineDomain108Transient.genuine_iff_lengthGram_det_neg
      l.val).mp l.property).2
    change 0 < -(D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).det
    change (lengthGram l.val).det < 0 at hd
    simpa only [x, lengthGram,
      D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram] using neg_pos.mpr hd
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  funext i
  change Real.arcosh (Real.cosh (l.val i)) = l.val i
  exact Real.arcosh_cosh (l.property.1 i).le

-- UNCOMPILED transient application of the canonical domain contraction.
theorem connected148 : ConnectedSpace GenuineLengths := by
  letI : ContractibleSpace Raw :=
    D5.S3.Geometry.Hyperideal.GramDomainContraction.full_domain_contractible
  exact fromCosh_surjective.connectedSpace fromCosh_continuous

end CFMPGenuineConnected146
end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped MatrixOrder Matrix.Norms.L2Operator
open Filter Topology

-- A temporary application of existing spectral, matrix-order, and connectedness APIs.
-- UNCOMPILED: no parser, kernel, or axiom-closure acceptance has been observed.
private theorem connected_posDef148 {Y n : Type*} [TopologicalSpace Y] [PreconnectedSpace Y]
    [Fintype n] [DecidableEq n]
    (A : Y → Matrix n n ℝ) (hA : Continuous A)
    (hSym : ∀ y, (A y).IsHermitian)
    (hInj : ∀ y, Function.Injective (A y).mulVec)
    (y₀ : Y) (h₀ : (A y₀).PosDef) :
    ∀ y, (A y).PosDef := by
  have hOpen : IsOpen {y : Y | (A y).PosDef} := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hpos : IsStrictlyPositive (A y) := hy.isStrictlyPositive
    have he := (upperHemicontinuous_spectrum ℝ (Matrix n n ℝ)).forall_isOpen
      (A y) (Set.Ioi 0) isOpen_Ioi (by
        intro t ht
        exact hpos.spectrum_pos ht)
    have hes := (hA.tendsto y).eventually he
    filter_upwards [hes] with z hz
    apply Matrix.IsStrictlyPositive.posDef
    exact (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos).mpr
      ⟨(hSym z).isSelfAdjoint, hz⟩
  have hSets : {y : Y | (A y).PosDef} = {y : Y | (A y).PosSemidef} := by
    ext y
    change (A y).PosDef ↔ (A y).PosSemidef
    rw [Matrix.posDef_iff_posSemidef_and_mulVec_injective]
    exact and_iff_left (hInj y)
  have hClosed : IsClosed {y : Y | (A y).PosDef} := by
    rw [hSets]
    exact Matrix.posSemidef_is_closed.preimage hA
  have hWhole : {y : Y | (A y).PosDef} = Set.univ :=
    (show IsClopen {y : Y | (A y).PosDef} from ⟨hClosed, hOpen⟩).eq_univ ⟨y₀, h₀⟩
  intro y
  change y ∈ {y : Y | (A y).PosDef}
  rw [hWhole]
  exact Set.mem_univ y

end


noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped MatrixOrder Matrix.Norms.L2Operator
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPOriginalSixPairedAngles435Transient (sourceAngle)
open CFMPRegularJacobian110Transient (actualJacobian regularPoint)
namespace CFMPActualJacobianPositive148

private theorem actual_matrix148 (l : Fin 6 → ℝ) (hl : genuine l) :
    actualJacobian l = LinearMap.toMatrix'
      (fderiv ℝ (fun p : Fin 6 → ℝ => fun q => sourceAngle p q) l).toLinearMap := by
  ext e f
  change fderiv ℝ (fun p => sourceAngle p e) l (Pi.single f 1) =
    (fderiv ℝ (fun p : Fin 6 → ℝ => fun q => sourceAngle p q) l
      (Pi.single f 1)) e
  rw [(CFMPSourceAngleKernel111.sourceAngles_hasFDerivAt l hl).fderiv]
  rfl

private theorem actual_continuous148 : Continuous
    (fun y : CFMPGenuineConnected146.GenuineLengths => actualJacobian y.val) := by
  apply continuous_pi
  intro e
  apply continuous_pi
  intro f
  apply continuous_iff_continuousAt.mpr
  intro y
  change ContinuousAt (fun z : CFMPGenuineConnected146.GenuineLengths =>
    fderiv ℝ (fun p => sourceAngle p e) z.val (Pi.single f 1)) y
  have hc := (CFMPOriginalGlobalSmoothCovolume103Transient.sourceAngle_smooth
    y.val y.property e).continuousAt_fderiv (by simp)
  exact (hc.clm_apply continuousAt_const).comp continuous_subtype_val.continuousAt

-- Temporary whole-domain application; it adds no positivity or connectivity premise.
theorem actualJacobian_posDef (l : Fin 6 → ℝ) (hl : genuine l) :
    Matrix.PosDef (fun e f : Fin 6 =>
      fderiv ℝ (fun p => sourceAngle p e) l (Pi.single f 1)) := by
  let hwhole : Matrix.PosDef (fun e f : Fin 6 =>
      fderiv ℝ (fun p => sourceAngle p e) l (Pi.single f 1)) := by
    letI : ConnectedSpace CFMPGenuineConnected146.GenuineLengths :=
      CFMPGenuineConnected146.connected148
    let A : CFMPGenuineConnected146.GenuineLengths → Matrix (Fin 6) (Fin 6) ℝ :=
      fun y => actualJacobian y.val
    have hA : Continuous A := actual_continuous148
    have hSym (y : CFMPGenuineConnected146.GenuineLengths) : (A y).IsHermitian := by
      apply Matrix.isHermitian_iff_isSymm.mpr
      change (actualJacobian y.val).IsSymm
      rw [actual_matrix148 y.val y.property]
      change Matrix.IsSymm (fun e f : Fin 6 =>
        (fderiv ℝ (fun p : Fin 6 → ℝ => fun q => sourceAngle p q) y.val
          (Pi.single f 1)) e)
      exact CFMPSourceAngleKernel111.actual_matrix_symmetric136 y.val y.property
    have hInj (y : CFMPGenuineConnected146.GenuineLengths) :
        Function.Injective (A y).mulVec := by
      change Function.Injective (actualJacobian y.val).mulVec
      rw [actual_matrix148 y.val y.property]
      intro v w hvw
      apply CFMPSourceAngleKernel111.sourceAngle_jacobian_injective y.val y.property
      simpa only [LinearMap.toMatrix'_mulVec] using! hvw
    let y₀ : CFMPGenuineConnected146.GenuineLengths :=
      ⟨regularPoint 1, CFMPRegularJacobian110Transient.regular_genuine 1 (by norm_num)⟩
    have h₀ : (A y₀).PosDef :=
      CFMPRegularJacobian110Transient.actualJacobian_regular_posDef 1 (by norm_num)
    exact connected_posDef148 A hA hSym hInj y₀ h₀ ⟨l, hl⟩
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let whole ← Lean.Meta.getLocalDeclFromUserName `hwhole
      let some raw := whole.value? |
        Lean.throwError "ACTUAL_JACOBIAN_POSITIVE148: hwhole must have a visible let value"
      let raw ← Lean.instantiateMVars raw
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let wholeType ← Lean.instantiateMVars whole.type
      if raw.hasMVar || target.hasMVar || wholeType.hasMVar then
        Lean.throwError "ACTUAL_JACOBIAN_POSITIVE148: unresolved expression or universe metavariables"
      unless ← Lean.Meta.isDefEq wholeType target do
        Lean.throwError "ACTUAL_JACOBIAN_POSITIVE148: hwhole type differs from the original conclusion"
      unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType raw) target do
        Lean.throwError "ACTUAL_JACOBIAN_POSITIVE148: whole proof has the wrong conclusion"
      let originalNames : Array Lean.Name :=
        #[`l, `hl]
      let mut params : Array Lean.Expr := #[]
      for originalName in originalNames do
        let decl ← Lean.Meta.getLocalDeclFromUserName originalName
        if (decl.value? (allowNondep := true)).isSome then
          Lean.throwError m!"ACTUAL_JACOBIAN_POSITIVE148: original parameter is a local let: {originalName}"
        params := params.push (Lean.mkFVar decl.fvarId)
      unless params.size == 2 do
        Lean.throwError m!"ACTUAL_JACOBIAN_POSITIVE148: expected original 2 parameters, got {params.size}"
      let proof ← Lean.instantiateMVars (← Lean.Meta.mkLambdaFVars params raw)
      let proofType ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
      let expectedType ← Lean.instantiateMVars (← Lean.Meta.mkForallFVars params target)
      if proof.hasMVar || proofType.hasMVar || expectedType.hasMVar then
        Lean.throwError "ACTUAL_JACOBIAN_POSITIVE148: closed proof or type still has metavariables"
      if proof.hasFVar || proofType.hasFVar || expectedType.hasFVar then
        Lean.throwError "ACTUAL_JACOBIAN_POSITIVE148: proof has assumptions beyond the original parameters"
      if proof.hasLooseBVars || proofType.hasLooseBVars || expectedType.hasLooseBVars then
        Lean.throwError "ACTUAL_JACOBIAN_POSITIVE148: closed proof or type has loose bound variables"
      unless ← Lean.Meta.isDefEq proofType expectedType do
        Lean.throwError "ACTUAL_JACOBIAN_POSITIVE148: closed proof does not have the original full telescope"
      let mut constants : Lean.NameSet := {}
      for constant in proof.getUsedConstants do
        constants := constants.insert constant
      for constant in proofType.getUsedConstants do
        constants := constants.insert constant
      let env := (← Lean.getEnv).setExporting false
      let mut axioms : Lean.NameSet := {}
      for constant in constants.toArray.qsort Lean.Name.lt do
        if (env.checked.get.find? constant).isNone then
          Lean.throwError m!"ACTUAL_JACOBIAN_POSITIVE148: constant absent from checked environment: {constant}"
        for axiomName in ← Lean.collectAxioms constant do
          axioms := axioms.insert axiomName
      let axiomNames := axioms.toArray.qsort Lean.Name.lt
      let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
      for axiomName in axiomNames do
        unless allowed.contains axiomName do
          Lean.throwError m!"ACTUAL_JACOBIAN_POSITIVE148: disallowed axiom dependency: {axiomName}"
      let names := String.intercalate ", " (axiomNames.toList.map toString)
      Lean.logInfo m!"CFMP_ACTUAL_JACOBIAN_POSITIVE148 exact_axioms=[{names}] constant_count={constants.toArray.size} original_parameter_count={params.size}"
  exact hwhole

end CFMPActualJacobianPositive148
end
