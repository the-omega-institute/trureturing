import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorStaticNormal228Transient
import CFMPOriginalBoundaryEdge229Transient
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open CFMPOriginalCellsIndependent435Transient
open CFMPOriginalExteriorFaceChart435Transient
open CFMPOriginalExteriorNativeNormal435Transient

open private endpoint_support from D5.S3.Geometry.Hyperideal.LengthGramSideTrace

namespace CFMPOriginalSupportReadout232Transient

abbrev Space := Fin 4 → ℝ

def supportScale (l : Fin 6 → ℝ) (n : Fin 20) : ℝ :=
  -|(edgeMatrix l n).det| / support l (facet n) (vertices l n 0)

theorem supportScale_pos (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) (n : Fin 20) :
    0 < supportScale l n := by
  exact div_pos_of_neg_of_neg
    (neg_neg_of_pos (abs_pos.mpr (edgeMatrix_det_ne_zero l hl n)))
    (support_at_origin_negative l hl n)

theorem covector_support_readout (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (v : Space) (hv : ∑ j, v j = 1) :
    dotProduct v (exteriorCovector l n) = supportScale l n * support l (facet n) v := by
  let u := ((edgeMatrix l n)⁻¹).mulVec (drop v-drop (vertices l n 0))
  have hm : (edgeMatrix l n).mulVec u = drop v-drop (vertices l n 0) := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (edgeMatrix_det_ne_zero l hl n)), Matrix.one_mulVec]
  have hvdrop : drop v = drop (vertices l n 0) + (edgeMatrix l n).mulVec u := by
    rw [hm]
    module
  have hs := support_coordinates l hl n v hv
  change support l (facet n) v =
    (1-∑ j, u j) * support l (facet n) (vertices l n 0) at hs
  have hne := (support_at_origin_negative l hl n).ne
  rw [exterior_covector_readout l n v hv, hvdrop, dotProduct_add,
    outward_coefficient_mulVec l hl n, hs]
  unfold supportScale planeOffset
  field_simp [hne]
  ring

def normalFactor (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 20) : ℝ :=
  supportScale l n / Real.sqrt (lorentz (raw l M n) (raw l M n))

theorem normalFactor_pos (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 20)
    (hraw : 0 < lorentz (raw l M n) (raw l M n)) :
    0 < normalFactor l M n :=
  div_pos (supportScale_pos l hl n) (Real.sqrt_pos.mpr hraw)

theorem unit_support_readout (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (n : Fin 20) (v : Space) (hv : ∑ j, v j = 1) :
    lorentz (v ᵥ* M) (unit l M n) = normalFactor l M n * support l (facet n) v := by
  have he (X Y : Space) (r : ℝ) : lorentz X (r • Y) = r * lorentz X Y := by
    simp [lorentz, Fin.sum_univ_four, smul_eq_mul]
    ring
  rw [unit, he, pair_raw l M hM n, covector_support_readout l hl n v hv]
  simp only [normalFactor, div_eq_mul_inv]
  ring

-- Reuse the frozen endpoint support signs for the actual labeled vertices.
theorem vertex_support_signs (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (n m : Fin 20) (j : Fin 3)
    (hraw : 0 < lorentz (raw l M m) (raw l M m)) :
    let z := CFMPOriginalBoundaryEdge229Transient.labels n j
    (incident (facet m) z.1 z.2 → lorentz (vertices l n j.succ ᵥ* M) (unit l M m) = 0) ∧
    (¬incident (facet m) z.1 z.2 → lorentz (vertices l n j.succ ᵥ* M) (unit l M m) < 0) := by
  dsimp only
  have hp := endpoint_support l hl (facet m)
    (CFMPOriginalBoundaryEdge229Transient.labels n j).1
    (CFMPOriginalBoundaryEdge229Transient.labels n j).2
    (CFMPOriginalBoundaryEdge229Transient.labels_distinct n j)
  have hz := CFMPOriginalBoundaryEdge229Transient.labels_realize l n j
  rw [hz] at hp
  have hread := unit_support_readout l hl M hM m (vertices l n j.succ)
    (vertex_sum_one l hl n j.succ)
  rw [hread]
  constructor
  · intro h
    rw [hp.1 h, mul_zero]
  · intro h
    exact mul_neg_of_pos_of_neg (normalFactor_pos l hl M m hraw) (hp.2 h)

end CFMPOriginalSupportReadout232Transient
