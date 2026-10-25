import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalFaceBridge435V2Transient
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Temporary exact charts for the original twenty exterior triangles. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped Matrix BigOperators ENNReal
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicPlaneRealization
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalCellsIndependent435Transient
open CFMPReflectedPlaneChart435Transient
open CFMPReflectedCoefficientSection435Transient
open CFMPActualPlaneBranch435Transient
open CFMPActualPlaneIsometry435Transient
open CFMPActualTriangleNormal435Transient

namespace CFMPOriginalExteriorFaceChart435Transient

abbrev parameterTriangle := CFMPOriginalInternalFaceBridge435V2Transient.parameterTriangle

def base (l : Fin 6 → ℝ) (n : Fin 20) : Coeff := vertices l n 1

def direction (l : Fin 6 → ℝ) (n : Fin 20) (j : Fin 2) : Coeff :=
  vertices l n (j.succ.succ) - base l n

def xi (l : Fin 6 → ℝ) (n : Fin 20) (q : E) : Coeff :=
  base l n + q 0 • direction l n 0 + q 1 • direction l n 1

theorem xi_vertex_values (l : Fin 6 → ℝ) (n : Fin 20) :
    xi l n 0 = vertices l n 1 ∧
    xi l n ![1,0] = vertices l n 2 ∧
    xi l n ![0,1] = vertices l n 3 := by
  simp [xi,base,direction] <;> module

theorem boundaryTriangle_subset_cutBody (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) : boundaryTriangle l n ⊆ cutBody l := by
  unfold boundaryTriangle
  apply convexHull_min
  · rintro x ⟨j,rfl⟩
    exact CFMPOriginalInternalFaceBridge435V2Transient.vertex_mem_cutBody l hl n j.succ
  · rw [← (cut_body_polytope l hl).2.1]
    exact convex_convexHull ℝ _

theorem xi_mem_boundaryTriangle (l : Fin 6 → ℝ) (n : Fin 20)
    (q : E) (hq : q ∈ parameterTriangle) : xi l n q ∈ boundaryTriangle l n := by
  let w : Fin 3 → ℝ := ![1 - q 0 - q 1,q 0,q 1]
  have hw : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w j := by
    intro j _
    rcases hq with ⟨h0,h1,h01⟩
    fin_cases j <;> simp [w] <;> linarith
  have hsum : ∑ j ∈ (Finset.univ : Finset (Fin 3)), w j = 1 := by
    simp [w,Fin.sum_univ_three] <;> ring
  have hp : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      vertices l n j.succ ∈ boundaryTriangle l n := by
    intro j _
    exact subset_convexHull ℝ _ ⟨j,rfl⟩
  have hconv : Convex ℝ (boundaryTriangle l n) := convex_convexHull ℝ _
  have hm := hconv.sum_mem hw hsum hp
  convert hm using 1
  ext k
  simp [xi,direction,base,w,Fin.sum_univ_three,smul_eq_mul] <;> ring

theorem xi_mem_cutBody (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (q : E) (hq : q ∈ parameterTriangle) : xi l n q ∈ cutBody l :=
  boundaryTriangle_subset_cutBody l hl n (xi_mem_boundaryTriangle l n q hq)

theorem section_sums (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) (n : Fin 20) :
    (∑ k, base l n k) = 1 ∧
    (∑ k, direction l n 0 k) = 0 ∧
    (∑ k, direction l n 1 k) = 0 := by
  simp [base,direction,Finset.sum_sub_distrib,vertex_sum_one l hl]

theorem tangent_injective (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) (n : Fin 20) :
    Function.Injective (fun q : E => q 0 • direction l n 0 + q 1 • direction l n 1) := by
  have hi := (affineIndependent_iff_linearIndependent_vsub ℝ
    (vertices l n) (1 : Fin 4)).mp (original_cells_independent l hl n)
  let e : Fin 2 ↪ {j : Fin 4 // j ≠ 1} :=
    ⟨fun j => ⟨j.succ.succ,by fin_cases j <;> decide⟩,
      fun j k h => Fin.succ_injective 2
        (Fin.succ_injective 3 (congrArg Subtype.val h))⟩
  have hc : LinearIndependent ℝ (direction l n) := hi.comp e e.injective
  intro q r h
  apply hc.fintypeLinearCombination_injective
  simpa [Fintype.linearCombination_apply,Fin.sum_univ_two] using h

theorem exterior_vertices_support (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (j : Fin 3) :
    support l (facet n) (vertices l n j.succ) = 0 := by
  fin_cases n <;> fin_cases j
  · change support l (Sum.inr 0) (endpoint l 0 1) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 0) (endpoint l 0 2) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 0) (endpoint l 0 3) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 0 3 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 1) (endpoint l 1 0) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 1 0 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 1) (endpoint l 1 2) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 1) (endpoint l 1 3) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 2) (endpoint l 2 0) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 2) (endpoint l 2 1) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 2) (endpoint l 2 3) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 3) (endpoint l 3 0) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 3) (endpoint l 3 1) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.2.1
  · change support l (Sum.inr 3) (endpoint l 3 2) = 0
    simpa [support] using ((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.2.1
  · change support l (Sum.inl 0) (endpoint l 1 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 2 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 2 3) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 1 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 2 3) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 3 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 1 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 3 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 3 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 1 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 3 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 0) (endpoint l 1 3) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.1 0 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 0 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 2 0) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 2 3) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 0 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 2 3) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 2 3 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 3 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 0 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 3 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 3 0) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 0 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 3 0) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 1) (endpoint l 0 3) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 3 (by decide)).2.2.2.1 1 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 0 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 1 0) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 0 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 1 3) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 0 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 1 3) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 3 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 3 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 0 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 3 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 3 0) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 0 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 3 0) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 3 0 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 2) (endpoint l 0 3) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 3 (by decide)).2.2.2.1 2 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 0 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 1 0) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 0 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 1 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 0 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 1 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 1 2 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 2 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 0 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 2 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 2 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 2 0) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 0 1) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 1 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 2 0) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 2 0 (by decide)).2.2.2.1 3 (by decide) (by decide))
  · change support l (Sum.inl 3) (endpoint l 0 2) = 0
    simpa [support] using congrArg Neg.neg
      (((cut_body_polytope l hl).2.2.2 0 2 (by decide)).2.2.2.1 3 (by decide) (by decide))

theorem xi_support (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (q : E) : support l (facet n) (xi l n q) = 0 := by
  have h0 := exterior_vertices_support l hl n 0
  have h1 := exterior_vertices_support l hl n 1
  have h2 := exterior_vertices_support l hl n 2
  change support l (facet n) (vertices l n 1) = 0 at h0
  change support l (facet n) (vertices l n 2) = 0 at h1
  change support l (facet n) (vertices l n 3) = 0 at h2
  simp [xi,base,direction,map_add,map_smul,map_sub,h0,h1,h2]

theorem all_exterior_face_prerequisites (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : M4) (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Coeff, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) :
    (∀ q ∈ parameterTriangle, xi l n q ∈ cutBody l) ∧
      Function.Injective (fun q : E =>
        q 0 • direction l n 0 + q 1 • direction l n 1) ∧
      (∑ k, base l n k) = 1 ∧
      (∑ k, direction l n 0 k) = 0 ∧
      (∑ k, direction l n 1 k) = 0 ∧
      (∀ q ∈ parameterTriangle,
        lorentz (xi l n q ᵥ* M) (xi l n q ᵥ* M) < 0 ∧
          0 < (xi l n q ᵥ* M) 3 ∧
          0 < (xi l n q ᵥ* M) 3 - (xi l n q ᵥ* M) 2) := by
  obtain ⟨ha,hb,hc⟩ := section_sums l hl n
  refine ⟨xi_mem_cutBody l hl n, tangent_injective l hl n, ha,hb,hc,?_⟩
  intro q hq
  exact CFMPOriginalInternalFaceBridge435V2Transient.body_future_data l hl M hG f hf ⟨xi l n q, xi_mem_cutBody l hl n q hq⟩

theorem same_reflection_chart_data (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : M4) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Coeff, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) :
    ∃ A : Coeff, ∃ hA : 0 < lorentz A A,
      Isometry (fun z => reflectionNative A hA (vertical z)) ∧
      (∀ q : E, reflectionLinear A (xi l n q ᵥ* M) 1 = 0) ∧
      sectionMap M (reflectionLinear A) (forward M (reflectionLinear A) (base l n)) = 1 ∧
      (∀ j, sectionMap M (reflectionLinear A)
        ((reflectedTangents M (reflectionLinear A)
          (direction l n 0) (direction l n 1)).col j) = 0) ∧
      (CFMPReflectedPlaneChart435Transient.augmented
        (reflectedTangents M (reflectionLinear A) (direction l n 0) (direction l n 1))
        (forward M (reflectionLinear A) (base l n))).det ≠ 0 ∧
      Function.Injective (reflectedTangents M (reflectionLinear A)
        (direction l n 0) (direction l n 1)).mulVec ∧
      (∀ q ∈ parameterTriangle,
        0 < radius (affine (forward M (reflectionLinear A) (base l n))
          (reflectedTangents M (reflectionLinear A)
            (direction l n 0) (direction l n 1)) q) ∧
        0 < delta (affine (forward M (reflectionLinear A) (base l n))
          (reflectedTangents M (reflectionLinear A)
            (direction l n 0) (direction l n 1)) q)) ∧
      (∀ (q : E) (hq : q ∈ parameterTriangle), ∃ z : UpperHalfPlane,
        z.re = reflectionLinear A (xi l n q ᵥ* M) 0 /
          (reflectionLinear A (xi l n q ᵥ* M) 3 -
            reflectionLinear A (xi l n q ᵥ* M) 2) ∧
        z.im = Real.sqrt (-lorentz (xi l n q ᵥ* M) (xi l n q ᵥ* M)) /
          (reflectionLinear A (xi l n q ᵥ* M) 3 -
            reflectionLinear A (xi l n q ᵥ* M) 2) ∧
        reflectionNative A hA (vertical z) =
          f ⟨xi l n q, xi_mem_cutBody l hl n q hq⟩) := by
  obtain ⟨hm,htan,ha,hb,hc,hfuture⟩ :=
    all_exterior_face_prerequisites l hl M hG f hf n
  have hzero : (0 : E) ∈ parameterTriangle := by
    norm_num [parameterTriangle,CFMPOriginalInternalFaceBridge435V2Transient.parameterTriangle]
  obtain ⟨A,hA,he,hplane,hs,hcols,hdet⟩ := same_A_section_and_isometry M hM
    (base l n) (direction l n 0) (direction l n 1) 0
    (hfuture 0 hzero).1 ha hb hc htan
  have hR : Function.Involutive (reflectionLinear A) := by
    intro X
    simpa only [reflectionLinear_apply] using reflection_involutive A hA.ne' X
  have hbase : reflectionLinear A (base l n ᵥ* M) 1 = 0 := by
    simpa using hplane 0
  have hbplane : reflectionLinear A (direction l n 0 ᵥ* M) 1 = 0 := by
    have h := hplane ![1,0]
    simpa [Matrix.add_vecMul, Matrix.smul_vecMul, map_add, map_smul, hbase] using h
  have hcplane : reflectionLinear A (direction l n 1 ᵥ* M) 1 = 0 := by
    have h := hplane ![0,1]
    simpa [Matrix.add_vecMul, Matrix.smul_vecMul, map_add, map_smul, hbase] using h
  have hpair : ∀ X Y, lorentz (reflectionLinear A X) (reflectionLinear A Y) =
      lorentz X Y := by
    intro X Y
    simpa only [reflectionLinear_apply] using reflection_pair A X Y hA.ne'
  refine ⟨A,hA,he,hplane,hs,hcols,hdet,reflected_tangents_injective M (reflectionLinear A)
    hM hR _ _ hbplane hcplane htan,?_,?_⟩
  · intro q hq
    have hqd := hfuture q hq
    have hp : reflectionLinear A (xi l n q ᵥ* M) 1 = 0 := hplane q
    rw [affine_forward]
    constructor
    · change 0 < radius (forward M (reflectionLinear A) (xi l n q))
      rw [actual_radius M (reflectionLinear A) hpair _ hp]
      exact neg_pos.mpr hqd.1
    · change 0 < reflectionLinear A (xi l n q ᵥ* M) 3 -
        reflectionLinear A (xi l n q ᵥ* M) 2
      exact reflection_den_pos A _ hA hqd.1 hqd.2.2
  · intro q hq
    have hqd := hfuture q hq
    exact same_original_point A (xi l n q ᵥ* M) hA hqd.1 hqd.2.2 (hplane q)
      (f ⟨xi l n q,hm q hq⟩)
      (original_frame_normalized_lift l M hG f hf ⟨xi l n q,hm q hq⟩)


-- The exterior coefficient plane has a nonzero offset from the original barycenter.
def outwardCoefficient (l : Fin 6 → ℝ) (n : Fin 20) : Fin 3 → ℝ :=
  |(edgeMatrix l n).det| • ((edgeMatrix l n)⁻¹).transpose.mulVec (fun _ => 1)

def planeOffset (l : Fin 6 → ℝ) (n : Fin 20) : ℝ :=
  dotProduct (outwardCoefficient l n) (drop (vertices l n 0)) + |(edgeMatrix l n).det|

-- This affine covector replaces the internally centered covector for an exterior face.
def exteriorCovector (l : Fin 6 → ℝ) (n : Fin 20) : Coeff :=
  let a := outwardCoefficient l n
  let h := planeOffset l n
  ![a 0-h,a 1-h,a 2-h,-h]

theorem outward_coefficient_mulVec (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (u : Fin 3 → ℝ) :
    dotProduct (outwardCoefficient l n) ((edgeMatrix l n).mulVec u) =
      |(edgeMatrix l n).det| * ∑ j, u j := by
  have hd := edgeMatrix_det_ne_zero l hl n
  rw [outwardCoefficient,smul_dotProduct,dotProduct_comm,
    Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec]
  simp [dotProduct,Fin.sum_univ_three]

theorem drop_xi (l : Fin 6 → ℝ) (n : Fin 20) (q : E) :
    drop (xi l n q) = drop (vertices l n 0) +
      (edgeMatrix l n).mulVec ![1-q 0-q 1,q 0,q 1] := by
  ext j
  simp [drop,xi,base,direction,edgeMatrix,Matrix.mulVec,dotProduct,
    Fin.sum_univ_three,smul_eq_mul] <;> ring

theorem exterior_plane_readout (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (q : E) :
    dotProduct (outwardCoefficient l n) (drop (xi l n q)) = planeOffset l n := by
  have hs : (∑ j : Fin 3, (![1-q 0-q 1,q 0,q 1] : Fin 3 → ℝ) j) = 1 := by
    simp [Fin.sum_univ_three] <;> ring
  rw [drop_xi,dotProduct_add,outward_coefficient_mulVec l hl n,hs,mul_one] <;> rfl

theorem original_cell_halfspace (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (u : Fin 3 → ℝ) (hu : ∑ j, u j ≤ 1) :
    dotProduct (outwardCoefficient l n)
        (drop (vertices l n 0) + (edgeMatrix l n).mulVec u) ≤ planeOffset l n := by
  rw [dotProduct_add,outward_coefficient_mulVec l hl n]
  have h := mul_le_mul_of_nonneg_left hu (abs_nonneg (edgeMatrix l n).det)
  simpa only [mul_one,planeOffset,add_comm] using add_le_add_left h
    (dotProduct (outwardCoefficient l n) (drop (vertices l n 0)))

theorem barycenter_strict_inward (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) :
    dotProduct (outwardCoefficient l n) (drop (vertices l n 0)) < planeOffset l n := by
  have hd : 0 < |(edgeMatrix l n).det| := abs_pos.mpr (edgeMatrix_det_ne_zero l hl n)
  unfold planeOffset
  linarith

theorem exterior_covector_readout (l : Fin 6 → ℝ) (n : Fin 20)
    (v : Coeff) (hv : ∑ j, v j = 1) :
    dotProduct v (exteriorCovector l n) =
      dotProduct (outwardCoefficient l n) (drop v) - planeOffset l n := by
  have hs : v 0+v 1+v 2+v 3 = 1 := by simpa [Fin.sum_univ_four] using hv
  have hh : planeOffset l n * (v 0+v 1+v 2+v 3) = planeOffset l n := by
    rw [hs,mul_one]
  simp only [exteriorCovector,dotProduct,drop,Fin.sum_univ_four,Fin.sum_univ_three,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Matrix.head_cons]
  change v 0 * (outwardCoefficient l n 0-planeOffset l n) +
    v 1 * (outwardCoefficient l n 1-planeOffset l n) +
    v 2 * (outwardCoefficient l n 2-planeOffset l n) + v 3 * -planeOffset l n =
    outwardCoefficient l n 0 * v 0 + outwardCoefficient l n 1 * v 1 +
      outwardCoefficient l n 2 * v 2 - planeOffset l n
  nlinarith only [hh]

#print axioms same_reflection_chart_data
#print axioms exterior_plane_readout
end CFMPOriginalExteriorFaceChart435Transient
