import D5.S3.Geometry.Hyperideal.CFMPOriginalCellsIndependent435Transient
import D5.S3.Geometry.Hyperideal.CFMPActualPlaneIsometry435Transient
import D5.S3.Geometry.Hyperideal.CFMPNativePlaneArea435Transient
import Mathlib.Analysis.Convex.Combination

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

namespace CFMPOriginalInternalFaceBridge435V2Transient

def parameterTriangle : Set E := {q | 0 ≤ q 0 ∧ 0 ≤ q 1 ∧ q 0 + q 1 ≤ 1}

def base (l : Fin 6 → ℝ) (n : Fin 20) : Coeff := vertices l n 0

def direction (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3) (j : Fin 2) : Coeff :=
  vertices l n (i.succAbove j).succ - base l n

def xi (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3) (q : E) : Coeff :=
  base l n + q 0 • direction l n i 0 + q 1 • direction l n i 1

theorem vertex_mem_cutBody (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (j : Fin 4) : vertices l n j ∈ cutBody l := by
  fin_cases n <;> fin_cases j
  all_goals first
    | exact (shared_radial_body l hl).2.1
    | exact ((cut_body_polytope l hl).2.2.2 _ _ (by decide)).1

theorem xi_mem_cutBody (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 3) (q : E) (hq : q ∈ parameterTriangle) :
    xi l n i q ∈ cutBody l := by
  have hconv : Convex ℝ (cutBody l) := by
    rw [← (cut_body_polytope l hl).2.1]
    exact convex_convexHull ℝ _
  let w : Fin 3 → ℝ := ![1 - q 0 - q 1, q 0, q 1]
  let p : Fin 3 → Coeff :=
    ![base l n, vertices l n (i.succAbove 0).succ,
      vertices l n (i.succAbove 1).succ]
  have hw : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w j := by
    intro j _
    rcases hq with ⟨h0,h1,h01⟩
    fin_cases j <;> simp [w] <;> linarith
  have hsum : ∑ j ∈ (Finset.univ : Finset (Fin 3)), w j = 1 := by
    simp [w, Fin.sum_univ_three] <;> ring
  have hp : ∀ j ∈ (Finset.univ : Finset (Fin 3)), p j ∈ cutBody l := by
    intro j _
    fin_cases j <;> exact vertex_mem_cutBody l hl n _
  have hm := hconv.sum_mem hw hsum hp
  convert hm using 1
  ext k
  simp [xi, direction, p, w, base, Fin.sum_univ_three, smul_eq_mul] <;> ring

theorem section_sums (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 3) :
    (∑ k, base l n k) = 1 ∧
      (∑ k, direction l n i 0 k) = 0 ∧
      (∑ k, direction l n i 1 k) = 0 := by
  simp [base, direction, Finset.sum_sub_distrib, vertex_sum_one l hl]

theorem tangent_injective (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 3) :
    Function.Injective (fun q : E =>
      q 0 • direction l n i 0 + q 1 • direction l n i 1) := by
  have hi := (affineIndependent_iff_linearIndependent_vsub ℝ
    (vertices l n) (0 : Fin 4)).mp (original_cells_independent l hl n)
  let e : Fin 2 ↪ {j : Fin 4 // j ≠ 0} :=
    ⟨fun j => ⟨(i.succAbove j).succ, Fin.succ_ne_zero _⟩,
      fun j k h => Fin.succAbove_right_injective (p := i)
        (Fin.succ_injective 3 (congrArg Subtype.val h))⟩
  have hc : LinearIndependent ℝ (direction l n i) := hi.comp e e.injective
  intro q r h
  apply hc.fintypeLinearCombination_injective
  simpa [Fintype.linearCombination_apply, Fin.sum_univ_two] using h

theorem xi_quadratic_negative (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 3) (q : E) (hq : q ∈ parameterTriangle) :
    gramQuadratic l (xi l n i q) < 0 :=
  (shared_radial_body l hl).2.2.2.1 _ (xi_mem_cutBody l hl n i q hq)

theorem body_future_data (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : M4) (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Coeff, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (w : cutBody l) :
    lorentz (w.val ᵥ* M) (w.val ᵥ* M) < 0 ∧
      0 < (w.val ᵥ* M) 3 ∧ 0 < (w.val ᵥ* M) 3 - (w.val ᵥ* M) 2 := by
  have hu : lorentz (w.val ᵥ* M) (w.val ᵥ* M) < 0 := by
    rw [frame_quadratic l M hG]
    exact (shared_radial_body l hl).2.2.2.1 w.val w.property
  have hs : 0 < Real.sqrt (-lorentz (w.val ᵥ* M) (w.val ᵥ* M)) :=
    Real.sqrt_pos.mpr (neg_pos.mpr hu)
  have ht := lift_time (f w)
  rw [original_frame_normalized_lift l M hG f hf w] at ht
  change 0 < (Real.sqrt (-lorentz (w.val ᵥ* M) (w.val ᵥ* M)))⁻¹ *
    (w.val ᵥ* M) 3 at ht
  have htime : 0 < (w.val ᵥ* M) 3 :=
    pos_of_mul_pos_right ht (inv_pos.mpr hs).le
  exact ⟨hu, htime, den_pos_of_time _ hu htime⟩

theorem all_internal_face_prerequisites (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : M4) (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Coeff, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) :
    (∀ q ∈ parameterTriangle, xi l n i q ∈ cutBody l) ∧
      Function.Injective (fun q : E =>
        q 0 • direction l n i 0 + q 1 • direction l n i 1) ∧
      (∑ k, base l n k) = 1 ∧
      (∑ k, direction l n i 0 k) = 0 ∧
      (∑ k, direction l n i 1 k) = 0 ∧
      (∀ q ∈ parameterTriangle,
        lorentz (xi l n i q ᵥ* M) (xi l n i q ᵥ* M) < 0 ∧
          0 < (xi l n i q ᵥ* M) 3 ∧
          0 < (xi l n i q ᵥ* M) 3 - (xi l n i q ᵥ* M) 2) := by
  obtain ⟨ha,hb,hc⟩ := section_sums l hl n i
  refine ⟨xi_mem_cutBody l hl n i, tangent_injective l hl n i, ha,hb,hc,?_⟩
  intro q hq
  exact body_future_data l hl M hG f hf ⟨xi l n i q, xi_mem_cutBody l hl n i q hq⟩

theorem same_reflection_chart_data (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : M4) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Coeff, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) :
    ∃ A : Coeff, ∃ hA : 0 < lorentz A A,
      Isometry (fun z => reflectionNative A hA (vertical z)) ∧
      (∀ q : E, reflectionLinear A (xi l n i q ᵥ* M) 1 = 0) ∧
      sectionMap M (reflectionLinear A) (forward M (reflectionLinear A) (base l n)) = 1 ∧
      (∀ j, sectionMap M (reflectionLinear A)
        ((reflectedTangents M (reflectionLinear A)
          (direction l n i 0) (direction l n i 1)).col j) = 0) ∧
      Function.Injective (reflectedTangents M (reflectionLinear A)
        (direction l n i 0) (direction l n i 1)).mulVec ∧
      (∀ q ∈ parameterTriangle,
        0 < radius (affine (forward M (reflectionLinear A) (base l n))
          (reflectedTangents M (reflectionLinear A)
            (direction l n i 0) (direction l n i 1)) q) ∧
        0 < delta (affine (forward M (reflectionLinear A) (base l n))
          (reflectedTangents M (reflectionLinear A)
            (direction l n i 0) (direction l n i 1)) q)) ∧
      (∀ (q : E) (hq : q ∈ parameterTriangle), ∃ z : UpperHalfPlane,
        z.re = reflectionLinear A (xi l n i q ᵥ* M) 0 /
          (reflectionLinear A (xi l n i q ᵥ* M) 3 -
            reflectionLinear A (xi l n i q ᵥ* M) 2) ∧
        z.im = Real.sqrt (-lorentz (xi l n i q ᵥ* M) (xi l n i q ᵥ* M)) /
          (reflectionLinear A (xi l n i q ᵥ* M) 3 -
            reflectionLinear A (xi l n i q ᵥ* M) 2) ∧
        reflectionNative A hA (vertical z) =
          f ⟨xi l n i q, xi_mem_cutBody l hl n i q hq⟩) := by
  obtain ⟨hm,htan,ha,hb,hc,hfuture⟩ :=
    all_internal_face_prerequisites l hl M hG f hf n i
  have hzero : (0 : E) ∈ parameterTriangle := by norm_num [parameterTriangle]
  obtain ⟨A,hA,he,hplane,hs,hcols,hdet⟩ := same_A_section_and_isometry M hM
    (base l n) (direction l n i 0) (direction l n i 1) 0
    (hfuture 0 hzero).1 ha hb hc htan
  have hR : Function.Involutive (reflectionLinear A) := by
    intro X
    simpa only [reflectionLinear_apply] using reflection_involutive A hA.ne' X
  have hbase : reflectionLinear A (base l n ᵥ* M) 1 = 0 := by
    simpa using hplane 0
  have hbplane : reflectionLinear A (direction l n i 0 ᵥ* M) 1 = 0 := by
    have h := hplane ![1,0]
    simpa [Matrix.add_vecMul, Matrix.smul_vecMul, map_add, map_smul, hbase] using h
  have hcplane : reflectionLinear A (direction l n i 1 ᵥ* M) 1 = 0 := by
    have h := hplane ![0,1]
    simpa [Matrix.add_vecMul, Matrix.smul_vecMul, map_add, map_smul, hbase] using h
  have hpair : ∀ X Y, lorentz (reflectionLinear A X) (reflectionLinear A Y) =
      lorentz X Y := by
    intro X Y
    simpa only [reflectionLinear_apply] using reflection_pair A X Y hA.ne'
  refine ⟨A,hA,he,hplane,hs,hcols,reflected_tangents_injective M (reflectionLinear A)
    hM hR _ _ hbplane hcplane htan,?_,?_⟩
  · intro q hq
    have hqd := hfuture q hq
    have hp : reflectionLinear A (xi l n i q ᵥ* M) 1 = 0 := hplane q
    rw [affine_forward]
    constructor
    · change 0 < radius (forward M (reflectionLinear A) (xi l n i q))
      rw [actual_radius M (reflectionLinear A) hpair _ hp]
      exact neg_pos.mpr hqd.1
    · change 0 < reflectionLinear A (xi l n i q ᵥ* M) 3 -
        reflectionLinear A (xi l n i q ᵥ* M) 2
      exact reflection_den_pos A _ hA hqd.1 hqd.2.2
  · intro q hq
    have hqd := hfuture q hq
    exact same_original_point A (xi l n i q ᵥ* M) hA hqd.1 hqd.2.2 (hplane q)
      (f ⟨xi l n i q,hm q hq⟩)
      (original_frame_normalized_lift l M hG f hf ⟨xi l n i q,hm q hq⟩)

end CFMPOriginalInternalFaceBridge435V2Transient
