import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorFaceChart435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalNormals435Transient

/-! Temporary actual offset normals for the twenty original exterior triangles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped Matrix BigOperators Topology
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPOriginalCellsIndependent435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePullbackBridge435Transient
open CFMPNativePlaneNormal435Transient
open CFMPNativeNormalCoorientation435Transient
open CFMPActualTriangleNormal435Transient
open CFMPOriginalExteriorFaceChart435Transient

namespace CFMPOriginalExteriorNativeNormal435Transient

def raw (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 20) : W :=
  let z := M⁻¹ *ᵥ exteriorCovector l n
  ![z 0,z 1,z 2,-z 3]

def unit (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 20) : W :=
  (Real.sqrt (lorentz (raw l M n) (raw l M n)))⁻¹ • raw l M n

theorem pair_raw (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : M.det ≠ 0) (n : Fin 20) (v : W) :
    lorentz (v ᵥ* M) (raw l M n) = dotProduct v (exteriorCovector l n) := by
  calc
    _ = dotProduct (v ᵥ* M) (M⁻¹ *ᵥ exteriorCovector l n) := by
      simp [raw,lorentz,dotProduct,Fin.sum_univ_four]
    _ = dotProduct v ((M * M⁻¹) *ᵥ exteriorCovector l n) := by
      simp only [Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul]
    _ = _ := by rw [Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]

theorem xi_sum_one (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (q : Fin 2 → ℝ) : ∑ k, xi l n q k = 1 := by
  obtain ⟨ha,hb,hc⟩ := section_sums l hl n
  simp only [xi,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,ha,hb,hc,mul_zero,add_zero]

theorem face_readout (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (q : Fin 2 → ℝ) :
    dotProduct (xi l n q) (exteriorCovector l n) = 0 := by
  rw [exterior_covector_readout l n _ (xi_sum_one l hl n q),
    exterior_plane_readout l hl n q,sub_self]

theorem vertex_readout (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (j : Fin 4) :
    dotProduct (vertices l n j) (exteriorCovector l n) =
      if j = 0 then -|(edgeMatrix l n).det| else 0 := by
  cases j using Fin.cases with
  | zero =>
    rw [exterior_covector_readout l n _ (vertex_sum_one l hl n 0)]
    simp [planeOffset] <;> ring
  | succ j =>
    simp only [if_neg (Fin.succ_ne_zero j)]
    fin_cases j
    · change dotProduct (vertices l n 1) (exteriorCovector l n) = 0
      simpa only [(xi_vertex_values l n).1] using face_readout l hl n 0
    · change dotProduct (vertices l n 2) (exteriorCovector l n) = 0
      simpa only [(xi_vertex_values l n).2.1] using face_readout l hl n ![1,0]
    · change dotProduct (vertices l n 3) (exteriorCovector l n) = 0
      simpa only [(xi_vertex_values l n).2.2] using face_readout l hl n ![0,1]

theorem support_at_origin_negative (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) : support l (facet n) (vertices l n 0) < 0 := by
  have ho : vertices l n 0 = barycenter := by fin_cases n <;> rfl
  rw [ho]
  cases hf : facet n with
  | inl k => norm_num [support,barycenter]
  | inr k => simpa [support,barycenter] using (shared_radial_body l hl).2.2.1 k

-- Reconstruct an arbitrary sum-one point using the actual invertible original cell matrix.
theorem support_coordinates (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (v : W) (hv : ∑ j, v j = 1) :
    let u := ((edgeMatrix l n)⁻¹).mulVec (drop v - drop (vertices l n 0))
    support l (facet n) v =
      (1-∑ j, u j) * support l (facet n) (vertices l n 0) := by
  let u := ((edgeMatrix l n)⁻¹).mulVec (drop v - drop (vertices l n 0))
  let v' : W := (1-∑ j, u j) • vertices l n 0 +
    u 0 • vertices l n 1 + u 1 • vertices l n 2 + u 2 • vertices l n 3
  have hm : (edgeMatrix l n).mulVec u = drop v - drop (vertices l n 0) := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (edgeMatrix_det_ne_zero l hl n)),Matrix.one_mulVec]
  have hs : ∑ j, v' j = 1 := by
    simp only [v',Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Finset.sum_add_distrib,← Finset.mul_sum,vertex_sum_one l hl n]
    simp [Fin.sum_univ_three] <;> ring
  have hd : drop v' = drop v := by
    calc
      _ = drop (vertices l n 0) + (edgeMatrix l n).mulVec u := by
        ext j
        simp [v',drop,edgeMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
          smul_eq_mul] <;> ring
      _ = _ := by rw [hm]; module
  have he : v' = v := by
    calc
      _ = liftAffine (drop v') := (lift_drop v' hs).symm
      _ = liftAffine (drop v) := congrArg liftAffine hd
      _ = _ := lift_drop v hv
  have h0 := exterior_vertices_support l hl n 0
  have h1 := exterior_vertices_support l hl n 1
  have h2 := exterior_vertices_support l hl n 2
  change support l (facet n) (vertices l n 1) = 0 at h0
  change support l (facet n) (vertices l n 2) = 0 at h1
  change support l (facet n) (vertices l n 3) = 0 at h2
  change support l (facet n) v = _
  conv_lhs => rw [← he]
  simp [v',u,map_add,map_smul,h0,h1,h2]

theorem body_nonpositive (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (v : cutBody l) : dotProduct v.val (exteriorCovector l n) ≤ 0 := by
  let u := ((edgeMatrix l n)⁻¹).mulVec (drop v.val - drop (vertices l n 0))
  have hm : (edgeMatrix l n).mulVec u = drop v.val - drop (vertices l n 0) := by
    dsimp only [u]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (edgeMatrix_det_ne_zero l hl n)),Matrix.one_mulVec]
  have hbody : support l (facet n) v.val ≤ 0 := by
    cases hf : facet n with
    | inl k => exact neg_nonpos.mpr (v.property.1.1 k)
    | inr k => simpa [support] using v.property.2 k
  have hr : support l (facet n) v.val =
      (1-∑ j, u j) * support l (facet n) (vertices l n 0) :=
    support_coordinates l hl n v.val v.property.1.2
  have hu : (∑ j, u j) ≤ 1 := by
    by_contra hh
    have hnegative : 1-(∑ j, u j) < 0 := by linarith
    have hpositive := mul_pos_of_neg_of_neg hnegative (support_at_origin_negative l hl n)
    rw [hr] at hbody
    exact (not_lt_of_ge hbody) hpositive
  have hh := original_cell_halfspace l hl n u hu
  rw [hm] at hh
  have hc : drop (vertices l n 0) + (drop v.val-drop (vertices l n 0)) = drop v.val := by
    module
  rw [hc] at hh
  rw [exterior_covector_readout l n v.val v.property.1.2]
  exact sub_nonpos.mpr hh

theorem raw_spacelike
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : W, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) :
    0 < lorentz (raw l M n) (raw l M n) := by
  have hq : (0 : Fin 2 → ℝ) ∈ parameterTriangle := by
    norm_num [parameterTriangle,CFMPOriginalInternalFaceBridge435V2Transient.parameterTriangle]
  let w : cutBody l := ⟨xi l n 0,xi_mem_cutBody l hl n 0 hq⟩
  have ht : lorentz (xi l n 0 ᵥ* M) (xi l n 0 ᵥ* M) < 0 :=
    (CFMPOriginalInternalFaceBridge435V2Transient.body_future_data l hl M hG f hf w).1
  have horth : lorentz (xi l n 0 ᵥ* M) (raw l M n) = 0 :=
    (pair_raw l M hM n _).trans (face_readout l hl n 0)
  have hn : raw l M n ≠ 0 := by
    intro hz
    have h := pair_raw l M hM n (vertices l n 0)
    rw [vertex_readout l hl n 0] at h
    have hzero : (0 : ℝ) = -|(edgeMatrix l n).det| := by
      simpa [hz,lorentz] using h
    have hd := abs_pos.mpr (edgeMatrix_det_ne_zero l hl n)
    linarith
  exact spacelike_of_timelike_orthogonal _ _ ht horth hn

theorem pair_unit
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : W, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) :
    lorentz (unit l M n) (unit l M n) = 1 := by
  have hp := raw_spacelike l hl M hM hG f hf n
  have hs : Real.sqrt (lorentz (raw l M n) (raw l M n)) ≠ 0 :=
    (Real.sqrt_pos.mpr hp).ne'
  simp only [unit]
  have he (t : ℝ) (N : W) : lorentz (t • N) (t • N) = t^2 * lorentz N N := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    ring
  rw [he,inv_pow,Real.sq_sqrt hp.le]
  exact inv_mul_cancel₀ (ne_of_gt hp)

theorem original_native_readout
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : W, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) (v : cutBody l) :
    lorentz (lift (f v)) (unit l M n) =
      dotProduct v.val (exteriorCovector l n) /
        (Real.sqrt (-gramQuadratic l v.val) *
          Real.sqrt (lorentz (raw l M n) (raw l M n))) := by
  obtain ⟨y,hy,hu,ht,hc⟩ := hf v
  rw [lift_of_coordinates _ y hu ht hc,hy]
  have hr : radial l v.val = (Real.sqrt (-gramQuadratic l v.val))⁻¹ • v.val := by
    ext k
    simp [radial,div_eq_mul_inv,mul_comm]
  rw [hr,Matrix.smul_vecMul]
  have he (a b : ℝ) (X Y : W) : lorentz (a • X) (b • Y) = a*b*lorentz X Y := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    ring
  simp only [unit,he,pair_raw l M hM n]
  ring

theorem original_outward_face
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : W, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) :
    (∀ v : cutBody l,
      lorentz (lift (f v)) (unit l M n) ≤ 0) ∧
    ∀ (q : Fin 2 → ℝ) (hq : q ∈ parameterTriangle),
      let v : cutBody l := ⟨xi l n q,
        xi_mem_cutBody l hl n q hq⟩
      let p := nativeCoordinates (f v)
      let N := unit l M n
      (liftMatrix p).mulVec (coordinateNormal p N) = N ∧
      dotProduct (coordinateNormal p N) (coordinateNormal p N)/(p 2)^2 = 1 ∧
      (∀ a : CFMPLorentzLiftSurface435Transient.V,
        lorentz ((liftMatrix p).mulVec a) N = 0 →
        dotProduct a (coordinateNormal p N)/(p 2)^2 = 0) ∧
      HasDerivAt (fun t : ℝ => lorentz (coordinateLift (p+t • coordinateNormal p N)) N) 1 0 ∧
      (∀ᶠ t : ℝ in 𝓝[>] 0, 0 < (p+t • coordinateNormal p N) 2 ∧
        0 < lorentz (coordinateLift (p+t • coordinateNormal p N)) N) := by
  have hpos := raw_spacelike l hl M hM hG f hf n
  constructor
  · intro v
    rw [original_native_readout l hl M hM hG f hf n v]
    exact div_nonpos_of_nonpos_of_nonneg (body_nonpositive l hl n v)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · intro q hq
    let v : cutBody l := ⟨xi l n q,
      xi_mem_cutBody l hl n q hq⟩
    let p := nativeCoordinates (f v)
    let N := unit l M n
    have hp : p 2 ≠ 0 := (f v).coordinates.property.ne'
    have hplane : lorentz (coordinateLift p) N = 0 := by
      change lorentz (lift (f v)) N = 0
      rw [original_native_readout l hl M hM hG f hf n v]
      change dotProduct (xi l n q)
        (exteriorCovector l n) / _ = 0
      rw [face_readout l hl n q,zero_div]
    have hunit := pair_unit l hl M hM hG f hf n
    exact ⟨coordinateNormal_lift p N hp hplane,
      coordinateNormal_unit p N hp hplane hunit,
      fun a ha => coordinateNormal_orthogonal p a N hp hplane ha,
      normal_plane_derivative p N hp hplane hunit,
      normal_points_positive p N (f v).coordinates.property hplane hunit⟩

#print axioms original_outward_face
end CFMPOriginalExteriorNativeNormal435Transient
