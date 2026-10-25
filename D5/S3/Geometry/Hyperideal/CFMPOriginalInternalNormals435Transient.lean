import D5.S3.Geometry.Hyperideal.CFMPOriginalFacePairing435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalFaceBridge435V2Transient
import D5.S3.Geometry.Hyperideal.CFMPNativeNormalCoorientation435Transient
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import D5.S3.Geometry.Hyperideal.LinearNonposOnHull

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix BigOperators Topology
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativePlaneNormal435Transient
open CFMPNativeNormalCoorientation435Transient

namespace CFMPOriginalInternalNormals435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

abbrev A := CFMPOriginalFacePairing435Transient.coefficient
abbrev B := CFMPOriginalCellsOrientation435Transient.edges

def covector (a : Fin 3 → ℝ) : W :=
  let c := (a 0+a 1+a 2)/4
  ![a 0-c,a 1-c,a 2-c,-c]

def raw (M : Matrix (Fin 4) (Fin 4) ℝ) (a : Fin 3 → ℝ) : W :=
  let z := M⁻¹ *ᵥ covector a
  ![z 0,z 1,z 2,-z 3]

def unit (M : Matrix (Fin 4) (Fin 4) ℝ) (a : Fin 3 → ℝ) : W :=
  (Real.sqrt (lorentz (raw M a) (raw M a)))⁻¹ • raw M a

theorem pair_raw (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (v : W) (a : Fin 3 → ℝ) :
    lorentz (v ᵥ* M) (raw M a) = dotProduct v (covector a) := by
  calc
    _ = dotProduct (v ᵥ* M) (M⁻¹ *ᵥ covector a) := by
      simp [raw,lorentz,dotProduct,Fin.sum_univ_four]
    _ = dotProduct v ((M * M⁻¹) *ᵥ covector a) := by
      simp only [Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul]
    _ = _ := by rw [Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
      Matrix.one_mulVec]

theorem covector_readout (a : Fin 3 → ℝ) (v : W) (hv : ∑ k, v k = 1) :
    dotProduct v (covector a) =
      dotProduct a (fun k : Fin 3 => v k.castSucc - 1/4) := by
  have hs : v 0+v 1+v 2+v 3=1 := by simpa [Fin.sum_univ_four] using hv
  have hv3 : v 3 = 1-v 0-v 1-v 2 := by linarith [hs]
  simp [covector,dotProduct,Fin.sum_univ_four,Fin.sum_univ_three]
  rw [hv3]
  ring

theorem coefficient_eq (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 3) :
    CFMPOriginalCellsOrientation435Transient.coefficient (B l n) i = A l n i := by
  rw [CFMPOriginalCellsOrientation435Transient.coefficient_eq_area,
    CFMPOriginalCellsOrientation435Transient.abs_div_det_eq_sign l hl n]
  rfl

theorem determinant_ne (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) (n : Fin 20) :
    (B l n).det ≠ 0 := by
  intro h
  have hp := CFMPOriginalCellsOrientation435Transient.signed_det_positive l hl n
  rw [h,mul_zero] at hp
  exact lt_irrefl _ hp

theorem vertex_readout (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 3) (j : Fin 4) :
    dotProduct (vertices l n j) (covector (A l n i)) =
      if j=i.succ then -|(B l n).det| else 0 := by
  rw [covector_readout _ _ (CFMPOriginalCellsIndependent435Transient.vertex_sum_one l hl n j)]
  have hbase : vertices l n 0 = barycenter := by fin_cases n <;> rfl
  cases j using Fin.cases with
  | zero =>
    have hne : (0 : Fin 4) ≠ i.succ := (Fin.succ_ne_zero i).symm
    simp [hbase,barycenter,dotProduct,hne]
  | succ j =>
    have h := CFMPOriginalCellsOrientation435Transient.coefficient_dot_mulVec
      (B l n) (determinant_ne l hl n) i (Pi.single j 1)
    rw [coefficient_eq l hl n i,Matrix.mulVec_single_one] at h
    change dotProduct (A l n i) (fun k => vertices l n j.succ k.castSucc-1/4) = _
    have he : (B l n).col j =
        (fun k : Fin 3 => vertices l n j.succ k.castSucc-1/4) := by
      ext k
      simp [B,CFMPOriginalCellsOrientation435Transient.edges,Matrix.col_apply,hbase,barycenter]
    rw [he] at h
    simpa [Pi.single_apply,Fin.succ_inj,eq_comm] using h

theorem cell_nonpositive (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 3) :
    ∀ v ∈ cell l n, dotProduct v (covector (A l n i)) ≤ 0 := by
  let L : W →ₗ[ℝ] ℝ :=
    { toFun := fun v => dotProduct v (covector (A l n i))
      map_add' := fun x y => add_dotProduct x y _
      map_smul' := fun c x => smul_dotProduct c x _ }
  apply D5.S3.Geometry.Hyperideal.LinearNonposOnHull.linear_nonpos_on_hull
    (range (vertices l n)) L
  rintro _ ⟨j,rfl⟩
  change dotProduct (vertices l n j) (covector (A l n i)) ≤ 0
  rw [vertex_readout l hl n i j]
  split_ifs
  · exact neg_nonpos.mpr (abs_nonneg _)
  · exact le_rfl

theorem raw_spacelike
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : W, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) :
    0 < lorentz (raw M (A l n i)) (raw M (A l n i)) := by
  let v : cutBody l := ⟨barycenter,(shared_radial_body l hl).2.1⟩
  let p := nativeCoordinates (f v)
  let N := raw M (A l n i)
  have hp : p 2 ≠ 0 := (f v).coordinates.property.ne'
  have hbase : dotProduct barycenter (covector (A l n i)) = 0 := by
    simp [barycenter,covector,dotProduct,Fin.sum_univ_four]
    ring
  have hplane : lorentz (coordinateLift p) N = 0 := by
    obtain ⟨y,hy,hu,ht,hc⟩ := hf v
    have hL : coordinateLift p = y := lift_of_coordinates _ y hu ht hc
    rw [hL,hy,pair_raw M hM]
    simp [radial,dotProduct,Fin.sum_univ_four,covector,barycenter,v]
    ring
  have hn : N ≠ 0 := by
    intro hz
    have h := pair_raw M hM (vertices l n i.succ) (A l n i)
    change lorentz (vertices l n i.succ ᵥ* M) N = _ at h
    rw [hz,vertex_readout l hl n i i.succ] at h
    simp [lorentz] at h
    exact determinant_ne l hl n h
  let a := coordinateNormal p N
  have ha : a ≠ 0 := by
    intro hz
    have h := coordinateNormal_lift p N hp hplane
    change (liftMatrix p).mulVec a = N at h
    rw [hz,Matrix.mulVec_zero] at h
    exact hn h.symm
  have hdot : 0 < dotProduct a a := by
    apply lt_of_le_of_ne
    · exact Finset.sum_nonneg (fun k _ => mul_self_nonneg (a k))
    · intro he
      exact ha (dotProduct_self_eq_zero.mp he.symm)
  have hg := liftMatrix_lorentz p a a hp
  change lorentz ((liftMatrix p).mulVec (coordinateNormal p N))
    ((liftMatrix p).mulVec (coordinateNormal p N)) = dotProduct a a/(p 2)^2 at hg
  rw [coordinateNormal_lift p N hp hplane] at hg
  rw [hg]
  exact div_pos hdot (sq_pos_of_ne_zero hp)

theorem pair_unit
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : W, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) :
    lorentz (unit M (A l n i)) (unit M (A l n i)) = 1 := by
  have hp := raw_spacelike l hl M hM f hf n i
  have hs : Real.sqrt (lorentz (raw M (A l n i)) (raw M (A l n i))) ≠ 0 :=
    (Real.sqrt_pos.mpr hp).ne'
  simp only [unit]
  have he (t : ℝ) (N : W) : lorentz (t • N) (t • N) = t^2 * lorentz N N := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    ring
  rw [he,inv_pow,Real.sq_sqrt hp.le]
  exact inv_mul_cancel₀ (ne_of_gt hp)

theorem paired_normals (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (p : Fin 30) :
    unit M (A l (CFMPOriginalFacePairing435Transient.pairTable p).1.1
      (CFMPOriginalFacePairing435Transient.pairTable p).1.2) =
    -unit M (A l (CFMPOriginalFacePairing435Transient.pairTable p).2.1
      (CFMPOriginalFacePairing435Transient.pairTable p).2.2) := by
  have ha := CFMPOriginalFacePairing435Transient.paired_coefficients l p
  have he : A l (CFMPOriginalFacePairing435Transient.pairTable p).1.1
      (CFMPOriginalFacePairing435Transient.pairTable p).1.2 =
      -A l (CFMPOriginalFacePairing435Transient.pairTable p).2.1
        (CFMPOriginalFacePairing435Transient.pairTable p).2.2 := eq_neg_of_add_eq_zero_left ha
  have hc (a : Fin 3 → ℝ) : covector (-a) = -covector a := by
    ext k
    fin_cases k <;> simp [covector] <;> ring
  have hr (a : Fin 3 → ℝ) : raw M (-a) = -raw M a := by
    ext k
    fin_cases k <;> simp [raw,hc,Matrix.mulVec_neg]
  rw [he]
  simp only [unit,hr]
  have hq (N : W) : lorentz (-N) (-N) = lorentz N N := by
    simp [lorentz,Fin.sum_univ_four]
  rw [hq,smul_neg]

theorem coordinateNormal_neg (p : CFMPLorentzLiftSurface435Transient.V) (N : W) :
    coordinateNormal p (-N) = -coordinateNormal p N := by
  ext k
  fin_cases k <;> simp [coordinateNormal] <;> ring

theorem face_readout (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (i : Fin 3) (q : Fin 2 → ℝ) :
    dotProduct (CFMPOriginalInternalFaceBridge435V2Transient.xi l n i q)
      (covector (A l n i)) = 0 := by
  have h0 : dotProduct (vertices l n 0) (covector (A l n i)) = 0 := by
    rw [vertex_readout l hl n i 0]
    simp [(Fin.succ_ne_zero i).symm]
  have he (j : Fin 2) : dotProduct (vertices l n (i.succAbove j).succ)
      (covector (A l n i)) = 0 := by
    rw [vertex_readout l hl n i (i.succAbove j).succ]
    simp [Fin.succAbove_ne]
  simp only [CFMPOriginalInternalFaceBridge435V2Transient.xi,
    CFMPOriginalInternalFaceBridge435V2Transient.direction,
    CFMPOriginalInternalFaceBridge435V2Transient.base,
    add_dotProduct,smul_dotProduct,sub_dotProduct,h0,he,sub_self,smul_zero,add_zero]

theorem original_native_readout
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : W, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) (v : cutBody l) :
    lorentz (lift (f v)) (unit M (A l n i)) =
      dotProduct v.val (covector (A l n i)) /
        (Real.sqrt (-gramQuadratic l v.val) *
          Real.sqrt (lorentz (raw M (A l n i)) (raw M (A l n i)))) := by
  obtain ⟨y,hy,hu,ht,hc⟩ := hf v
  rw [lift_of_coordinates _ y hu ht hc,hy]
  have hr : radial l v.val = (Real.sqrt (-gramQuadratic l v.val))⁻¹ • v.val := by
    ext k
    simp [radial,div_eq_mul_inv,mul_comm]
  rw [hr,Matrix.smul_vecMul]
  have he (a b : ℝ) (X Y : W) : lorentz (a • X) (b • Y) = a*b*lorentz X Y := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    ring
  simp only [unit,he,pair_raw M hM]
  ring

theorem paired_coordinate_flux
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (pair : Fin 30)
    (mu : Measure HyperbolicThreeSpace)
    (X : HyperbolicThreeSpace → CFMPLorentzLiftSurface435Transient.V)
    (hi : Integrable (fun p => dotProduct (X p)
      (coordinateNormal (nativeCoordinates p)
        (unit M (A l (CFMPOriginalFacePairing435Transient.pairTable pair).1.1
          (CFMPOriginalFacePairing435Transient.pairTable pair).1.2))) /
            (nativeCoordinates p 2)^2) mu) :
    Integrable (fun p => dotProduct (X p)
      (coordinateNormal (nativeCoordinates p)
        (unit M (A l (CFMPOriginalFacePairing435Transient.pairTable pair).2.1
          (CFMPOriginalFacePairing435Transient.pairTable pair).2.2))) /
            (nativeCoordinates p 2)^2) mu ∧
    (∫ p, dotProduct (X p)
      (coordinateNormal (nativeCoordinates p)
        (unit M (A l (CFMPOriginalFacePairing435Transient.pairTable pair).1.1
          (CFMPOriginalFacePairing435Transient.pairTable pair).1.2))) /
            (nativeCoordinates p 2)^2 ∂mu) +
    (∫ p, dotProduct (X p)
      (coordinateNormal (nativeCoordinates p)
        (unit M (A l (CFMPOriginalFacePairing435Transient.pairTable pair).2.1
          (CFMPOriginalFacePairing435Transient.pairTable pair).2.2))) /
            (nativeCoordinates p 2)^2 ∂mu) = 0 := by
  have hn := paired_normals l M pair
  simp only [hn,coordinateNormal_neg,dotProduct_neg,neg_div] at hi ⊢
  exact ⟨hi.neg.congr (Filter.Eventually.of_forall (fun p => neg_neg _)),
    by rw [integral_neg]; exact neg_add_cancel _⟩

theorem original_outward_face
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : W, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) :
    (∀ v : cutBody l, v.val ∈ cell l n →
      lorentz (lift (f v)) (unit M (A l n i)) ≤ 0) ∧
    ∀ (q : Fin 2 → ℝ) (hq : q ∈ CFMPOriginalInternalFaceBridge435V2Transient.parameterTriangle),
      let v : cutBody l := ⟨CFMPOriginalInternalFaceBridge435V2Transient.xi l n i q,
        CFMPOriginalInternalFaceBridge435V2Transient.xi_mem_cutBody l hl n i q hq⟩
      let p := nativeCoordinates (f v)
      let N := unit M (A l n i)
      (liftMatrix p).mulVec (coordinateNormal p N) = N ∧
      dotProduct (coordinateNormal p N) (coordinateNormal p N)/(p 2)^2 = 1 ∧
      (∀ a : CFMPLorentzLiftSurface435Transient.V,
        lorentz ((liftMatrix p).mulVec a) N = 0 →
        dotProduct a (coordinateNormal p N)/(p 2)^2 = 0) ∧
      HasDerivAt (fun t : ℝ => lorentz (coordinateLift (p+t • coordinateNormal p N)) N) 1 0 ∧
      (∀ᶠ t : ℝ in 𝓝[>] 0, 0 < (p+t • coordinateNormal p N) 2 ∧
        0 < lorentz (coordinateLift (p+t • coordinateNormal p N)) N) := by
  have hpos := raw_spacelike l hl M hM f hf n i
  constructor
  · intro v hv
    rw [original_native_readout l hl M hM f hf n i v]
    exact div_nonpos_of_nonpos_of_nonneg (cell_nonpositive l hl n i v.val hv)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · intro q hq
    let v : cutBody l := ⟨CFMPOriginalInternalFaceBridge435V2Transient.xi l n i q,
      CFMPOriginalInternalFaceBridge435V2Transient.xi_mem_cutBody l hl n i q hq⟩
    let p := nativeCoordinates (f v)
    let N := unit M (A l n i)
    have hp : p 2 ≠ 0 := (f v).coordinates.property.ne'
    have hplane : lorentz (coordinateLift p) N = 0 := by
      change lorentz (lift (f v)) N = 0
      rw [original_native_readout l hl M hM f hf n i v]
      change dotProduct (CFMPOriginalInternalFaceBridge435V2Transient.xi l n i q)
        (covector (A l n i)) / _ = 0
      rw [face_readout l hl n i q,zero_div]
    have hunit := pair_unit l hl M hM f hf n i
    exact ⟨coordinateNormal_lift p N hp hplane,
      coordinateNormal_unit p N hp hplane hunit,
      fun a ha => coordinateNormal_orthogonal p a N hp hplane ha,
      normal_plane_derivative p N hp hplane hunit,
      normal_points_positive p N (f v).coordinates.property hplane hunit⟩

def faceSet (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (f : cutBody l → HyperbolicThreeSpace) (n : Fin 20) (i : Fin 3) :
    Set HyperbolicThreeSpace :=
  range (fun q : CFMPOriginalInternalFaceBridge435V2Transient.parameterTriangle =>
    f ⟨CFMPOriginalInternalFaceBridge435V2Transient.xi l n i q.val,
      CFMPOriginalInternalFaceBridge435V2Transient.xi_mem_cutBody l hl n i q.val q.property⟩)

theorem pair_xi (l : Fin 6 → ℝ) (p : Fin 30) (q : Fin 2 → ℝ) :
    CFMPOriginalInternalFaceBridge435V2Transient.xi l
      (CFMPOriginalFacePairing435Transient.pairTable p).1.1
      (CFMPOriginalFacePairing435Transient.pairTable p).1.2 q =
    CFMPOriginalInternalFaceBridge435V2Transient.xi l
      (CFMPOriginalFacePairing435Transient.pairTable p).2.1
      (CFMPOriginalFacePairing435Transient.pairTable p).2.2
      (CFMPOriginalFacePairing435Transient.pairedParam p q) := by
  change CFMPOriginalFacePairing435Transient.faceParam l _ _ q =
    CFMPOriginalFacePairing435Transient.faceParam l _ _
      (CFMPOriginalFacePairing435Transient.pairedParam p q)
  unfold CFMPOriginalFacePairing435Transient.faceParam
  simp only [CFMPOriginalFacePairing435Transient.face_order l p]
  by_cases h : CFMPOriginalFacePairing435Transient.swapEndpoints p = true
  · simp [CFMPOriginalFacePairing435Transient.pairedParam,h,
      CFMPOriginalFacePairing435Transient.reverseFace,Equiv.swap_apply_def,
      Function.comp_apply,add_assoc,add_comm,add_left_comm]
  · simp [CFMPOriginalFacePairing435Transient.pairedParam,h,Function.comp_apply]

theorem paired_native_face (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (f : cutBody l → HyperbolicThreeSpace) (p : Fin 30) :
    faceSet l hl f (CFMPOriginalFacePairing435Transient.pairTable p).1.1
      (CFMPOriginalFacePairing435Transient.pairTable p).1.2 =
    faceSet l hl f (CFMPOriginalFacePairing435Transient.pairTable p).2.1
      (CFMPOriginalFacePairing435Transient.pairTable p).2.2 := by
  have hm (q : Fin 2 → ℝ) :
      CFMPOriginalFacePairing435Transient.pairedParam p q ∈
        CFMPOriginalInternalFaceBridge435V2Transient.parameterTriangle ↔
      q ∈ CFMPOriginalInternalFaceBridge435V2Transient.parameterTriangle := by
    dsimp [CFMPOriginalFacePairing435Transient.pairedParam,
      CFMPOriginalInternalFaceBridge435V2Transient.parameterTriangle]
    split_ifs <;> simp [and_left_comm,add_comm]
  have hinv (q : Fin 2 → ℝ) :
      CFMPOriginalFacePairing435Transient.pairedParam p
        (CFMPOriginalFacePairing435Transient.pairedParam p q) = q := by
    unfold CFMPOriginalFacePairing435Transient.pairedParam
    split_ifs <;> ext k <;> fin_cases k <;> rfl
  ext z
  constructor
  · rintro ⟨q,rfl⟩
    refine ⟨⟨CFMPOriginalFacePairing435Transient.pairedParam p q.val,(hm q.val).mpr q.property⟩,?_⟩
    apply congrArg f
    apply Subtype.ext
    exact (pair_xi l p q.val).symm
  · rintro ⟨q,rfl⟩
    refine ⟨⟨CFMPOriginalFacePairing435Transient.pairedParam p q.val,(hm q.val).mpr q.property⟩,?_⟩
    apply congrArg f
    apply Subtype.ext
    simpa only [hinv] using pair_xi l p (CFMPOriginalFacePairing435Transient.pairedParam p q.val)

def flux (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (n : Fin 20) (i : Fin 3)
    (X : HyperbolicThreeSpace → CFMPLorentzLiftSurface435Transient.V)
    (p : HyperbolicThreeSpace) : ℝ :=
  dotProduct (X p) (coordinateNormal (nativeCoordinates p) (unit M (A l n i))) /
    (nativeCoordinates p 2)^2

theorem actual_pair_flux
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (pair : Fin 30) (X : HyperbolicThreeSpace → CFMPLorentzLiftSurface435Transient.V)
    (hi : IntegrableOn
      (flux l M (CFMPOriginalFacePairing435Transient.pairTable pair).1.1
        (CFMPOriginalFacePairing435Transient.pairTable pair).1.2 X)
      (faceSet l hl f (CFMPOriginalFacePairing435Transient.pairTable pair).1.1
        (CFMPOriginalFacePairing435Transient.pairTable pair).1.2)
      (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) :
    IntegrableOn
      (flux l M (CFMPOriginalFacePairing435Transient.pairTable pair).2.1
        (CFMPOriginalFacePairing435Transient.pairTable pair).2.2 X)
      (faceSet l hl f (CFMPOriginalFacePairing435Transient.pairTable pair).2.1
        (CFMPOriginalFacePairing435Transient.pairTable pair).2.2)
      (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) ∧
    (∫ p in faceSet l hl f (CFMPOriginalFacePairing435Transient.pairTable pair).1.1
        (CFMPOriginalFacePairing435Transient.pairTable pair).1.2,
      flux l M (CFMPOriginalFacePairing435Transient.pairTable pair).1.1
        (CFMPOriginalFacePairing435Transient.pairTable pair).1.2 X p
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) +
    (∫ p in faceSet l hl f (CFMPOriginalFacePairing435Transient.pairTable pair).2.1
        (CFMPOriginalFacePairing435Transient.pairTable pair).2.2,
      flux l M (CFMPOriginalFacePairing435Transient.pairTable pair).2.1
        (CFMPOriginalFacePairing435Transient.pairTable pair).2.2 X p
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) = 0 := by
  rw [← paired_native_face l hl f pair]
  exact paired_coordinate_flux l M pair
    ((Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace).restrict
      (faceSet l hl f (CFMPOriginalFacePairing435Transient.pairTable pair).1.1
        (CFMPOriginalFacePairing435Transient.pairTable pair).1.2)) X hi

theorem all_actual_internal_flux
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (X : HyperbolicThreeSpace → CFMPLorentzLiftSurface435Transient.V)
    (hi : ∀ (n : Fin 20) (i : Fin 3), IntegrableOn (flux l M n i X)
      (faceSet l hl f n i) (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) :
    ∑ n : Fin 20, ∑ i : Fin 3,
      ∫ p in faceSet l hl f n i, flux l M n i X p
        ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) = 0 := by
  let g (n : Fin 20) (i : Fin 3) : ℝ :=
    ∫ p in faceSet l hl f n i, flux l M n i X p
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
  let e : (Fin 30 × Bool) ≃ (Fin 20 × Fin 3) :=
    Equiv.ofBijective CFMPOriginalFacePairing435Transient.pairedOccurrence (by decide)
  have hp (pair : Fin 30) :
      g (CFMPOriginalFacePairing435Transient.pairTable pair).1.1
          (CFMPOriginalFacePairing435Transient.pairTable pair).1.2 +
        g (CFMPOriginalFacePairing435Transient.pairTable pair).2.1
          (CFMPOriginalFacePairing435Transient.pairTable pair).2.2 = 0 :=
    (actual_pair_flux l hl M f pair X (hi _ _)).2
  change ∑ n, ∑ i, g n i = 0
  calc
    _ = ∑ t : Fin 20 × Fin 3, g t.1 t.2 := (Fintype.sum_prod_type _).symm
    _ = ∑ t : Fin 30 × Bool, g (e t).1 (e t).2 := (Equiv.sum_comp e _).symm
    _ = ∑ pair : Fin 30,
        (g (CFMPOriginalFacePairing435Transient.pairTable pair).1.1
          (CFMPOriginalFacePairing435Transient.pairTable pair).1.2 +
        g (CFMPOriginalFacePairing435Transient.pairTable pair).2.1
          (CFMPOriginalFacePairing435Transient.pairTable pair).2.2) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro pair _
      simp [e,CFMPOriginalFacePairing435Transient.pairedOccurrence,Fintype.sum_bool,add_comm]
    _ = 0 := by simp_rw [hp]; simp

end CFMPOriginalInternalNormals435Transient
