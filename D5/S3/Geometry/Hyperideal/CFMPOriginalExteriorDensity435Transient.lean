import D5.S3.Geometry.Hyperideal.CFMPActualCoefficientDensity435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorNativeNormal435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicPlaneRealization
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalExteriorFaceChart435Transient
open CFMPOriginalCellsIndependent435Transient

namespace CFMPOriginalExteriorDensity435Transient

abbrev E := Fin 2 → ℝ
abbrev V := Fin 3 → ℝ
abbrev W := Fin 4 → ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

def x (l : Fin 6 → ℝ) (n : Fin 20) (q : E) : V :=
  fun j => xi l n q j.castSucc

def v (l : Fin 6 → ℝ) (n : Fin 20) (a : Fin 2) : V :=
  fun j => direction l n a j.castSucc

def scale (l : Fin 6 → ℝ) (n : Fin 20) : ℝ :=
  |(edgeMatrix l n).det| / (edgeMatrix l n).det

theorem lift_x (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j)
    (n : Fin 20) (q : E) :
    CFMPCoefficientAreaDeterminant435Transient.lift (x l n q) = xi l n q := by
  obtain ⟨ha,hb,hc⟩ := section_sums l hl n
  have hs : ∑ k, xi l n q k = 1 := by
    simp only [xi,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
      ← Finset.mul_sum,ha,hb,hc,mul_zero,add_zero]
  simp only [Fin.sum_univ_four] at hs
  ext k
  fin_cases k <;> simp [CFMPCoefficientAreaDeterminant435Transient.lift,x]
  linarith

theorem tangent_v (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j)
    (n : Fin 20) (a : Fin 2) :
    CFMPCoefficientAreaDeterminant435Transient.tangent (v l n a) =
      direction l n a := by
  have hs : ∑ k, direction l n a k = 0 := by
    fin_cases a
    · exact (section_sums l hl n).2.1
    · exact (section_sums l hl n).2.2
  simp only [Fin.sum_univ_four] at hs
  ext k
  fin_cases k <;> simp [CFMPCoefficientAreaDeterminant435Transient.tangent,v]
  linarith

theorem adjugate_exterior (B : Matrix (Fin 3) (Fin 3) ℝ) :
    B.adjugate.transpose.mulVec (fun _ => 1) =
      ((B.col 1 - B.col 0) ⨯₃ (B.col 2 - B.col 0)) := by
  ext k
  fin_cases k <;>
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,Matrix.adjugate_fin_three,
      Matrix.transpose_apply,cross_apply,Matrix.col_apply] <;> ring

theorem exterior_directions (l : Fin 6 → ℝ) (n : Fin 20) (j : Fin 2) :
    (edgeMatrix l n).col j.succ - (edgeMatrix l n).col 0 = v l n j := by
  ext k
  fin_cases j <;>
    simp [v,edgeMatrix,CFMPOriginalCellsIndependent435Transient.drop,
      CFMPOriginalExteriorFaceChart435Transient.direction,
      CFMPOriginalExteriorFaceChart435Transient.base,Matrix.col_apply] <;> ring

theorem coefficient_scale (l : Fin 6 → ℝ) (n : Fin 20) :
    outwardCoefficient l n = scale l n • (v l n 0 ⨯₃ v l n 1) := by
  have h0 : (edgeMatrix l n).col 1 - (edgeMatrix l n).col 0 = v l n 0 :=
    exterior_directions l n 0
  have h1 : (edgeMatrix l n).col 2 - (edgeMatrix l n).col 0 = v l n 1 :=
    exterior_directions l n 1
  rw [outwardCoefficient,Matrix.inv_def,Ring.inverse_eq_inv,
    Matrix.transpose_smul,Matrix.smul_mulVec,smul_smul,adjugate_exterior,h0,h1]
  simp only [scale,div_eq_mul_inv]

theorem scale_sq (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j) (n : Fin 20) :
    (scale l n)^2 = 1 := by
  rw [scale,div_pow,sq_abs]
  exact div_self (pow_ne_zero _ (edgeMatrix_det_ne_zero l hl n))

theorem covector_scale (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j)
    (n : Fin 20) (q : E) :
    exteriorCovector l n =
      scale l n • CFMPCoefficientAreaDeterminant435Transient.covector
        (v l n 0 ⨯₃ v l n 1)
        (dotProduct (v l n 0 ⨯₃ v l n 1) (x l n q)) := by
  have hp := exterior_plane_readout l hl n q
  change dotProduct (outwardCoefficient l n) (x l n q) = planeOffset l n at hp
  rw [coefficient_scale,smul_dotProduct] at hp
  have hc : planeOffset l n = scale l n *
      dotProduct (v l n 0 ⨯₃ v l n 1) (x l n q) := hp.symm
  simp only [exteriorCovector,coefficient_scale,hc]
  ext k
  fin_cases k <;>
    simp [CFMPCoefficientAreaDeterminant435Transient.covector,smul_eq_mul] <;> ring

theorem raw_scale (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j)
    (M : M4) (n : Fin 20) (q : E) :
    CFMPOriginalExteriorNativeNormal435Transient.raw l M n =
      scale l n • CFMPCoefficientAreaDeterminant435Transient.raw M
        (v l n 0 ⨯₃ v l n 1)
        (dotProduct (v l n 0 ⨯₃ v l n 1) (x l n q)) := by
  ext k
  fin_cases k <;>
    simp [CFMPOriginalExteriorNativeNormal435Transient.raw,
      CFMPCoefficientAreaDeterminant435Transient.raw,covector_scale l hl n q,
      Matrix.mulVec_smul,smul_eq_mul]
  <;> ring

theorem raw_norm (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j)
    (M : M4) (n : Fin 20) (q : E) :
    lorentz (CFMPOriginalExteriorNativeNormal435Transient.raw l M n)
      (CFMPOriginalExteriorNativeNormal435Transient.raw l M n) =
    lorentz (CFMPCoefficientAreaDeterminant435Transient.raw M
        (v l n 0 ⨯₃ v l n 1)
        (dotProduct (v l n 0 ⨯₃ v l n 1) (x l n q)))
      (CFMPCoefficientAreaDeterminant435Transient.raw M
        (v l n 0 ⨯₃ v l n 1)
        (dotProduct (v l n 0 ⨯₃ v l n 1) (x l n q))) := by
  rw [raw_scale l hl M n q]
  have hs (s : ℝ) (N : W) : lorentz (s • N) (s • N) = s^2 * lorentz N N := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    ring
  rw [hs,scale_sq l hl n,one_mul]

theorem original_face_density
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : M4) (hM : M.det ≠ 0)
    (hG : ∀ a b, lorentz (M a) (M b) = lengthGram l a b)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ z, ∃ y : W, y = (radial l z.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f z).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (q : E) (hq : q ∈ parameterTriangle) :
    let U := (xi l n q) ᵥ* M
    let db := (CFMPNativePullbackMetric435Transient.nativeMatrix U).mulVec
      (direction l n 0 ᵥ* M)
    let dc := (CFMPNativePullbackMetric435Transient.nativeMatrix U).mulVec
      (direction l n 1 ᵥ* M)
    let N := CFMPOriginalExteriorNativeNormal435Transient.raw l M n
    Real.sqrt (dotProduct (db ⨯₃ dc) (db ⨯₃ dc)) /
      (CFMPNativePullbackMetric435Transient.nativeMap U 2)^2 =
      |M.det| * Real.sqrt (lorentz N N) /
        (Real.sqrt (CFMPNativePullbackMetric435Transient.radius U))^3 := by
  obtain ⟨A,hA,he,hplane,hs,hcols,hdetChart,hinj,hpositive,hchart⟩ :=
    same_reflection_chart_data l hl M hM hG f hf n
  let R := CFMPActualTriangleNormal435Transient.reflectionLinear A
  have hR : ∀ Y Z : W, lorentz (R Y) (R Z) = lorentz Y Z := by
    intro Y Z
    simpa only [R,CFMPActualTriangleNormal435Transient.reflectionLinear_apply] using
      reflection_pair A Y Z hA.ne'
  have hbase : R (base l n ᵥ* M) 1 = 0 := by
    simpa [xi,R] using hplane 0
  have hP : R (direction l n 0 ᵥ* M) 1 = 0 := by
    have h := hplane ![1,0]
    change R (xi l n ![1,0] ᵥ* M) 1 = 0 at h
    simpa [xi,Matrix.add_vecMul,Matrix.smul_vecMul,map_add,map_smul,hbase] using h
  have hQ : R (direction l n 1 ᵥ* M) 1 = 0 := by
    have h := hplane ![0,1]
    change R (xi l n ![0,1] ᵥ* M) 1 = 0 at h
    simpa [xi,Matrix.add_vecMul,Matrix.smul_vecMul,map_add,map_smul,hbase] using h
  have hfuture := CFMPOriginalInternalFaceBridge435V2Transient.body_future_data l hl M hG f hf
    ⟨xi l n q,xi_mem_cutBody l hl n q hq⟩
  have hr : 0 < CFMPNativePullbackMetric435Transient.radius (xi l n q ᵥ* M) :=
    neg_pos.mpr hfuture.1
  have hd : CFMPNativePullbackMetric435Transient.delta (xi l n q ᵥ* M) ≠ 0 :=
    hfuture.2.2.ne'
  have hN := CFMPOriginalExteriorNativeNormal435Transient.raw_spacelike l hl M hM hG f hf n
  rw [raw_norm l hl M n q] at hN
  have h := CFMPActualCoefficientDensity435Transient.actual_face_density M hM
    (x l n q) (v l n 0) (v l n 1) hN
    (by simpa only [lift_x l hl n q] using hr)
    (by simpa only [lift_x l hl n q] using hd) R hR
    (by simpa only [lift_x l hl n q] using hplane q)
    (by simpa only [tangent_v l hl n 0] using hP)
    (by simpa only [tangent_v l hl n 1] using hQ)
  dsimp only at h ⊢
  simpa only [lift_x l hl n q,tangent_v l hl n 0,tangent_v l hl n 1,
    raw_norm l hl M n q] using h

#print axioms original_face_density
end CFMPOriginalExteriorDensity435Transient
