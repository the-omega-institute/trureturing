import D5.S3.Geometry.Hyperideal.CFMPActualCoefficientDensity435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalNormals435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicPlaneRealization
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalInternalFaceBridge435V2Transient

namespace CFMPOriginalFaceDensity435Transient

abbrev E := Fin 2 → ℝ
abbrev V := Fin 3 → ℝ
abbrev W := Fin 4 → ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

def x (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3) (q : E) : V :=
  fun j => xi l n i q j.castSucc

def v (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3) (a : Fin 2) : V :=
  fun j => direction l n i a j.castSucc

def sign (n : Fin 20) (i : Fin 3) : ℝ :=
  CFMPOriginalFacePairing435Transient.orientation n * ![-1,1,-1] i

theorem lift_x (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j)
    (n : Fin 20) (i : Fin 3) (q : E) :
    CFMPCoefficientAreaDeterminant435Transient.lift (x l n i q) = xi l n i q := by
  obtain ⟨ha,hb,hc⟩ := section_sums l hl n i
  have hs : ∑ k, xi l n i q k = 1 := by
    simp only [xi,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
      ← Finset.mul_sum,ha,hb,hc,mul_zero,add_zero]
  simp only [Fin.sum_univ_four] at hs
  ext k
  fin_cases k <;> simp [CFMPCoefficientAreaDeterminant435Transient.lift,x]
  linarith

theorem tangent_v (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j)
    (n : Fin 20) (i : Fin 3) (a : Fin 2) :
    CFMPCoefficientAreaDeterminant435Transient.tangent (v l n i a) =
      direction l n i a := by
  have hs : ∑ k, direction l n i a k = 0 := by
    fin_cases a
    · exact (section_sums l hl n i).2.1
    · exact (section_sums l hl n i).2.2
  simp only [Fin.sum_univ_four] at hs
  ext k
  fin_cases k <;> simp [CFMPCoefficientAreaDeterminant435Transient.tangent,v]
  linarith

theorem coefficient_scale (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3) :
    CFMPOriginalFacePairing435Transient.coefficient l n i =
      sign n i • (v l n i 0 ⨯₃ v l n i 1) := by
  fin_cases i
  · change CFMPOriginalFacePairing435Transient.orientation n •
      (-(CFMPOriginalFacePairing435Transient.edge l n 1 ⨯₃
        CFMPOriginalFacePairing435Transient.edge l n 2)) =
      (CFMPOriginalFacePairing435Transient.orientation n * (-1)) •
      (CFMPOriginalFacePairing435Transient.edge l n 1 ⨯₃
        CFMPOriginalFacePairing435Transient.edge l n 2)
    simp only [mul_neg,mul_one,neg_smul,smul_neg]
  · change CFMPOriginalFacePairing435Transient.orientation n •
      (CFMPOriginalFacePairing435Transient.edge l n 0 ⨯₃
        CFMPOriginalFacePairing435Transient.edge l n 2) =
      (CFMPOriginalFacePairing435Transient.orientation n * 1) •
      (CFMPOriginalFacePairing435Transient.edge l n 0 ⨯₃
        CFMPOriginalFacePairing435Transient.edge l n 2)
    simp only [mul_one]
  · change CFMPOriginalFacePairing435Transient.orientation n •
      (-(CFMPOriginalFacePairing435Transient.edge l n 0 ⨯₃
        CFMPOriginalFacePairing435Transient.edge l n 1)) =
      (CFMPOriginalFacePairing435Transient.orientation n * (-1)) •
      (CFMPOriginalFacePairing435Transient.edge l n 0 ⨯₃
        CFMPOriginalFacePairing435Transient.edge l n 1)
    simp only [mul_neg,mul_one,neg_smul,smul_neg]

theorem sign_sq (n : Fin 20) (i : Fin 3) : (sign n i)^2 = 1 := by
  fin_cases n <;> fin_cases i <;>
    norm_num [sign,CFMPOriginalFacePairing435Transient.orientation]

theorem covector_scale (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j)
    (n : Fin 20) (i : Fin 3) (q : E) :
    CFMPOriginalInternalNormals435Transient.covector
      (CFMPOriginalFacePairing435Transient.coefficient l n i) =
    sign n i • CFMPCoefficientAreaDeterminant435Transient.covector
      (v l n i 0 ⨯₃ v l n i 1)
      (dotProduct (v l n i 0 ⨯₃ v l n i 1) (x l n i q)) := by
  let A := v l n i 0 ⨯₃ v l n i 1
  have hp := CFMPOriginalInternalNormals435Transient.face_readout l hl n i q
  change dotProduct (xi l n i q)
    (CFMPOriginalInternalNormals435Transient.covector
      (CFMPOriginalFacePairing435Transient.coefficient l n i)) = 0 at hp
  rw [← lift_x l hl n i q,coefficient_scale] at hp
  change dotProduct (CFMPCoefficientAreaDeterminant435Transient.lift (x l n i q))
    (CFMPOriginalInternalNormals435Transient.covector (sign n i • A)) = 0 at hp
  have hc : ((sign n i * A 0)+(sign n i * A 1)+(sign n i * A 2))/4 =
      sign n i * dotProduct A (x l n i q) := by
    simp [CFMPCoefficientAreaDeterminant435Transient.lift,
      CFMPOriginalInternalNormals435Transient.covector,dotProduct,
      Fin.sum_univ_four,Fin.sum_univ_three,smul_eq_mul] at hp ⊢
    nlinarith [hp]
  dsimp only [A] at hc
  rw [coefficient_scale]
  ext k
  fin_cases k <;>
    simp [CFMPOriginalInternalNormals435Transient.covector,
      CFMPCoefficientAreaDeterminant435Transient.covector,smul_eq_mul]
  all_goals nlinarith [hc]

theorem raw_scale (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j)
    (M : M4) (n : Fin 20) (i : Fin 3) (q : E) :
    CFMPOriginalInternalNormals435Transient.raw M
      (CFMPOriginalFacePairing435Transient.coefficient l n i) =
      sign n i • CFMPCoefficientAreaDeterminant435Transient.raw M
        (v l n i 0 ⨯₃ v l n i 1)
        (dotProduct (v l n i 0 ⨯₃ v l n i 1) (x l n i q)) := by
  ext k
  fin_cases k <;>
    simp [CFMPOriginalInternalNormals435Transient.raw,
      CFMPCoefficientAreaDeterminant435Transient.raw,covector_scale l hl n i q,
      Matrix.mulVec_smul,smul_eq_mul]
  <;> ring

theorem raw_norm (l : Fin 6 → ℝ) (hl : ∀ j, 0 < l j)
    (M : M4) (n : Fin 20) (i : Fin 3) (q : E) :
    lorentz (CFMPOriginalInternalNormals435Transient.raw M
      (CFMPOriginalFacePairing435Transient.coefficient l n i))
      (CFMPOriginalInternalNormals435Transient.raw M
        (CFMPOriginalFacePairing435Transient.coefficient l n i)) =
    lorentz (CFMPCoefficientAreaDeterminant435Transient.raw M
        (v l n i 0 ⨯₃ v l n i 1)
        (dotProduct (v l n i 0 ⨯₃ v l n i 1) (x l n i q)))
      (CFMPCoefficientAreaDeterminant435Transient.raw M
        (v l n i 0 ⨯₃ v l n i 1)
        (dotProduct (v l n i 0 ⨯₃ v l n i 1) (x l n i q))) := by
  rw [raw_scale l hl M n i q]
  have hs (s : ℝ) (N : W) : lorentz (s • N) (s • N) = s^2 * lorentz N N := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    ring
  rw [hs,sign_sq,one_mul]

theorem original_face_density
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : M4) (hM : M.det ≠ 0)
    (hG : ∀ a b, lorentz (M a) (M b) = lengthGram l a b)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ z, ∃ y : W, y = (radial l z.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f z).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) (q : E) (hq : q ∈ parameterTriangle) :
    let U := (xi l n i q) ᵥ* M
    let db := (CFMPNativePullbackMetric435Transient.nativeMatrix U).mulVec
      (direction l n i 0 ᵥ* M)
    let dc := (CFMPNativePullbackMetric435Transient.nativeMatrix U).mulVec
      (direction l n i 1 ᵥ* M)
    let N := CFMPOriginalInternalNormals435Transient.raw M
      (CFMPOriginalFacePairing435Transient.coefficient l n i)
    Real.sqrt (dotProduct (db ⨯₃ dc) (db ⨯₃ dc)) /
      (CFMPNativePullbackMetric435Transient.nativeMap U 2)^2 =
      |M.det| * Real.sqrt (lorentz N N) /
        (Real.sqrt (CFMPNativePullbackMetric435Transient.radius U))^3 := by
  obtain ⟨A,hA,he,hplane,hs,hcols,hinj,hpositive,hchart⟩ :=
    same_reflection_chart_data l hl M hM hG f hf n i
  let R := CFMPActualTriangleNormal435Transient.reflectionLinear A
  have hR : ∀ Y Z : W, lorentz (R Y) (R Z) = lorentz Y Z := by
    intro Y Z
    simpa only [R,CFMPActualTriangleNormal435Transient.reflectionLinear_apply] using
      reflection_pair A Y Z hA.ne'
  have hbase : R (base l n ᵥ* M) 1 = 0 := by
    simpa [xi,R] using hplane 0
  have hP : R (direction l n i 0 ᵥ* M) 1 = 0 := by
    have h := hplane ![1,0]
    change R (xi l n i ![1,0] ᵥ* M) 1 = 0 at h
    simpa [xi,Matrix.add_vecMul,Matrix.smul_vecMul,map_add,map_smul,hbase] using h
  have hQ : R (direction l n i 1 ᵥ* M) 1 = 0 := by
    have h := hplane ![0,1]
    change R (xi l n i ![0,1] ᵥ* M) 1 = 0 at h
    simpa [xi,Matrix.add_vecMul,Matrix.smul_vecMul,map_add,map_smul,hbase] using h
  have hfuture := body_future_data l hl M hG f hf
    ⟨xi l n i q,xi_mem_cutBody l hl n i q hq⟩
  have hr : 0 < CFMPNativePullbackMetric435Transient.radius (xi l n i q ᵥ* M) :=
    neg_pos.mpr hfuture.1
  have hd : CFMPNativePullbackMetric435Transient.delta (xi l n i q ᵥ* M) ≠ 0 :=
    hfuture.2.2.ne'
  have hN := CFMPOriginalInternalNormals435Transient.raw_spacelike l hl M hM f hf n i
  rw [raw_norm l hl M n i q] at hN
  have h := CFMPActualCoefficientDensity435Transient.actual_face_density M hM
    (x l n i q) (v l n i 0) (v l n i 1) hN
    (by simpa only [lift_x l hl n i q] using hr)
    (by simpa only [lift_x l hl n i q] using hd) R hR
    (by simpa only [lift_x l hl n i q] using hplane q)
    (by simpa only [tangent_v l hl n i 0] using hP)
    (by simpa only [tangent_v l hl n i 1] using hQ)
  dsimp only at h ⊢
  simpa only [lift_x l hl n i q,tangent_v l hl n i 0,tangent_v l hl n i 1,
    raw_norm l hl M n i q] using h

#print axioms original_face_density
end CFMPOriginalFaceDensity435Transient
