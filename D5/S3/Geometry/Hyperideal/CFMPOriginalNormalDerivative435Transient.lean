import D5.S3.Geometry.Hyperideal.CFMPAnchoredOriginalExteriorFaceMotion435Transient
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalCellsIndependent435Transient CFMPActualCellMotion435Transient
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalExteriorFaceChart435Transient

namespace CFMPOriginalNormalDerivative435Transient

private theorem determinant_differentiable {m : Type*} [Fintype m] [DecidableEq m]
    (A : ℝ → Matrix m m ℝ) (t : ℝ)
    (hA : ∀ i j, DifferentiableAt ℝ (fun s => A s i j) t) :
    DifferentiableAt ℝ (fun s => (A s).det) t := by
  simp_rw [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro sigma _
  exact (differentiableAt_const _).mul
    (DifferentiableAt.fun_finsetProd (fun i _ => hA (sigma i) i))

private theorem inverse_differentiable {m : Type*} [Fintype m] [DecidableEq m]
    (A : ℝ → Matrix m m ℝ) (t : ℝ)
    (hA : DifferentiableAt ℝ A t) (hdet : (A t).det ≠ 0) :
    DifferentiableAt ℝ (fun s => (A s)⁻¹) t := by
  have hc (i j : m) : DifferentiableAt ℝ (fun s => A s i j) t :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hA i) j
  have hd := determinant_differentiable A t hc
  have ha (i j : m) : DifferentiableAt ℝ (fun s => (A s).adjugate i j) t := by
    simp_rw [Matrix.adjugate_apply]
    apply determinant_differentiable
    intro k r
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact differentiableAt_const _
    · exact hc k r
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  simpa -implicitDefEqProofs only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Pi.mul_def, Pi.inv_def]
    using (hd.inv hdet).mul (ha i j)

theorem exterior_covector_differentiable
    (l : ℝ → Fin 6 → ℝ) (t : ℝ) (hl : DifferentiableAt ℝ l t)
    (hpos : ∀ k, 0 < l t k) (n : Fin 20) :
    DifferentiableAt ℝ (fun s => exteriorCovector (l s) n) t := by
  have he := edgeMatrix_differentiable l t hl n
  have hd := determinant_differentiable (fun s => edgeMatrix (l s) n) t
    (fun i j => differentiableAt_pi.mp (differentiableAt_pi.mp he i) j)
  have hn := edgeMatrix_det_ne_zero (l t) hpos n
  have hi := inverse_differentiable (fun s => edgeMatrix (l s) n) t he hn
  have hi' (i j : Fin 3) :
      DifferentiableAt ℝ (fun s => (edgeMatrix (l s) n)⁻¹ i j) t :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hi i) j
  have habs : DifferentiableAt ℝ (fun s => |(edgeMatrix (l s) n).det|) t :=
    by
      simpa -implicitDefEqProofs only using hd.abs hn
  have ha (i : Fin 3) :
      DifferentiableAt ℝ (fun s => outwardCoefficient (l s) n i) t := by
    have hsum := DifferentiableAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
      (fun j _ => (hi' j i).mul_const (1 : ℝ))
    simpa -implicitDefEqProofs only [outwardCoefficient, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, Matrix.transpose_apply, dotProduct, Pi.mul_def] using habs.mul hsum
  have hv (i : Fin 3) :
      DifferentiableAt ℝ (fun s => drop (vertices (l s) n 0) i) t :=
    differentiableAt_pi.mp (vertices_differentiable l t hl n 0) i.castSucc
  have hh : DifferentiableAt ℝ (fun s => planeOffset (l s) n) t := by
    have hsum := DifferentiableAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
      (fun i _ => (ha i).mul (hv i))
    simpa -implicitDefEqProofs only [planeOffset, dotProduct, Pi.mul_def, Pi.add_def] using hsum.add habs
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · change DifferentiableAt ℝ (fun s => outwardCoefficient (l s) n 0 - planeOffset (l s) n) t
    exact (ha 0).sub hh
  · change DifferentiableAt ℝ (fun s => outwardCoefficient (l s) n 1 - planeOffset (l s) n) t
    exact (ha 1).sub hh
  · change DifferentiableAt ℝ (fun s => outwardCoefficient (l s) n 2 - planeOffset (l s) n) t
    exact (ha 2).sub hh
  · change DifferentiableAt ℝ (fun s => -planeOffset (l s) n) t
    exact hh.neg

theorem raw_differentiable
    (l : ℝ → Fin 6 → ℝ) (t : ℝ) (hl : DifferentiableAt ℝ l t)
    (hpos : ∀ k, 0 < l t k) (P : ℝ → M4)
    (hP : DifferentiableAt ℝ P t) (hdet : (P t).det ≠ 0) (n : Fin 20) :
    DifferentiableAt ℝ (fun s =>
      CFMPOriginalExteriorNativeNormal435Transient.raw (l s) (P s) n) t := by
  have hi := inverse_differentiable P t hP hdet
  have hi' (i j : Fin 4) : DifferentiableAt ℝ (fun s => (P s)⁻¹ i j) t :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hi i) j
  have hc := exterior_covector_differentiable l t hl hpos n
  have hc' (i : Fin 4) : DifferentiableAt ℝ (fun s => exteriorCovector (l s) n i) t :=
    differentiableAt_pi.mp hc i
  have hz (i : Fin 4) : DifferentiableAt ℝ
      (fun s => ((P s)⁻¹ *ᵥ exteriorCovector (l s) n) i) t := by
    have hsum := DifferentiableAt.fun_sum (u := (Finset.univ : Finset (Fin 4)))
      (fun j _ => (hi' i j).mul (hc' j))
    simpa -implicitDefEqProofs only [Matrix.mulVec, dotProduct, Pi.mul_def] using hsum
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · change DifferentiableAt ℝ (fun s => ((P s)⁻¹ *ᵥ exteriorCovector (l s) n) 0) t
    exact hz 0
  · change DifferentiableAt ℝ (fun s => ((P s)⁻¹ *ᵥ exteriorCovector (l s) n) 1) t
    exact hz 1
  · change DifferentiableAt ℝ (fun s => ((P s)⁻¹ *ᵥ exteriorCovector (l s) n) 2) t
    exact hz 2
  · change DifferentiableAt ℝ (fun s => -((P s)⁻¹ *ᵥ exteriorCovector (l s) n) 3) t
    exact (hz 3).neg

private theorem normalized_pair (v : Fin 4 → ℝ) (hp : 0 < lorentz v v) :
    lorentz ((Real.sqrt (lorentz v v))⁻¹ • v)
      ((Real.sqrt (lorentz v v))⁻¹ • v) = 1 := by
  let r := Real.sqrt (lorentz v v)
  have hr : r ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hs : r^2 = lorentz v v := Real.sq_sqrt hp.le
  calc
    _ = r⁻¹^2 * lorentz v v := by
      simp [r,lorentz,Fin.sum_univ_four,smul_eq_mul]
      <;> ring
    _ = 1 := by rw [← hs]; field_simp

theorem actual_normal_derivative
    (l0 : Fin 6 → ℝ) (hl0 : ∀ k, 0 < l0 k)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (l : ℝ → Fin 6 → ℝ) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0) (n : Fin 20) :
    let N : ℝ → Fin 4 → ℝ := fun s =>
      CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (frame M0 (l s)) n
    N t = CFMPOriginalExteriorNativeNormal435Transient.unit l0 M0 n ∧
      DifferentiableAt ℝ N t ∧
      HasDerivAt N (deriv N t) t ∧ lorentz (N t) (deriv N t) = 0 := by
  let P : ℝ → M4 := fun s => frame M0 (l s)
  let R : ℝ → Fin 4 → ℝ := fun s =>
    CFMPOriginalExteriorNativeNormal435Transient.raw (l s) (P s) n
  let N : ℝ → Fin 4 → ℝ := fun s =>
    CFMPOriginalExteriorNativeNormal435Transient.unit (l s) (P s) n
  have hgood : good (H M0 l0) := by
    rw [normalized_base M0 hm0 l0 hg0]
    exact base.2
  have hframe : DifferentiableAt ℝ (frame M0) (l t) := by
    rw [hbase]
    exact (smooth_frame M0 l0 hgood).differentiableAt (by simp)
  have hP : DifferentiableAt ℝ P t := hframe.comp t hl.differentiableAt
  have hPt : P t = M0 := by
    dsimp only [P]
    rw [hbase,anchored M0 hm0 l0 hg0]
  have hraw := raw_differentiable l t hl.differentiableAt
    (by simpa only [hbase] using hl0) P hP (by simpa only [hPt] using hm0) n
  have hpos : 0 < lorentz (R t) (R t) := by
    dsimp only [R]
    rw [hbase,hPt]
    exact CFMPOriginalExteriorNativeNormal435Transient.raw_spacelike
      l0 hl0 M0 hm0
      (CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows M0 l0 hg0) f hf n
  have hcoord (i : Fin 4) : DifferentiableAt ℝ (fun s => R s i) t :=
    differentiableAt_pi.mp hraw i
  have hquad : DifferentiableAt ℝ (fun s => lorentz (R s) (R s)) t := by
    unfold lorentz
    fun_prop
  have hnorm : DifferentiableAt ℝ N t :=
    ((hquad.sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne').smul hraw
  have hevent : (fun s => -lorentz (N s) (N s)) =ᶠ[𝓝 t] (fun _ => (-1 : ℝ)) := by
    filter_upwards [hquad.continuousAt.eventually (Ioi_mem_nhds hpos)] with s hs
    change -lorentz ((Real.sqrt (lorentz (R s) (R s)))⁻¹ • R s)
      ((Real.sqrt (lorentz (R s) (R s)))⁻¹ • R s) = -1
    rw [normalized_pair (R s) hs]
  have hpair := CFMPFrameContinuity435Transient.lorentz_curve
    N (deriv N t) t hnorm.hasDerivAt
  have hconstant : HasDerivAt (fun _ : ℝ => (-1 : ℝ))
      (-2 * lorentz (N t) (deriv N t)) t :=
    hpair.congr_of_eventuallyEq hevent.symm
  have hz := hconstant.unique (hasDerivAt_const t (-1 : ℝ))
  refine ⟨?_,hnorm,hnorm.hasDerivAt,?_⟩
  · change CFMPOriginalExteriorNativeNormal435Transient.unit (l t) (P t) n = _
    rw [hbase,hPt]
  · linarith

end CFMPOriginalNormalDerivative435Transient

run_cmd do
  for name in [``CFMPOriginalNormalDerivative435Transient.exterior_covector_differentiable,
      ``CFMPOriginalNormalDerivative435Transient.raw_differentiable,
      ``CFMPOriginalNormalDerivative435Transient.actual_normal_derivative] do
    let env := (← Lean.getEnv).setExporting false
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP590 declaration absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP590 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP590 CHECKED {name} axioms={axioms}"
