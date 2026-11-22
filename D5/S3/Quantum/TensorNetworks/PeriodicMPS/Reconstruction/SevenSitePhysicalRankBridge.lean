/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSitePhysicalRankBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSitePhysicalRankBridge
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Differentiable covers of the seven-site physical critical slice. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteReadoutDerivative
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalCharZero
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Ordinary-coordinate suppliers for the physical differential calculation. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSitePhysicalRankBridge

open Function Set Filter Matrix MvPolynomial
open scoped BigOperators Matrix Kronecker Matrix.Norms.Elementwise ComplexConjugate Topology
open PeriodicMPSUniformHardCoreLocalization (twoSiteObservation twoSiteObservation_traceWord)
open PeriodicMPSUniformHardCoreMarginalWitness (pairGram mass_eq_trace)
open PeriodicMPSProjectiveCoordinates (projector mass mass_pos)
open PeriodicMPSCompactReadout
  (Readout readout normalizedMarginal_mem normalizedExchangeMarginals
    eq_of_readout_of_trace_eq)
open PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open PeriodicMPSAmbiguityDensity (changePhysical pairBasis changePhysical_unitary_raw)
open PeriodicMPSUniformHardCorePencilDecoder (det_pencil_binary crossDet)
open PeriodicMPSUniformDeterminantPencil (pencil)
open SevenSiteTraceBase (amplitude differentiable_amplitude)
open SevenSiteCriticalCertificate
  (V observedRow rotationIndex map_slicedObservation alignedInvariants sliceBlock criticalMatrix
    seven_site_critical_slice_cover)
open SevenSiteReadoutDerivative
  (injective_fderiv_normalized_iff observedRows_eq_rawReadout)

open private pauliFrame pauli_explicit
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.TwoQubitMarginalReflection
open private rawTwo_scaled from D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity

noncomputable section

/-- The second trace, the two determinants, and the mixed trace at first trace one. -/
abbrev Ordinary := ℂ × ℂ × ℂ × ℂ

/-- In the aligned coordinates the first entry records the original trace line. -/
abbrev Aligned := ℂ × ℂ × ℂ × ℂ

abbrev SlicePoint := Fin 5 → ℝ
abbrev Rotation := ℝ × ℝ × ℝ

private abbrev Core := Fin 2 → PeriodicMPSParentIntersection.Bond

private def H (s : ℂ) : ℂ := 1 + Complex.conjCLE s * s

private theorem H_ne_zero (s : ℂ) : H s ≠ 0 := by
  have h : (H s).re = 1 + (s.re ^ 2 + s.im ^ 2) := by
    simp [H, Complex.conjCLE_apply, Complex.mul_re] <;> ring
  intro hs
  rw [hs] at h
  simp only [Complex.zero_re] at h
  nlinarith [sq_nonneg s.re, sq_nonneg s.im]

/-- Determinant-pencil coefficients after aligning the trace line, with its
residual physical phase still free. -/
def align (p : Ordinary) : Aligned :=
  let (s, d, e, k) := p
  let b := Complex.conjCLE s
  let m := s - k
  (s, (d + m * b + e * b ^ 2) / H s ^ 2,
    (d * s ^ 2 - m * s + e) / H s ^ 2,
    (2 * d * s - m * (1 - b * s) - 2 * e * b) / H s ^ 2)

/-- Inverse substitution in the binary determinant pencil. -/
def unalign (p : Aligned) : Ordinary :=
  let (s, d, e, k) := p
  let b := Complex.conjCLE s
  (s, d + k * b + e * b ^ 2, d * s ^ 2 - k * s + e,
    s - (2 * d * s - k * (1 - b * s) - 2 * e * b))

@[simp] theorem align_unalign (p : Aligned) : align (unalign p) = p := by
  rcases p with ⟨s, d, e, k⟩
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
    dsimp only [align, unalign] <;> field_simp [H_ne_zero] <;> simp only [H] <;> ring

@[simp] theorem unalign_align (p : Ordinary) : unalign (align p) = p := by
  rcases p with ⟨s, d, e, k⟩
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
    dsimp only [align, unalign] <;> field_simp [H_ne_zero] <;> simp only [H] <;> ring

theorem differentiable_unalign : Differentiable ℝ unalign := by
  unfold unalign
  dsimp only
  fun_prop

/-- The entire aligned mixed-trace zero sector has a single differentiable
parametrization from three complex coordinates. -/
theorem image_zeroMixed :
    (fun p : ℂ × ℂ × ℂ => unalign (p.1, p.2.1, p.2.2, 0)) '' univ =
      {p : Ordinary | (align p).2.2.2 = 0} := by
  ext p
  constructor
  · rintro ⟨q, -, rfl⟩
    simp only [mem_setOf_eq, align_unalign]
  · intro hp
    let q := align p
    have hq : q.2.2.2 = 0 := hp
    refine ⟨(q.1, q.2.1, q.2.2.1), mem_univ _, ?_⟩
    change unalign (q.1, q.2.1, q.2.2.1, 0) = p
    rw [← hq]
    exact unalign_align p

theorem differentiable_zeroMixed :
    Differentiable ℝ (fun p : ℂ × ℂ × ℂ => unalign (p.1, p.2.1, p.2.2, 0)) :=
  differentiable_unalign.comp (by fun_prop)

private def phase (c : ℝ) : ℂ :=
  Complex.ofRealCLM ((1 - (c / 2) ^ 2) / (1 + (c / 2) ^ 2)) +
    Complex.I * Complex.ofRealCLM (c / (1 + (c / 2) ^ 2))

private theorem phase_re (c : ℝ) : (phase c).re = (1 - (c / 2) ^ 2) / (1 + (c / 2) ^ 2) := by
  simp only [phase, Complex.ofRealCLM_apply, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]

private theorem phase_im (c : ℝ) : (phase c).im = c / (1 + (c / 2) ^ 2) := by
  simp only [phase, Complex.ofRealCLM_apply, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, add_zero]

private theorem phase_zero : phase 0 = 1 := by
  norm_num [phase, Complex.ofRealCLM_apply]

private theorem phase_normSq (c : ℝ) : Complex.normSq (phase c) = 1 := by
  rw [Complex.normSq_apply, phase_re, phase_im]
  set u : ℝ := c / 2 with hu
  have hc : c = 2 * u := by rw [hu]; ring
  have hh : 1 + u ^ 2 ≠ 0 := by positivity
  rw [hc]
  field_simp [hh] <;> ring

private theorem phase_arg_denom (c : ℝ) : 1 + (phase c).re = 2 / (1 + (c / 2) ^ 2) := by
  rw [phase_re]
  set u : ℝ := (c / 2) ^ 2 with hu
  have hh : 1 + u ≠ 0 := by rw [hu]; positivity
  field_simp [hh] <;> ring

private theorem phase_arg_denom_ne (c : ℝ) : 1 + (phase c).re ≠ 0 := by
  rw [phase_arg_denom]
  exact div_ne_zero (by norm_num) (by positivity)

private theorem phase_arg (c : ℝ) : 2 * (phase c).im / (1 + (phase c).re) = c := by
  have hh : 1 + (c / 2) ^ 2 ≠ 0 := by positivity
  apply (div_eq_iff (phase_arg_denom_ne c)).2
  rw [phase_im, phase_arg_denom]
  set D : ℝ := 1 + (c / 2) ^ 2
  have hD : D ≠ 0 := hh
  field_simp [hD] <;> ring

private theorem analyticAt_phase (c : ℝ) : AnalyticAt ℝ phase c := by
  have hid : AnalyticAt ℝ (fun t : ℝ => t) c := analyticAt_id
  have hq : AnalyticAt ℝ (fun t : ℝ => (t / 2) ^ 2) c :=
    (hid.div_const (c := 2)).fun_pow 2
  have hOne : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) c := analyticAt_const
  have hD := hOne.fun_add hq
  have hD₀ : 1 + (c / 2) ^ 2 ≠ 0 := by positivity
  have hre := (hOne.fun_sub hq).fun_div hD hD₀
  have him := hid.fun_div hD hD₀
  exact ((Complex.ofRealCLM.analyticAt _).comp hre).fun_add
    ((analyticAt_const (v := Complex.I)).fun_mul ((Complex.ofRealCLM.analyticAt _).comp him))

/-- The three real rotation variables and the five certificate slice variables
in the ordinary trace chart. Taking the center phase to be either sign
covers the circle by two stereographic charts. -/
def physicalChart (centerPhase : ℂ) (v : Rotation × SlicePoint) : Ordinary :=
  let a := Complex.ofRealCLM v.1.1
  let b := Complex.ofRealCLM v.1.2.1
  let l := centerPhase * phase v.1.2.2
  let d := Complex.ofRealCLM (v.2 0) + Complex.I * Complex.ofRealCLM (v.2 3)
  let e := Complex.ofRealCLM (v.2 2) + Complex.I * Complex.ofRealCLM (v.2 4)
  unalign ((b - Complex.I * a) / 2, d, l ^ 2 * e, l * Complex.ofRealCLM (v.2 1))

@[simp] theorem physicalChart_center (x : SlicePoint) :
    physicalChart 1 (0, x) =
      (0, (x 0 : ℂ) + Complex.I * (x 3 : ℂ),
        (x 2 : ℂ) + Complex.I * (x 4 : ℂ), (x 1 : ℂ)) := by
  simp [physicalChart, phase, unalign, Complex.conjCLE_apply, Complex.ofRealCLM_apply]

private theorem analyticAt_unalign (p : Aligned) : AnalyticAt ℝ unalign p := by
  have hs : AnalyticAt ℝ (fun q : Aligned => q.1) p := analyticAt_fst
  have h₁ : AnalyticAt ℝ (fun q : Aligned => q.2) p := analyticAt_snd
  have hd : AnalyticAt ℝ (fun q : Aligned => q.2.1) p := analyticAt_fst.comp h₁
  have h₂ : AnalyticAt ℝ (fun q : Aligned => q.2.2) p := analyticAt_snd.comp h₁
  have he : AnalyticAt ℝ (fun q : Aligned => q.2.2.1) p := analyticAt_fst.comp h₂
  have hk : AnalyticAt ℝ (fun q : Aligned => q.2.2.2) p := analyticAt_snd.comp h₂
  have hb : AnalyticAt ℝ (fun q : Aligned => Complex.conjCLE q.1) p :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).analyticAt p.1).comp hs
  have hOne : AnalyticAt ℝ (fun _ : Aligned => (1 : ℂ)) p := analyticAt_const
  have hTwo : AnalyticAt ℝ (fun _ : Aligned => (2 : ℂ)) p := analyticAt_const
  have hd' := (hd.fun_add (hk.fun_mul hb)).fun_add (he.fun_mul (hb.fun_pow 2))
  have he' := ((hd.fun_mul (hs.fun_pow 2)).fun_sub (hk.fun_mul hs)).fun_add he
  have hk' := ((hTwo.fun_mul hd).fun_mul hs).fun_sub
    (hk.fun_mul (hOne.fun_sub (hb.fun_mul hs)))
  unfold unalign
  dsimp only
  exact hs.prod (hd'.prod (he'.prod (hs.fun_sub (hk'.fun_sub ((hTwo.fun_mul he).fun_mul hb)))))

theorem analyticAt_physicalChart (l : ℂ) (v : Rotation × SlicePoint) :
    AnalyticAt ℝ (physicalChart l) v := by
  have hRotation : AnalyticAt ℝ (fun w : Rotation × SlicePoint => w.1) v := analyticAt_fst
  have hTail : AnalyticAt ℝ (fun w : Rotation × SlicePoint => w.1.2) v :=
    analyticAt_snd.comp hRotation
  have ha : AnalyticAt ℝ (fun w : Rotation × SlicePoint => w.1.1) v :=
    analyticAt_fst.comp hRotation
  have hb : AnalyticAt ℝ (fun w : Rotation × SlicePoint => w.1.2.1) v :=
    analyticAt_fst.comp hTail
  have hc : AnalyticAt ℝ (fun w : Rotation × SlicePoint => w.1.2.2) v :=
    analyticAt_snd.comp hTail
  have hSlice : AnalyticAt ℝ (fun w : Rotation × SlicePoint => w.2) v := analyticAt_snd
  have hx (i : Fin 5) :
      AnalyticAt ℝ (fun w : Rotation × SlicePoint => Complex.ofRealCLM (w.2 i)) v := by
    have hcoord : AnalyticAt ℝ (fun w : Rotation × SlicePoint => w.2 i) v :=
      ((ContinuousLinearMap.proj i : SlicePoint →L[ℝ] ℝ).analyticAt v.2).comp hSlice
    exact AnalyticAt.comp (f := fun w : Rotation × SlicePoint => w.2 i)
      (Complex.ofRealCLM.analyticAt (v.2 i)) hcoord
  have hI : AnalyticAt ℝ (fun _ : Rotation × SlicePoint => Complex.I) v := analyticAt_const
  have hl₀ : AnalyticAt ℝ (fun _ : Rotation × SlicePoint => l) v := analyticAt_const
  have hs := (((Complex.ofRealCLM.analyticAt _).comp hb).fun_sub
    (hI.fun_mul ((Complex.ofRealCLM.analyticAt _).comp ha))).div_const (c := 2)
  have hphase : AnalyticAt ℝ (fun w : Rotation × SlicePoint => phase w.1.2.2) v :=
    AnalyticAt.comp (f := fun w : Rotation × SlicePoint => w.1.2.2)
      (analyticAt_phase v.1.2.2) hc
  have hl := hl₀.fun_mul hphase
  have hd := (hx 0).fun_add (hI.fun_mul (hx 3))
  have he := (hx 2).fun_add (hI.fun_mul (hx 4))
  unfold physicalChart
  exact (analyticAt_unalign _).comp
    (hs.prod (hd.prod (((hl.fun_pow 2).fun_mul he).prod (hl.fun_mul (hx 1)))))

private def inversePhysicalChart (p : Ordinary) : Rotation × SlicePoint :=
  let (s, d, E, K) := align p
  let r := Real.sqrt (Complex.normSq K)
  let l := K / Complex.ofRealCLM r
  let e := E / l ^ 2
  ((-2 * Complex.imCLM s, 2 * Complex.reCLM s,
    2 * Complex.imCLM l / (1 + Complex.reCLM l)),
    ![Complex.reCLM d, r, Complex.reCLM e, Complex.imCLM d, Complex.imCLM e])

private theorem inverse_physicalChart (v : Rotation × SlicePoint) (hv : 0 < v.2 1) :
    inversePhysicalChart (physicalChart 1 v) = v := by
  rcases v with ⟨⟨a, b, c⟩, x⟩
  simp only at hv
  have hx : (x 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hr : Real.sqrt (Complex.normSq (phase c * (x 1 : ℂ))) = x 1 := by
    rw [Complex.normSq_mul, phase_normSq, one_mul, Complex.normSq_ofReal]
    simpa [pow_two] using Real.sqrt_sq hv.le
  have hl : phase c * (x 1 : ℂ) / (x 1 : ℂ) = phase c :=
    mul_div_cancel_right₀ _ hx
  have hphase : phase c ≠ 0 := by
    intro h
    simpa [h, Complex.normSq_zero] using phase_normSq c
  simp only [physicalChart, inversePhysicalChart, align_unalign, one_mul, Complex.ofRealCLM_apply,
    hr, hl, mul_div_cancel_left₀ _ (pow_ne_zero 2 hphase), Complex.reCLM_apply,
    Complex.imCLM_apply, phase_arg]
  apply Prod.ext
  · refine Prod.ext ?_ (Prod.ext ?_ rfl) <;>
      simp [Complex.mul_re, Complex.mul_im, div_eq_mul_inv, Complex.inv_re, Complex.inv_im,
        Complex.normSq_apply] <;> ring
  · funext i
    fin_cases i <;> simp [Complex.mul_re, Complex.mul_im]

private theorem differentiableAt_align (p : Ordinary) : DifferentiableAt ℝ align p := by
  have hD : DifferentiableAt ℝ (fun z : Ordinary => H z.1 ^ 2) p := by
    unfold H
    fun_prop
  have hD₀ : H p.1 ^ 2 ≠ 0 := pow_ne_zero 2 (H_ne_zero p.1)
  unfold align
  dsimp only
  refine DifferentiableAt.prodMk (by fun_prop)
    (DifferentiableAt.prodMk ?_ (DifferentiableAt.prodMk ?_ ?_))
  all_goals
    simp only [div_eq_mul_inv]
    refine DifferentiableAt.fun_mul ?_ (hD.inv hD₀)
    fun_prop

private theorem differentiableAt_inversePhysicalChart (p : Ordinary)
    (hK : (align p).2.2.2 ≠ 0)
    (hphase : 1 + ((align p).2.2.2 /
      (Real.sqrt (Complex.normSq (align p).2.2.2) : ℂ)).re ≠ 0) :
    DifferentiableAt ℝ inversePhysicalChart p := by
  let q := align p
  let r (z : Aligned) := Real.sqrt (Complex.normSq z.2.2.2)
  let l (z : Aligned) := z.2.2.2 / Complex.ofRealCLM (r z)
  let e (z : Aligned) := z.2.2.1 / l z ^ 2
  let decode (z : Aligned) : Rotation × SlicePoint :=
    ((-2 * Complex.imCLM z.1, 2 * Complex.reCLM z.1,
      2 * Complex.imCLM (l z) / (1 + Complex.reCLM (l z))),
      ![Complex.reCLM z.2.1, r z, Complex.reCLM (e z), Complex.imCLM z.2.1,
        Complex.imCLM (e z)])
  have hnorm : 0 < Complex.normSq q.2.2.2 := Complex.normSq_pos.2 hK
  have hr₀ : Complex.ofRealCLM (r q) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hnorm).ne'
  have hnormSq : DifferentiableAt ℝ (fun z : Aligned => Complex.normSq z.2.2.2) q := by
    simp only [Complex.normSq_apply]
    fun_prop
  have hr : DifferentiableAt ℝ r q := hnormSq.sqrt hnorm.ne'
  have hrComplex : DifferentiableAt ℝ (fun z : Aligned => Complex.ofRealCLM (r z)) q :=
    Complex.ofRealCLM.differentiableAt.comp q hr
  have hdiffK : DifferentiableAt ℝ (fun z : Aligned => z.2.2.2) q := by fun_prop
  have hl : DifferentiableAt ℝ l q := by
    simp only [l, div_eq_mul_inv]
    exact hdiffK.fun_mul (hrComplex.inv hr₀)
  have hl₀ : l q ≠ 0 := div_ne_zero hK hr₀
  have hdiffE : DifferentiableAt ℝ (fun z : Aligned => z.2.2.1) q := by fun_prop
  have he : DifferentiableAt ℝ e q := by
    simp only [e, div_eq_mul_inv]
    exact hdiffE.fun_mul ((hl.fun_pow 2).inv (pow_ne_zero 2 hl₀))
  have hRe := Complex.reCLM.differentiableAt.comp q hl
  have hIm := Complex.imCLM.differentiableAt.comp q hl
  have harg : 1 + Complex.reCLM (l q) ≠ 0 := hphase
  have hdecode : DifferentiableAt ℝ decode q := by
    dsimp only [decode]
    refine DifferentiableAt.prodMk
      (DifferentiableAt.prodMk (by fun_prop) (DifferentiableAt.prodMk (by fun_prop) ?_)) ?_
    · simp only [div_eq_mul_inv]
      exact (hIm.const_mul 2).fun_mul ((DifferentiableAt.const_add 1 hRe).inv harg)
    · apply differentiableAt_pi.mpr
      intro i
      fin_cases i
      · change DifferentiableAt ℝ (fun z : Aligned => Complex.reCLM z.2.1) q
        fun_prop
      · exact hr
      · exact Complex.reCLM.differentiableAt.comp q he
      · change DifferentiableAt ℝ (fun z : Aligned => Complex.imCLM z.2.1) q
        fun_prop
      · exact Complex.imCLM.differentiableAt.comp q he
  have hfactor : inversePhysicalChart = decode ∘ align := by
    funext z
    change inversePhysicalChart z = decode (align z)
    unfold inversePhysicalChart
    generalize align z = w
    rcases w with ⟨s, d, E, K⟩
    rfl
  rw [hfactor]
  exact hdecode.comp p (differentiableAt_align p)

/-- At the aligned positive slice the rotation-and-slice chart has all
eight real tangent directions. -/
theorem bijective_fderiv_physicalChart_center (x : SlicePoint) (hx : 0 < x 1) :
    Bijective (fderiv ℝ (physicalChart 1) ((0 : Rotation), x)) := by
  let v : Rotation × SlicePoint := (0, x)
  let p := physicalChart 1 v
  have ha : align p =
      (0, (x 0 : ℂ) + Complex.I * (x 3 : ℂ),
        (x 2 : ℂ) + Complex.I * (x 4 : ℂ), (x 1 : ℂ)) := by
    rw [show p = physicalChart 1 (0, x) from rfl, physicalChart_center]
    simp [align, H]
  have hK : (align p).2.2.2 ≠ 0 := by
    rw [ha]
    exact Complex.ofReal_ne_zero.mpr hx.ne'
  have hl : 1 + ((align p).2.2.2 /
      (Real.sqrt (Complex.normSq (align p).2.2.2) : ℂ)).re ≠ 0 := by
    rw [ha]
    dsimp only
    rw [Complex.normSq_ofReal, show Real.sqrt (x 1 * x 1) = x 1 from
      by simpa [pow_two] using Real.sqrt_sq hx.le, div_self (Complex.ofReal_ne_zero.mpr hx.ne')]
    norm_num
  let F := fderiv ℝ (physicalChart 1) v
  let G := fderiv ℝ inversePhysicalChart p
  have hF : HasFDerivAt (physicalChart 1) F v :=
    (analyticAt_physicalChart 1 v).differentiableAt.hasFDerivAt
  have hG : HasFDerivAt inversePhysicalChart G p :=
    (differentiableAt_inversePhysicalChart p hK hl).hasFDerivAt
  have hE : inversePhysicalChart ∘ physicalChart 1 =ᶠ[𝓝 v] id := by
    have h : ContinuousAt (fun w : Rotation × SlicePoint => w.2 1) v := by fun_prop
    exact (h.eventually (lt_mem_nhds hx)).mono fun w hw => inverse_physicalChart w hw
  have hcomp : G.comp F = ContinuousLinearMap.id ℝ (Rotation × SlicePoint) := by
    rw [← (hG.comp v hF).fderiv, hE.fderiv_eq, fderiv_id]
  have hinj : Injective F := by
    intro y z h
    simpa only [← ContinuousLinearMap.comp_apply, hcomp, ContinuousLinearMap.id_apply] using
      congrArg G h
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Rotation, SlicePoint, Ordinary, Module.finrank_prod, Module.finrank_pi,
      Complex.finrank_real_complex])).mp (show Injective F.toLinearMap from hinj)⟩

/-- The physical frame before division by the positive norm of its first column. -/
def sectionMatrix (s l : ℂ) : PeriodicMPSParentIntersection.Bond :=
  !![1, -Complex.conjCLE s * l; s, l]

/-- The coordinate line for one of the three physical rotation directions. -/
def rotationLine (j : Fin 3) (t : ℝ) : Rotation :=
  ![(t, 0, 0), (0, t, 0), (0, 0, t)] j

private def centeredFrame (v : Rotation) : PeriodicMPSParentIntersection.Bond :=
  sectionMatrix ((Complex.ofRealCLM v.2.1 - Complex.I * Complex.ofRealCLM v.1) / 2)
    (phase v.2.2)

private def frameTangent (j : Fin 3) : PeriodicMPSParentIntersection.Bond :=
  (-Complex.I / 2) • pauliFrame j.succ +
    if j = 2 then (Complex.I / 2) • (1 : PeriodicMPSParentIntersection.Bond) else 0

private theorem hasDerivAt_phase : HasDerivAt phase Complex.I 0 := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id' 0
  have hOne : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const _ _
  have hq : HasDerivAt (fun t : ℝ => (t / 2) ^ 2) 0 0 := by
    simpa only [Nat.reduceSub, zero_div, pow_one, mul_zero, zero_mul] using!
      (hid.div_const 2).fun_pow 2
  have hn : HasDerivAt (fun t : ℝ => 1 - (t / 2) ^ 2) 0 0 := by
    simpa only [sub_zero] using! hOne.fun_sub hq
  have hh : HasDerivAt (fun t : ℝ => 1 + (t / 2) ^ 2) 0 0 := by
    simpa only [add_zero] using! hOne.fun_add hq
  have hh₀ : 1 + ((0 : ℝ) / 2) ^ 2 ≠ 0 := by positivity
  have hre : HasDerivAt (fun t : ℝ => (1 - (t / 2) ^ 2) / (1 + (t / 2) ^ 2)) 0 0 := by
    simpa only [zero_mul, mul_zero, sub_zero, zero_div] using! hn.fun_div hh hh₀
  have him : HasDerivAt (fun t : ℝ => t / (1 + (t / 2) ^ 2)) 1 0 := by
    simpa only [zero_div, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, mul_zero, mul_one,
      sub_zero, one_pow, div_one] using! hid.fun_div hh hh₀
  simpa only [phase, Complex.ofRealCLM_apply, Complex.ofReal_zero, Complex.ofReal_one,
    mul_one, zero_add] using! hre.ofReal_comp.fun_add (him.ofReal_comp.const_mul Complex.I)

/-- Entrywise jet of the unnormalized physical section. The Z direction
contains a scalar imaginary term, which cancels in conjugation. -/
theorem hasDerivAt_centeredFrame (j : Fin 3) (a b : Fin 2) :
    HasDerivAt (fun t : ℝ => centeredFrame (rotationLine j t) a b)
      (frameTangent j a b) 0 := by
  have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa only [Complex.ofReal_one] using! (hasDerivAt_id' (0 : ℝ)).ofReal_comp
  have hx : HasDerivAt (fun t : ℝ => (0 - Complex.I * (t : ℂ)) / 2) (-Complex.I / 2) 0 := by
    simpa only [mul_one, zero_sub] using! ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).fun_sub
      (hcast.const_mul Complex.I)).div_const 2
  have hy : HasDerivAt (fun t : ℝ => (t : ℂ) / 2) (1 / 2) 0 := hcast.div_const 2
  have hconjX : HasDerivAt (fun t : ℝ => -Complex.conjCLE ((0 - Complex.I * (t : ℂ)) / 2))
      (-Complex.I / 2) 0 := by
    have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 hx
    simpa [Complex.conjCLE_apply, Function.comp_def, map_div₀, map_ofNat, neg_div] using!
      h.fun_neg
  have hconjY : HasDerivAt (fun t : ℝ => -Complex.conjCLE ((t : ℂ) / 2)) (-1 / 2) 0 := by
    have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0 hy
    simpa [Complex.conjCLE_apply, Function.comp_def, map_div₀, map_ofNat, neg_div] using!
      h.fun_neg
  have hT (i : Fin 3) : frameTangent i =
      (![!![0, -Complex.I / 2; -Complex.I / 2, 0], !![0, -1 / 2; 1 / 2, 0],
        !![0, 0; 0, Complex.I]] : Fin 3 → PeriodicMPSParentIntersection.Bond) i := by
    simp only [frameTangent, pauliFrame, Fin.cases_succ, pauli_explicit]
    ext u v
    fin_cases i <;> fin_cases u <;> fin_cases v <;>
      norm_num [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        div_mul_eq_mul_div₀, neg_mul, mul_neg, Complex.I_mul_I] <;>
      ring
  rw [hT j]
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [centeredFrame, rotationLine, sectionMatrix, phase_zero, Complex.ofRealCLM_apply] <;>
    first
    | exact hasDerivAt_const _ _
    | simpa using! hx
    | simpa using! hy
    | simpa using! hconjX
    | simpa using! hconjY
    | exact hasDerivAt_phase

private theorem trace_mul_self (A : PeriodicMPSParentIntersection.Bond) :
    (A * A).trace = A.trace ^ 2 - 2 * A.det := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The analytic ordinary chart is induced by an actual physical mixing of
the two aligned cores and the first trace of the resulting pair is one. -/
theorem sectionMatrix_invariants (A : Core) (ht : (A 0).trace = 1) (hs : (A 1).trace = 0)
    (s l : ℂ) :
    let B := changePhysical (sectionMatrix s l) A
    (B 0).trace = 1 ∧
      ((B 1).trace, (B 0).det, (B 1).det, (B 0 * B 1).trace) =
        unalign (s, (A 0).det, l ^ 2 * (A 1).det, l * (A 0 * A 1).trace) := by
  let B := changePhysical (sectionMatrix s l) A
  change (B 0).trace = 1 ∧
    ((B 1).trace, (B 0).det, (B 1).det, (B 0 * B 1).trace) = _
  have h₀ : B 0 = A 0 + (-Complex.conjCLE s * l) • A 1 := by
    simp [B, sectionMatrix, changePhysical, Fin.sum_univ_two]
  have h₁ : B 1 = s • A 0 + l • A 1 := by
    simp [B, sectionMatrix, changePhysical, Fin.sum_univ_two]
  refine ⟨by simp [h₀, Matrix.trace_add, Matrix.trace_smul, ht, hs],
    Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))⟩
  · change (B 1).trace = s
    rw [h₁]
    simp [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, ht, hs]
  · change (B 0).det = (A 0).det + (l * (A 0 * A 1).trace) * Complex.conjCLE s +
      (l ^ 2 * (A 1).det) * (Complex.conjCLE s) ^ 2
    have h := det_pencil_binary A 1 (-Complex.conjCLE s * l)
    simp only [pencil, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, crossDet,
      ht, hs, mul_zero, zero_sub, one_pow, mul_one] at h
    rw [h₀, h]
    ring
  · change (B 1).det = (A 0).det * s ^ 2 - (l * (A 0 * A 1).trace) * s +
      l ^ 2 * (A 1).det
    have h := det_pencil_binary A s l
    simp only [pencil, Matrix.cons_val_zero, Matrix.cons_val_one, crossDet,
      ht, hs, mul_zero, zero_sub] at h
    rw [h₁, h]
    ring
  · change (B 0 * B 1).trace = s - (2 * (A 0).det * s -
      (l * (A 0 * A 1).trace) * (1 - Complex.conjCLE s * s) -
      2 * (l ^ 2 * (A 1).det) * Complex.conjCLE s)
    rw [h₀, h₁]
    simp only [add_mul, mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_add,
      Matrix.trace_smul, smul_eq_mul, trace_mul_self, ht, hs,
      Matrix.trace_mul_comm (A 1) (A 0)]
    ring

private theorem sectionMatrix_gram {s l : ℂ} (hl : Complex.normSq l = 1) :
    (sectionMatrix s l)ᴴ * sectionMatrix s l =
      H s • (1 : PeriodicMPSParentIntersection.Bond) := by
  have h : (starRingEnd ℂ) l * l = 1 := by
    rw [mul_comm, Complex.mul_conj, hl, Complex.ofReal_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectionMatrix, H, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    first | ring1 | linear_combination (1 + s * (starRingEnd ℂ) s) * h

private def sectionNorm (s : ℂ) : ℝ := Real.sqrt (1 + Complex.normSq s)

private theorem sectionNorm_pos (s : ℂ) : 0 < sectionNorm s :=
  Real.sqrt_pos.2 (by linarith [Complex.normSq_nonneg s])

private theorem sectionNorm_sq (s : ℂ) : (sectionNorm s : ℂ) ^ 2 = H s := by
  rw [← Complex.ofReal_pow, sectionNorm, Real.sq_sqrt (by linarith [Complex.normSq_nonneg s])]
  simp only [H, Complex.conjCLE_apply, Complex.ofReal_add, Complex.ofReal_one]
  rw [mul_comm, Complex.mul_conj]

/-- A literal unitary lift of the trace direction and residual phase. -/
def sectionUnitary (s l : ℂ) (hl : Complex.normSq l = 1) :
    Matrix.unitaryGroup (Fin 2) ℂ := by
  let r := (sectionNorm s : ℂ)
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.2 (sectionNorm_pos s).ne'
  refine ⟨r⁻¹ • sectionMatrix s l, Matrix.mem_unitaryGroup_iff'.2 ?_⟩
  rw [Matrix.star_eq_conjTranspose]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, sectionMatrix_gram hl]
  have hstar : star (r⁻¹) = r⁻¹ := by
    simpa only [star_inv₀, Complex.star_def] using
      congrArg (fun z : ℂ => z⁻¹) (Complex.conj_ofReal (sectionNorm s))
  rw [hstar, show H s = r ^ 2 from (sectionNorm_sq s).symm]
  calc
    _ = (r⁻¹ * (r⁻¹ * r ^ 2)) • (1 : PeriodicMPSParentIntersection.Bond) := by
      simp only [smul_smul, mul_assoc]
    _ = 1 := by
      rw [show r⁻¹ * (r⁻¹ * r ^ 2) = 1 by field_simp [hr] <;> ring, one_smul]

/-- Exact raw two-site covariance under the physical frame after restoring
the first trace. The scalar enters with the ket and bra seventh powers. -/
theorem rawTwo_sectionMatrix (A : Core) (s l : ℂ) (hl : Complex.normSq l = 1) :
    let U := (sectionUnitary s l hl).val
    let r : ℂ := sectionNorm s
    PeriodicMPSTwoSiteAmbiguity.rawTwo (changePhysical (sectionMatrix s l) A) 3 =
      (r ^ 7 * star (r ^ 7)) •
        (pairBasis U * PeriodicMPSTwoSiteAmbiguity.rawTwo A 3 * (pairBasis U)ᴴ) := by
  dsimp only
  let r := (sectionNorm s : ℂ)
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.2 (sectionNorm_pos s).ne'
  let U := sectionUnitary s l hl
  have hM : sectionMatrix s l = r • U.val := by
    change sectionMatrix s l = r • (r⁻¹ • sectionMatrix s l)
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
  have he : changePhysical (sectionMatrix s l) A = r • changePhysical U.val A := by
    rw [hM]
    funext i
    simp only [changePhysical, Pi.smul_apply, Matrix.smul_apply, Finset.smul_sum,
      smul_eq_mul, mul_smul]
  rw [he, rawTwo_scaled r (changePhysical U.val A) 3, changePhysical_unitary_raw U A 3]

/-- The literal seven-site ordinary amplitude, in the same affine trace
coordinate order as the hard-core pencil decoder. -/
def ordinaryAmplitude (p : Ordinary) : SevenSiteTraceBase.Amp :=
  amplitude ![1, p.1, p.2.1, p.2.2.1, p.2.2.2]

def ordinaryRaw (p : Ordinary) : TwoQubitMarginalReflection.Density :=
  pairGram (m := 5) (ordinaryAmplitude p)

def ordinaryMass (p : Ordinary) : ℝ := (ordinaryRaw p).trace.re

/-- The literal adjacent marginal on the ordinary parameter domain. -/
def ordinaryMarginal (p : Ordinary) : TwoQubitMarginalReflection.Density :=
  twoSiteObservation 5 (projector (ordinaryAmplitude p))

theorem exists_core_ordinary (p : Ordinary) :
    ∃ A : Core, (A 0).trace = 1 ∧ (A 1).trace = p.1 ∧
      ordinaryAmplitude p = UniformMPSExpectedDimensionRefutation.traceWord 2 2 7 A := by
  obtain ⟨A, ht, hs, hd, he, hk⟩ := exists_trace_coordinates 1 p.1 p.2.1 p.2.2.1 p.2.2.2
  refine ⟨A, ht, hs, ?_⟩
  simpa only [ht, hs, hd, he, hk, ordinaryAmplitude] using SevenSiteTraceBase.amplitude_actual A

theorem ordinaryMarginal_mem (p : Ordinary) (hp : ordinaryAmplitude p ≠ 0) :
    ordinaryMarginal p ∈ normalizedExchangeMarginals := by
  obtain ⟨A, _, _, hA⟩ := exists_core_ordinary p
  have hAne : UniformMPSExpectedDimensionRefutation.traceWord 2 2 7 A ≠ 0 := by
    simpa only [← hA] using hp
  have h := normalizedMarginal_mem (m := 5) A hAne
  rw [← twoSiteObservation_traceWord (m := 5) A] at h
  simpa only [ordinaryMarginal, hA] using h

theorem ordinaryMass_pos (p : Ordinary) (hp : ordinaryAmplitude p ≠ 0) :
    0 < ordinaryMass p := by
  rw [ordinaryMass, ordinaryRaw, ← mass_eq_trace]
  exact mass_pos _ hp

theorem ordinaryMarginal_eq_normalizedRaw (p : Ordinary) :
    ordinaryMarginal p = (ordinaryMass p)⁻¹ • ordinaryRaw p := by
  have hmass : mass (ordinaryAmplitude p) = ordinaryMass p := by
    unfold ordinaryMass ordinaryRaw
    exact mass_eq_trace (m := 5) (ordinaryAmplitude p)
  rw [ordinaryMarginal,
    PeriodicMPSUniformHardCoreLocalization.twoSiteObservation_projector (m := 5)
      (ordinaryAmplitude p), hmass, ordinaryRaw]

private theorem differentiable_ordinaryAmplitude :
    Differentiable ℝ ordinaryAmplitude := by
  apply differentiable_amplitude.comp
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · change Differentiable ℝ (fun _ : Ordinary => (1 : ℂ))
    exact differentiable_const (1 : ℂ)
  · change Differentiable ℝ (fun p : Ordinary => p.1)
    fun_prop
  · change Differentiable ℝ (fun p : Ordinary => p.2.1)
    fun_prop
  · change Differentiable ℝ (fun p : Ordinary => p.2.2.1)
    fun_prop
  · change Differentiable ℝ (fun p : Ordinary => p.2.2.2)
    fun_prop

private theorem differentiable_ordinaryRaw : Differentiable ℝ ordinaryRaw := by
  have hA := differentiable_ordinaryAmplitude
  change Differentiable ℝ (fun p => pairGram (m := 5) (ordinaryAmplitude p))
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  unfold pairGram
  simp only [Complex.star_def, ← Complex.conjCLE_apply]
  fun_prop

private theorem differentiable_ordinaryMass : Differentiable ℝ ordinaryMass := by
  have hR := differentiable_ordinaryRaw
  unfold ordinaryMass Matrix.trace Matrix.diag
  change Differentiable ℝ (fun p => Complex.reCLM (∑ i, ordinaryRaw p i i))
  fun_prop

/-- The literal normalized marginal is differentiable wherever its amplitude
is nonzero. -/
theorem differentiableAt_ordinaryMarginal (p : Ordinary) (hp : ordinaryAmplitude p ≠ 0) :
    DifferentiableAt ℝ ordinaryMarginal p := by
  have he : ordinaryMarginal = fun q => (ordinaryMass q)⁻¹ • ordinaryRaw q :=
    funext ordinaryMarginal_eq_normalizedRaw
  rw [he]
  exact ((differentiable_ordinaryMass p).inv (ordinaryMass_pos p hp).ne').smul
    (differentiable_ordinaryRaw p)

private theorem fderiv_constraint {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p : Ordinary} (hp : ordinaryAmplitude p ≠ 0)
    (L : TwoQubitMarginalReflection.Density →L[ℝ] Y) (c : Y)
    (h : ∀ M ∈ normalizedExchangeMarginals, L M = c) (u : Ordinary) :
    L (fderiv ℝ ordinaryMarginal p u) = 0 := by
  have he : L ∘ ordinaryMarginal =ᶠ[𝓝 p] (fun _ => c) :=
    (differentiable_ordinaryAmplitude.continuous.continuousAt.eventually_ne hp).mono
      fun q hq => h _ (ordinaryMarginal_mem q hq)
  have hd : fderiv ℝ (L ∘ ordinaryMarginal) p =
      L.comp (fderiv ℝ ordinaryMarginal p) :=
    (L.hasFDerivAt.comp p (differentiableAt_ordinaryMarginal p hp).hasFDerivAt).fderiv
  rw [he.fderiv_eq, fderiv_const_apply] at hd
  simpa only [ContinuousLinearMap.comp_apply, _root_.zero_apply] using
    (congrArg (fun T : Ordinary →L[ℝ] Y => T u) hd).symm

/-- The nine Pauli readings detect injectivity of the differential of the
literal marginal on the eight-dimensional ordinary source. -/
theorem ordinaryMarginal_injective_iff_readout (p : Ordinary) (hp : ordinaryAmplitude p ≠ 0) :
    Injective (fderiv ℝ ordinaryMarginal p) ↔
      Injective (fderiv ℝ (readout ∘ ordinaryMarginal) p) := by
  let D := fderiv ℝ ordinaryMarginal p
  let entry (i j : TwoQubitMarginalReflection.Bits) :
      TwoQubitMarginalReflection.Density →L[ℝ] ℂ :=
    let row : TwoQubitMarginalReflection.Density →L[ℝ]
        (TwoQubitMarginalReflection.Bits → ℂ) := ContinuousLinearMap.proj i
    let col : (TwoQubitMarginalReflection.Bits → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj j
    col.comp row
  have hD : fderiv ℝ (readout ∘ ordinaryMarginal) p = readout.comp D :=
    (readout.hasFDerivAt.comp p (differentiableAt_ordinaryMarginal p hp).hasFDerivAt).fderiv
  rw [hD]
  constructor
  · intro h
    have constraints (u : Ordinary) (hu : readout (D u) = 0) : D u = 0 := by
      have hHerm : (D u).IsHermitian := by
        change (D u)ᴴ = D u
        ext i j
        let L := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (entry j i) - entry i j
        have he := fderiv_constraint hp L 0
          (fun M hM => sub_eq_zero.mpr (congrArg (fun N : TwoQubitMarginalReflection.Density =>
            N i j) hM.1.eq)) u
        exact sub_eq_zero.mp he
      have hSwap : TwoQubitMarginalReflection.ExchangeSymmetric (D u) := by
        intro i j
        let L := entry i.swap j.swap - entry i j
        exact sub_eq_zero.mp (fderiv_constraint hp L 0
          (fun M hM => sub_eq_zero.mpr (hM.2.1 i j)) u)
      let T : TwoQubitMarginalReflection.Density →L[ℝ] ℂ :=
        ∑ i : TwoQubitMarginalReflection.Bits, entry i i
      have htrace : (D u).trace = 0 := by
        have hT (M : TwoQubitMarginalReflection.Density) : T M = M.trace := by
          simp only [T, Matrix.trace, Matrix.diag, _root_.sum_apply]
          exact Finset.sum_congr rfl fun _ _ => rfl
        simpa only [D, hT] using fderiv_constraint hp T 1
          (fun M hM => (hT M).trans hM.2.2) u
      exact eq_of_readout_of_trace_eq hHerm (by simp)
        hSwap (by intro i j; simp) (by simp [htrace]) (by simpa using hu)
    intro a b hab
    apply h
    have hzero : readout (D (a - b)) = 0 := by
      simpa only [ContinuousLinearMap.comp_apply, map_sub, sub_eq_zero] using hab
    exact sub_eq_zero.mp (by simpa only [map_sub] using constraints (a-b) hzero)
  · intro h a b hab
    exact h (congrArg readout hab)

/-- Projectivization of the literal eight-dimensional ordinary experiment
adds precisely the radial column to the raw Pauli differential. -/
theorem ordinaryReadout_injective_iff_augmented (p : Ordinary) (hp : ordinaryAmplitude p ≠ 0) :
    Injective (fderiv ℝ (readout ∘ ordinaryMarginal) p) ↔
      Injective (fun w : Ordinary × ℝ =>
        (fderiv ℝ ordinaryMass p w.1 + w.2 * ordinaryMass p,
          fderiv ℝ (readout ∘ ordinaryRaw) p w.1 + w.2 • readout (ordinaryRaw p))) := by
  have hvalue : readout ∘ ordinaryMarginal =
      fun q => (ordinaryMass q)⁻¹ • (readout ∘ ordinaryRaw) q := by
    funext q
    exact (congrArg readout (ordinaryMarginal_eq_normalizedRaw q)).trans (map_smul readout _ _)
  rw [hvalue]
  exact injective_fderiv_normalized_iff ordinaryMass (readout ∘ ordinaryRaw) p
    (differentiable_ordinaryMass p) (readout.differentiable.comp differentiable_ordinaryRaw p)
    (ordinaryMass_pos p hp).ne'

/-- The derivative of the literal marginal has full source rank precisely
when the unnormalized ordinary readout augmented by its value is injective. -/
theorem ordinaryMarginal_injective_iff_augmented (p : Ordinary)
    (hp : ordinaryAmplitude p ≠ 0) :
    Injective (fderiv ℝ ordinaryMarginal p) ↔
      Injective (fun w : Ordinary × ℝ =>
        (fderiv ℝ ordinaryMass p w.1 + w.2 * ordinaryMass p,
          fderiv ℝ (readout ∘ ordinaryRaw) p w.1 + w.2 • readout (ordinaryRaw p))) :=
  (ordinaryMarginal_injective_iff_readout p hp).trans
    (ordinaryReadout_injective_iff_augmented p hp)

/-- The embedded positive-slice variables, before adding physical rotations. -/
def sliceOrdinary (x : SlicePoint) : Ordinary := physicalChart 1 (0, x)

/-- The raw marginal computed from the ordinary coordinate polynomial
agrees with the literal raw marginal of any core presentation. -/
theorem ordinaryRaw_actual (A : Core) (hA : (A 0).trace = 1) :
    ordinaryRaw ((A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace) =
      PeriodicMPSTwoSiteAmbiguity.rawTwo A 3 := by
  have h := SevenSiteTraceBase.amplitude_actual A
  rw [hA] at h
  unfold ordinaryRaw
  change pairGram (m := 5)
    (amplitude ![1, (A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace]) = _
  simpa only [← h] using PeriodicMPSUniformHardCoreMarginalWitness.pairGram_traceWord A 3

/-- The covariance identity in the eight ordinary chart variables. -/
theorem ordinaryRaw_physicalChart (centerPhase : ℂ) (hPhase : Complex.normSq centerPhase = 1)
    (v : Rotation × SlicePoint) :
    let s := (Complex.ofRealCLM v.1.2.1 - Complex.I * Complex.ofRealCLM v.1.1) / 2
    let l := centerPhase * phase v.1.2.2
    let hl : Complex.normSq l = 1 := by
      change Complex.normSq (centerPhase * phase v.1.2.2) = 1
      rw [Complex.normSq_mul, hPhase, phase_normSq, one_mul]
    let U := (sectionUnitary s l hl).val
    let r : ℂ := sectionNorm s
    ordinaryRaw (physicalChart centerPhase v) =
      (r ^ 7 * star (r ^ 7)) •
        (pairBasis U * ordinaryRaw (sliceOrdinary v.2) * (pairBasis U)ᴴ) := by
  dsimp only
  let x := v.2
  let d := (x 0 : ℂ) + Complex.I * (x 3 : ℂ)
  let e := (x 2 : ℂ) + Complex.I * (x 4 : ℂ)
  let s := (Complex.ofRealCLM v.1.2.1 - Complex.I * Complex.ofRealCLM v.1.1) / 2
  let l := centerPhase * phase v.1.2.2
  obtain ⟨A, ht, hs, hd, he, hk⟩ := exists_trace_coordinates 1 0 d e (x 1)
  let B := changePhysical (sectionMatrix s l) A
  have hB := sectionMatrix_invariants A ht hs s l
  have hBt : (B 0).trace = 1 := hB.1
  have hBp : ((B 1).trace, (B 0).det, (B 1).det, (B 0 * B 1).trace) =
      physicalChart centerPhase v := by
    change _ = unalign (s, d, l ^ 2 * e, l * (x 1 : ℂ))
    rw [← hd, ← he, ← hk]
    exact hB.2
  have hAp : ((A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace) =
      sliceOrdinary x := by
    rw [sliceOrdinary, physicalChart_center, hs, hd, he, hk]
  have hRawB := (congrArg ordinaryRaw hBp.symm).trans (ordinaryRaw_actual B hBt)
  have hRawA : ordinaryRaw (sliceOrdinary v.2) = PeriodicMPSTwoSiteAmbiguity.rawTwo A 3 :=
    (congrArg ordinaryRaw hAp.symm).trans (ordinaryRaw_actual A ht)
  rw [hRawB, hRawA]
  have hl : Complex.normSq l = 1 := by
    change Complex.normSq (centerPhase * phase v.1.2.2) = 1
    rw [Complex.normSq_mul, hPhase, phase_normSq, one_mul]
  exact rawTwo_sectionMatrix A s l hl

/-- The literal chart derivative at a positive slice can be computed after
pullback through the three physical and five slice directions. -/
theorem ordinaryReadout_injective_iff_physicalChart (x : SlicePoint)
    (hx : 0 < x 1) (hA : ordinaryAmplitude (sliceOrdinary x) ≠ 0) :
    Injective (fderiv ℝ (readout ∘ ordinaryMarginal) (sliceOrdinary x)) ↔
      Injective (fderiv ℝ ((readout ∘ ordinaryMarginal) ∘ physicalChart 1) (0, x)) := by
  let v : Rotation × SlicePoint := (0, x)
  have hF : DifferentiableAt ℝ (physicalChart 1) v :=
    (analyticAt_physicalChart 1 v).differentiableAt
  have hG : DifferentiableAt ℝ (readout ∘ ordinaryMarginal) (physicalChart 1 v) :=
    readout.differentiableAt.comp _ (differentiableAt_ordinaryMarginal _ hA)
  change Injective (fderiv ℝ (readout ∘ ordinaryMarginal) (physicalChart 1 v)) ↔
    Injective (fderiv ℝ ((readout ∘ ordinaryMarginal) ∘ physicalChart 1) v)
  rw [fderiv_comp v hG hF]
  let F := fderiv ℝ (physicalChart 1) v
  let G := fderiv ℝ (readout ∘ ordinaryMarginal) (physicalChart 1 v)
  change Injective G ↔ Injective (G ∘ F)
  have hb : Bijective F := bijective_fderiv_physicalChart_center x hx
  exact (Injective.of_comp_iff' (⇑G) hb).symm

def rawRows (p : Ordinary) : Fin 10 → ℝ :=
  Fin.cons (ordinaryMass p) (readout (ordinaryRaw p))

/-- All ten raw rows at zero rotation are the real evaluations of the
certificate polynomials in their prescribed order. -/
theorem rawRows_slice_eq_eval (x : SlicePoint) (i : Fin 10) :
    rawRows (sliceOrdinary x) i =
      (eval (fun j => (x j : ℂ)) (V Complex.I (observedRow i))).re := by
  let d := (x 0 : ℂ) + Complex.I * (x 3 : ℂ)
  let e := (x 2 : ℂ) + Complex.I * (x 4 : ℂ)
  obtain ⟨A, ht, hs, hd, he, hk⟩ := exists_trace_coordinates 1 0 d e (x 1)
  have hRaw : ordinaryRaw (sliceOrdinary x) = PeriodicMPSTwoSiteAmbiguity.rawTwo A 3 := by
    have hA : ((A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace) = sliceOrdinary x := by
      rw [sliceOrdinary, physicalChart_center, hs, hd, he, hk]
    rw [← hA, ordinaryRaw_actual A ht]
  have hPlus : sliceBlock Complex.I (fun j => (x j : ℂ)) true = alignedInvariants A := by
    simp [sliceBlock, alignedInvariants, hd, he, hk, d, e]
  have hMinus : sliceBlock Complex.I (fun j => (x j : ℂ)) false =
      star ∘ alignedInvariants A := by
    funext j
    fin_cases j <;> simp [sliceBlock, alignedInvariants, hd, he, hk, d, e]
  rw [SevenSiteCriticalCertificate.eval_value, SevenSiteCriticalCertificate.slicedObservation,
    hPlus, hMinus]
  simpa only [rawRows, ordinaryMass, hRaw] using
    (congrFun (observedRows_eq_rawReadout A ht hs) i).symm

private theorem hasDerivAt_eval_slice_line (p : MvPolynomial (Fin 5) ℂ)
    (x : SlicePoint) (j : Fin 5) :
    HasDerivAt (fun t : ℝ => eval (fun i => (↑((x + t • (Pi.single j 1 : SlicePoint)) i) : ℂ)) p)
      (eval (fun i => (x i : ℂ)) (pderiv j p)) 0 := by
  let u : SlicePoint := Pi.single j 1
  let e (t : ℝ) : MvPolynomial (Fin 5) ℂ →+* ℂ :=
    eval (fun i => (↑((x + t • u) i) : ℂ))
  let e₀ : MvPolynomial (Fin 5) ℂ →+* ℂ := eval (fun i => (x i : ℂ))
  change HasDerivAt (fun t : ℝ => e t p) (e₀ (pderiv j p)) 0
  have hzero (q : MvPolynomial (Fin 5) ℂ) : e 0 q = e₀ q := by
    simp only [e, e₀, zero_smul, add_zero]
  have hcoord (i : Fin 5) :
      HasDerivAt (fun t : ℝ => e t (X i)) (e₀ (pderiv j (X i))) 0 := by
    have h := (hasDerivAt_const (0 : ℝ) (x i)).fun_add
      (hasDerivAt_mul_const (x := (0 : ℝ)) (u i))
    have hi : HasDerivAt (fun t : ℝ => (↑((x + t • u) i) : ℂ)) (↑(u i) : ℂ) 0 := by
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add] using h.ofReal_comp
    have he : (↑(u i) : ℂ) = e₀ (pderiv j (X i)) := by
      by_cases hij : i = j
      · subst i
        simp [u, e₀, pderiv_X_self]
      · simp [u, e₀, Pi.single_eq_of_ne hij, pderiv_X_of_ne hij]
    simpa only [e, eval_X, he] using hi
  induction p using MvPolynomial.induction_on with
  | C c =>
    simpa only [e, eval_C, pderiv_C, map_zero] using hasDerivAt_const (0 : ℝ) c
  | add p q hp hq =>
    simpa only [map_add] using hp.fun_add hq
  | mul_X p i hp =>
    simpa only [pderiv_mul, map_add, map_mul, hzero] using hp.fun_mul (hcoord i)

/-- The five actual slice directional derivatives give the five partial
columns of the certified augmented matrix. -/
theorem hasDerivAt_rawRows_slice (x : SlicePoint) (i : Fin 10) (j : Fin 5) :
    HasDerivAt (fun t : ℝ => rawRows (sliceOrdinary (x + t • Pi.single j 1)) i)
      (eval (fun k => (x k : ℂ)) (pderiv j (V Complex.I (observedRow i)))).re 0 := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_eval_slice_line (V Complex.I (observedRow i)) x j)
  simpa only [Function.comp_def, Complex.reCLM_apply, rawRows_slice_eq_eval] using h

/-- The action on a Pauli test matrix uses the adjoint on the left.
This fixes the signs of all three rotation columns against the certificate. -/
theorem pauli_commutator_eq_rotationIndex (j : Fin 3) (a : Fin 4) :
    (Complex.I / 2) • (pauliFrame j.succ * pauliFrame a -
        pauliFrame a * pauliFrame j.succ) =
      ((rotationIndex j a).1 : ℂ) • pauliFrame (rotationIndex j a).2 := by
  have hframe : pauliFrame = ![(1 : PeriodicMPSParentIntersection.Bond),
      !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]] := by
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    rw [Matrix.cons_val_succ]
    exact pauli_explicit i
  rw [hframe]
  fin_cases j <;> fin_cases a <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    norm_num [rotationIndex, Fin.succ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_succ',
      Matrix.cons_val_zero', Matrix.cons_val', Matrix.of_apply, Complex.I_mul_I] <;>
    ring_nf <;> simp [Complex.I_sq]

/-- The infinitesimal adjoint action differentiates the two test observables
in their original tensor-factor order. -/
theorem pauli_pair_rotation_column (ρ : TwoQubitMarginalReflection.Density)
    (j : Fin 3) (a b : Fin 4) :
    let δ := fun m : Fin 4 => (Complex.I / 2) •
      (pauliFrame j.succ * pauliFrame m - pauliFrame m * pauliFrame j.succ)
    (((δ a ⊗ₖ pauliFrame b) + (pauliFrame a ⊗ₖ δ b)) * ρ).trace.re =
      ((rotationIndex j a).1 : ℝ) *
        (((pauliFrame (rotationIndex j a).2) ⊗ₖ pauliFrame b) * ρ).trace.re +
      ((rotationIndex j b).1 : ℝ) *
        ((pauliFrame a ⊗ₖ (pauliFrame (rotationIndex j b).2)) * ρ).trace.re := by
  dsimp only
  rw [pauli_commutator_eq_rotationIndex, pauli_commutator_eq_rotationIndex,
    smul_kronecker, kronecker_smul, add_mul, smul_mul_assoc, smul_mul_assoc,
    trace_add, trace_smul, trace_smul]
  simp [Complex.add_re, smul_eq_mul, Complex.mul_re]

/-- The vanishing set to which the checked slice cover applies. -/
def certifiedCriticalSlice : Set SlicePoint :=
  {x | x 1 ≠ 0 ∧ ∀ i : Fin 10,
    eval (fun j => (x j : ℂ)) (criticalMatrix Complex.I i).det = 0}

/-- Lifting the certified critical slice through both phase charts gives a
countable differentiable cover from six real variables. -/
theorem cover_physicalChart_criticalSlice :
    ∃ (ι : Type) (_ : Countable ι)
      (D : ι → Set (Rotation × (Fin 3 → ℝ)))
      (f : ι → Rotation × (Fin 3 → ℝ) → Ordinary),
      (∀ i, DifferentiableOn ℝ (f i) (D i)) ∧
        ((fun q : Bool × (Rotation × SlicePoint) =>
          physicalChart (if q.1 then 1 else -1) q.2) ''
          {q | q.2.2 ∈ certifiedCriticalSlice}) ⊆ ⋃ i, f i '' D i := by
  obtain ⟨ι, hι, D, g, hg, hcov⟩ := seven_site_critical_slice_cover
  letI : Countable ι := hι
  let E := Rotation × (Fin 3 → ℝ)
  let W (j : Bool × ι) : Set E := {q | q.2 ∈ D j.2}
  let f (j : Bool × ι) (q : E) : Ordinary :=
    physicalChart (if j.1 then 1 else -1) (q.1, g j.2 q.2)
  refine ⟨Bool × ι, inferInstance, W, f, ?_, ?_⟩
  · intro j
    have hg' : DifferentiableOn ℝ (fun q : E => g j.2 q.2) (W j) :=
      (hg j.2).comp differentiable_snd.differentiableOn (fun _ h => h)
    have hChart : Differentiable ℝ (physicalChart (if j.1 then 1 else -1)) :=
      fun v => (analyticAt_physicalChart _ v).differentiableAt
    exact hChart.comp_differentiableOn (differentiable_fst.differentiableOn.prodMk hg')
  · rintro _ ⟨⟨b, r, x⟩, hx, rfl⟩
    obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨(b, i), (r, u), hu, rfl⟩

#print axioms image_zeroMixed
#print axioms bijective_fderiv_physicalChart_center
#print axioms hasDerivAt_rawRows_slice
#print axioms ordinaryMarginal_injective_iff_augmented
#print axioms rawTwo_sectionMatrix
#print axioms ordinaryRaw_physicalChart
#print axioms hasDerivAt_centeredFrame
#print axioms pauli_pair_rotation_column
#print axioms cover_physicalChart_criticalSlice

end

end D5.S3.Quantum.TensorNetworks.SevenSitePhysicalRankBridge
