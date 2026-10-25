import CFMPFourCyclePhysicalMinimum263Transient
import Mathlib.Analysis.Calculus.FDeriv.Congr

noncomputable section
universe u264 v264
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff Matrix
open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPGlobalGenuineCovolume256Transient
open CFMPActualGlobalEnergy259Transient
open CFMPActualGlobalHessian260Transient

namespace CFMPActualEnergySecond264Transient

variable {T : Type u264} {E : Type v264}
  [Fintype T] [Fintype E] [DecidableEq E]

def pairing : (E → ℝ) →L[ℝ] ((E → ℝ) →L[ℝ] ℝ) :=
  ∑ e : E, (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)

theorem pairing_coefficients (u : E → ℝ) :
    pairing u = ∑ e : E, u e • (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ) := by
  simp [pairing]

theorem pairing_apply (u v : E → ℝ) : pairing u v = ∑ e : E, u e * v e := by
  simp [pairing_coefficients]

theorem globalGenuine_open (s : Incidence T E) : IsOpen (globalGenuine s) := by
  have heq : globalGenuine s =
      ⋂ t : T, (localRead s t) ⁻¹' {a : Lengths | CFMPGenuineLengthNeighborhood435Transient.genuine a} := by
    ext p
    simp [globalGenuine]
  rw [heq]
  exact isOpen_iInter_of_finite (fun t =>
    CFMPGenuineLengthNeighborhood435Transient.genuine_open.preimage (localRead s t).continuous)

theorem actual_energy_gradient_eventually
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (p : E → ℝ) (hp : p ∈ globalGenuine s) :
    fderiv ℝ (physicalEnergy s G) =ᶠ[𝓝 p]
      (fun q : E → ℝ => pairing (-physicalCurvature s q)) := by
  filter_upwards [(globalGenuine_open s).mem_nhds hp] with q hq
  simpa only [pairing_coefficients,Pi.neg_apply] using
    (physicalEnergy_hasFDerivAt s G hG q hq).fderiv

theorem actual_energy_gradient_hasFDerivAt
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (p : E → ℝ) (hp : p ∈ globalGenuine s) :
    HasFDerivAt (fderiv ℝ (physicalEnergy s G))
      ((pairing : (E → ℝ) →L[ℝ] ((E → ℝ) →L[ℝ] ℝ)).comp
        (-curvatureDifferential s p)) p := by
  have hd : HasFDerivAt (fun q : E → ℝ => pairing (-physicalCurvature s q))
      ((pairing : (E → ℝ) →L[ℝ] ((E → ℝ) →L[ℝ] ℝ)).comp
        (-curvatureDifferential s p)) p := by
    convert! ((pairing : (E → ℝ) →L[ℝ] ((E → ℝ) →L[ℝ] ℝ)).hasFDerivAt.comp p
      (physicalCurvature_hasFDerivAt s p hp).neg) using 1 <;> rfl
  exact hd.congr_of_eventuallyEq (actual_energy_gradient_eventually s G hG p hp)

theorem actual_energy_second_eq_negative_curvature
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (p : E → ℝ) (hp : p ∈ globalGenuine s) (v w : E → ℝ) :
    fderiv ℝ (fderiv ℝ (physicalEnergy s G)) p w v =
      -(∑ e : E, v e * (fderiv ℝ (physicalCurvature s) p w) e) := by
  rw [(actual_energy_gradient_hasFDerivAt s G hG p hp).fderiv,
    (physicalCurvature_hasFDerivAt s p hp).fderiv]
  change pairing (-(curvatureDifferential s p w)) v = _
  rw [pairing_apply]
  simp only [Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact mul_comm _ _

theorem actual_energy_second_local_pullback
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (p : E → ℝ) (hp : p ∈ globalGenuine s) (v w : E → ℝ) :
    fderiv ℝ (fderiv ℝ (physicalEnergy s G)) p w v =
      ∑ t : T, ∑ e : Fin 6, ∑ f : Fin 6,
        localRead s t v e * CFMPActualPhysicalHessian258Transient.physicalHessian G
          (localRead s t p) e f * localRead s t w f := by
  rw [actual_energy_second_eq_negative_curvature s G hG p hp v w]
  exact negative_curvature_bilinear_actual_pullback s G hG p hp v w

def actualGlobalHessian (s : Incidence T E) (G : RealizationFamily) (p : E → ℝ) :
    Matrix E E ℝ := fun e f =>
  fderiv ℝ (fderiv ℝ (physicalEnergy s G)) p (Pi.single f 1) (Pi.single e 1)

theorem actualGlobalHessian_eq_negative_curvature_matrix
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (p : E → ℝ) (hp : p ∈ globalGenuine s) :
    actualGlobalHessian s G p = fun e f : E =>
      -(fderiv ℝ (physicalCurvature s) p (Pi.single f 1)) e := by
  ext e f
  simpa only [actualGlobalHessian,Pi.single_apply,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] using
    actual_energy_second_eq_negative_curvature s G hG p hp (Pi.single e 1) (Pi.single f 1)

end CFMPActualEnergySecond264Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualEnergySecond264Transient.actual_energy_gradient_hasFDerivAt,
      ``CFMPActualEnergySecond264Transient.actual_energy_second_eq_negative_curvature,
      ``CFMPActualEnergySecond264Transient.actual_energy_second_local_pullback,
      ``CFMPActualEnergySecond264Transient.actualGlobalHessian_eq_negative_curvature_matrix] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP264 actual global physical Hessian theorem absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP264 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP264 CHECKED {name} axioms={axioms}"
