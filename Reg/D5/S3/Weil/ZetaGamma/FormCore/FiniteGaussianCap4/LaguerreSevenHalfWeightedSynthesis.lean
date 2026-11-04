import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis
import Reg.Support.SingleDependentReadout

/-! Dependent-family audit of the actual simultaneous synthesis estimate. -/

open FiniteGaussianCap4.LaguerreSevenHalf
open FiniteGaussianCap4.LaguerreSevenHalf.WeightedSynthesis
open MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis

private def basis : ℕ →₀ ℝ := Finsupp.single 0 1

private theorem basis_feature (x : ℝ) : finiteFeature basis x = centralPsi x 0 := by
  have h : finitePolynomial basis = psiPolynomial 0 := by
    simp [basis, finitePolynomial, finiteCoefficients, coefficientWeight]
  simpa only [finiteFeature, h] using physicalPolynomial_psi 0 x

private theorem basis_memLp : MemLp (finiteFeature basis) 1 mellinMeasure := by
  rw [memLp_one_iff_integrable]
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (5 / 4 : ℝ))) := by fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  apply (integrable_centralPsi 0).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le _), smul_eq_mul, basis_feature]

private theorem basis_nonzero : finiteSynthesis basis ≠ 0 := by
  intro hz
  have ht : ((finiteSynthesis basis).2 : ℝ → ℝ) =ᵐ[mellinMeasure] finiteFeature basis :=
    MemLp.coeFn_toLp basis_memLp
  have he : finiteFeature basis =ᵐ[mellinMeasure] 0 := by
    apply ht.symm.trans
    rw [hz]
    exact Lp.coeFn_zero ℝ 1 mellinMeasure
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (5 / 4 : ℝ))) := by fun_prop
  have he' := (ae_withDensity_iff hm).mp he
  have hi : normalizedCentralMellin 0 = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [he', ae_restrict_mem measurableSet_Ioi] with x hzero hx
    have hp : ENNReal.ofReal (x ^ (5 / 4 : ℝ)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hx _))
    rw [← basis_feature x, hzero hp]
    simp
  exact (ne_of_gt (normalizedCentralMellin_even_pos 0)) (by simpa using hi)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Coeff) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ w => ‖w‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ w : Coeff, ‖synthesis w‖ ≤ synthesisBound * R.readout () () w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  change ‖synthesis 0‖ ≤ synthesisBound * (-1) at hh
  rw [map_zero, norm_zero] at hh
  have hp : (0 : ℝ) < synthesisBound :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 649) (le_max_left _ _)
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, lp.single 2 0 (1 : ℝ), ?_⟩
  change ‖(0 : Coeff)‖ ≠ ‖(lp.single 2 0 (1 : ℝ) : Coeff)‖
  rw [norm_zero, lp.norm_single (by norm_num)]
  norm_num

def family : Registration arena (type_of% synthesis_norm_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨synthesis_norm_le, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    synthesis_norm_le (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis.norm_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => ‖w‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Finite

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ →₀ ℝ) (fun _ => PhysicalSpace)

def actual : Realization signature :=
  realize signature (fun _ _ v => synthesis (includeFinite v)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => finiteSynthesis basis) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ v : ℕ →₀ ℝ, R.readout () () v = finiteSynthesis v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  change finiteSynthesis basis = finiteSynthesis 0 at hh
  rw [map_zero] at hh
  exact basis_nonzero hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, basis, ?_⟩
  change synthesis (includeFinite 0) ≠ synthesis (includeFinite basis)
  rw [synthesis_finite, synthesis_finite, map_zero]
  exact Ne.symm basis_nonzero

def family : Registration arena (type_of% synthesis_finite) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨synthesis_finite, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    synthesis_finite (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis.finite_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis.Finite.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ v => synthesis (includeFinite v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Finite

namespace Series

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Coeff) (fun _ => PhysicalSpace)

def actual : Realization signature :=
  realize signature (fun _ _ w => synthesis w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => finiteSynthesis basis) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ w : Coeff,
    HasSum (fun k => finiteSynthesis (Finsupp.single k (w k))) (R.readout () () w)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : HasSum (fun _ : ℕ => (0 : PhysicalSpace)) (finiteSynthesis basis) := by
    simpa [rejected, realize] using h 0
  exact basis_nonzero (hh.unique hasSum_zero)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, includeFinite basis, ?_⟩
  change synthesis 0 ≠ synthesis (includeFinite basis)
  rw [synthesis_finite, map_zero]
  exact Ne.symm basis_nonzero

def family : Registration arena (type_of% synthesis_hasSum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨synthesis_hasSum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    synthesis_hasSum (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis.series_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis.Series.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => synthesis w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Series

end Reg.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis
