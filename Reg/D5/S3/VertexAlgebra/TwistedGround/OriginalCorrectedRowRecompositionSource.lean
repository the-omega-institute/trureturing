import D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource
import LeanInformationAuditInterface.Contract.Registration

/-! Exact source-type mirrors preserve the original theorem telescopes. A mirror
is compiled audit evidence, not a four-slot registration or a binding verdict. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource

abbrev sourceScope_Corr_residual_support := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.Corr_residual_support)
theorem source_actual_Corr_residual_support : sourceScope_Corr_residual_support :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.Corr_residual_support

abbrev sourceScope_sourceCovariance_symm := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.sourceCovariance_symm.{u})
theorem source_actual_sourceCovariance_symm : sourceScope_sourceCovariance_symm.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.sourceCovariance_symm.{u}

abbrev sourceScope_charged_correction_coefficients := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.charged_correction_coefficients.{u})
theorem source_actual_charged_correction_coefficients : sourceScope_charged_correction_coefficients.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.charged_correction_coefficients.{u}

abbrev sourceScope_charged_correction_shift_coefficient := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.charged_correction_shift_coefficient.{u})
theorem source_actual_charged_correction_shift_coefficient : sourceScope_charged_correction_shift_coefficient.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.charged_correction_shift_coefficient.{u}

abbrev sourceScope_affineLaurent_apply := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.affineLaurent_apply.{u})
theorem source_actual_affineLaurent_apply : sourceScope_affineLaurent_apply.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.affineLaurent_apply.{u}

abbrev sourceScope_original_corrected_row_finite_reduction := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.original_corrected_row_finite_reduction)
theorem source_actual_original_corrected_row_finite_reduction : sourceScope_original_corrected_row_finite_reduction :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.original_corrected_row_finite_reduction


open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients
open TwistedGround OriginalFourMChargeCoset OriginalNormalRowSource
open OriginalCorrectedRowRecompositionSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace FiniteReduction
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource

def arena : Arena where
  signature := CorrectedRow.signature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (alpha beta gamma : Index D →₀ ℕ) (e : ℤ),
    R.readout () ⟨D, hu, a, alpha, beta, gamma⟩ e =
      let K := rowSupport D alpha beta gamma
      let label := supportLabel D K
      let d := restricted D K alpha
      let h := restricted D K beta
      let l := restricted D K gamma
      (FactorialFockMetric.weight beta : ℂ) * (FactorialFockMetric.weight gamma : ℂ) *
        (if e+chargeNorm D a = Finsupp.weight (normalWeight D label) (threeOccupation d h l)
          then recompositionAmplitude D a label d h l else 0)

theorem source_bridge : sourceScope_original_corrected_row_finite_reduction ↔ arena.Law CorrectedRow.actual :=
  Iff.rfl

theorem positive : arena.Law CorrectedRow.actual :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.original_corrected_row_finite_reduction

theorem negative : ¬ arena.Law CorrectedRow.rejected := by
  intro h
  have bad := h CorrectedRow.emptyLattice CorrectedRow.empty_unit 0 0 0 0 0
  have good := positive CorrectedRow.emptyLattice CorrectedRow.empty_unit 0 0 0 0 0
  change CorrectedRow.actual.readout () ⟨CorrectedRow.emptyLattice, CorrectedRow.empty_unit, 0, 0, 0, 0⟩ 0 + 1 = _ at bad
  have eqn := bad.trans good.symm
  have shifted : CorrectedRow.actual.readout () ⟨CorrectedRow.emptyLattice, CorrectedRow.empty_unit, 0, 0, 0, 0⟩ 0 + 1 =
      CorrectedRow.actual.readout () ⟨CorrectedRow.emptyLattice, CorrectedRow.empty_unit, 0, 0, 0, 0⟩ 0 + 0 := by
    simpa only [add_zero] using eqn
  exact one_ne_zero (add_left_cancel shifted)

def family : Registration arena sourceScope_original_corrected_row_finite_reduction where
  actual := CorrectedRow.actual
  bridge := source_bridge
  variation := ⟨positive, CorrectedRow.rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law CorrectedRow.actual CorrectedRow.rejected negative
  dependence := CorrectedRow.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.original_corrected_row_finite_reduction)
    (Realization CorrectedRow.signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.FiniteReduction.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource.FiniteReduction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize CorrectedRow.signature CorrectedRow.actual.readout CorrectedRow.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteReduction

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource
