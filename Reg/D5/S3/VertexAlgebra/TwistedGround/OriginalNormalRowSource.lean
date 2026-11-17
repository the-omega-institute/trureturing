import D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource
import LeanInformationAuditInterface.Contract.Registration

/-! Exact source-type mirrors preserve the original theorem telescopes. A mirror
is compiled audit evidence, not a four-slot registration or a binding verdict. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource

abbrev sourceScope_normalMatrix_symm := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.normalMatrix_symm.{u})
theorem source_actual_normalMatrix_symm : sourceScope_normalMatrix_symm.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.normalMatrix_symm.{u}

abbrev sourceScope_original_normal_row_finite := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.original_normal_row_finite.{u})
theorem source_actual_original_normal_row_finite : sourceScope_original_normal_row_finite.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.original_normal_row_finite.{u}

abbrev sourceScope_restricted_reconstruct := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.restricted_reconstruct)
theorem source_actual_restricted_reconstruct : sourceScope_restricted_reconstruct :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.restricted_reconstruct

abbrev sourceScope_embedded_weight := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.embedded_weight.{u})
theorem source_actual_embedded_weight : sourceScope_embedded_weight.{u} :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.embedded_weight.{u}

abbrev sourceScope_normalLaurentRow_native := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.normalLaurentRow_native)
theorem source_actual_normalLaurentRow_native : sourceScope_normalLaurentRow_native :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.normalLaurentRow_native

abbrev sourceScope_original_normal_row := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.original_normal_row)
theorem source_actual_original_normal_row : sourceScope_original_normal_row :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.original_normal_row

abbrev sourceScope_original_corrected_normal_convolution := type_of% (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.original_corrected_normal_convolution)
theorem source_actual_original_corrected_normal_convolution : sourceScope_original_corrected_normal_convolution :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.original_corrected_normal_convolution


open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedCoefficients
open LatticeHalfFockChargedTensorCoefficients
open TwistedGround OriginalFourMChargeCoset OriginalNormalRowSource
open OriginalCorrectedRowRecompositionSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Convolution
open _root_.Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalAffineRecompositionSource

def arena : Arena where
  signature := CorrectedRow.signature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (alpha beta gamma : Index D →₀ ℕ) (e : ℤ),
    R.readout () ⟨D, hu, a, alpha, beta, gamma⟩ e =
      (FactorialFockMetric.weight beta : ℂ) * (FactorialFockMetric.weight gamma : ℂ) *
        ∑ s ∈ (LatticeHalfFockFiniteCorrection.Corr D a (MvPolynomial.monomial alpha 1)).support,
          ∑ delta ∈ (LatticeHalfFockFiniteCorrection.Corr D a (MvPolynomial.monomial alpha 1) s).support,
            (LatticeHalfFockFiniteCorrection.Corr D a (MvPolynomial.monomial alpha 1) s).coeff delta *
              (FactorialFockMetric.weight delta : ℂ) * normalLaurentRow D a delta beta gamma
                (e+2*(s : ℤ)+chargeNorm D a)

theorem source_bridge : sourceScope_original_corrected_normal_convolution ↔ arena.Law CorrectedRow.actual :=
  Iff.rfl

theorem positive : arena.Law CorrectedRow.actual :=
  @_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.original_corrected_normal_convolution

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

def family : Registration arena sourceScope_original_corrected_normal_convolution where
  actual := CorrectedRow.actual
  bridge := source_bridge
  variation := ⟨positive, CorrectedRow.rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law CorrectedRow.actual CorrectedRow.rejected negative
  dependence := CorrectedRow.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.original_corrected_normal_convolution)
    (Realization CorrectedRow.signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.Convolution.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource.Convolution.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource
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

end Convolution

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalNormalRowSource
