import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative
noncomputable section
open scoped Topology
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianResolvent OriginalGaussianDifferentiation OriginalGaussianSourceMeans OriginalGaussianSourceDerivative
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative
abbrev functionSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℝ → ℂ)
def functionActual : Realization functionSignature :=
  realize _ (fun _ _ f => f) (fun e => nomatch e)
def functionShifted : Realization functionSignature :=
  realize _ (fun _ _ f u => f u + (u : ℂ)) (fun e => nomatch e)
private theorem functionDependence : ObservationalDependence functionSignature functionActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he : (0 : ℂ) = 1 := congrFun h 0
  exact zero_ne_one he

namespace hasDerivAt_radial_source_pairing
abbrev arena : Arena where
  signature := functionSignature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    HasDerivAt (R.readout () () (fun u : ℝ => innerSL ℂ (star (sourceFamily 0 (Real.sqrt u : ℂ))) (columnSeries (Real.sqrt u : ℂ))))
      ((((1 / ((1 - r) * F r ^ 2) - 1) / (2 * r) : ℝ)) : ℂ) r
private theorem rejected_fails : ¬ arena.Law functionShifted := by
  intro h
  have hb := h (r := 1 / 2) (by norm_num) (by norm_num)
  have ha := (@hasDerivAt_radial_source_pairing (1 / 2) (by norm_num) (by norm_num)).add
    (hasDerivAt_id (1 / 2 : ℝ)).ofReal_comp
  have he := hb.unique ha
  simp only [Complex.ofReal_one] at he
  have he' : (0 : ℂ) = 1 := by linear_combination he
  exact zero_ne_one he'
def family : Registration arena (type_of% (@hasDerivAt_radial_source_pairing)) where
  actual := functionActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_radial_source_pairing, functionShifted, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := functionDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_radial_source_pairing) (Realization functionSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative.hasDerivAt_radial_source_pairing.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative.hasDerivAt_radial_source_pairing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize functionSignature functionActual.readout functionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end hasDerivAt_radial_source_pairing

namespace hasDerivAt_radial_sourceConstant
abbrev arena : Arena where
  signature := functionSignature
  Law R := ∀ {r : ℝ} (hr : 0 < r) (hr1 : r < 1),
    HasDerivAt (R.readout () () (fun u : ℝ => sourceConstant (Real.sqrt u : ℂ)))
      ((((1 / ((1 - r) * F r ^ 2) - 1) / (2 * r) : ℝ)) : ℂ) r
private theorem rejected_fails : ¬ arena.Law functionShifted := by
  intro h
  have hb := h (r := 1 / 2) (by norm_num) (by norm_num)
  have ha := (@hasDerivAt_radial_sourceConstant (1 / 2) (by norm_num) (by norm_num)).add
    (hasDerivAt_id (1 / 2 : ℝ)).ofReal_comp
  have he := hb.unique ha
  simp only [Complex.ofReal_one] at he
  have he' : (0 : ℂ) = 1 := by linear_combination he
  exact zero_ne_one he'
def family : Registration arena (type_of% (@hasDerivAt_radial_sourceConstant)) where
  actual := functionActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_radial_sourceConstant, functionShifted, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_fails
  dependence := functionDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_radial_sourceConstant) (Realization functionSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative.hasDerivAt_radial_sourceConstant.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative.hasDerivAt_radial_sourceConstant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize functionSignature functionActual.readout functionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end hasDerivAt_radial_sourceConstant

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceDerivative
