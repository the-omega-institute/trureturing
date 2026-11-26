import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Taylor coefficient readouts for monomials and arbitrary analytic germs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround
open FourPoint.OriginalFourMActualChart (Chart Puncture scale scaleRoot loweringParameter)
open OriginalFourMOccupationTransport (rawLocal halfJacobian inverseRoot)
open OriginalFourMInverseJets
open OriginalGaussianSewnAnalytic (coefficient)
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℂ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize _ (fun _ m f => coefficient m f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize _ (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨0, fun _ => 0, fun _ => 1, ?_⟩
  simp [actual, realize, coefficient]

namespace Monomial

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ} (_hx : 0 < x) (_hx1 : x < 1) (c : Chart) (i : Puncture) (m n : ℕ),
    R.readout () m (fun u => rawLocal c x i u ^ n / halfJacobian c x i (inverseRoot c x i u)) =
      if n ≤ m then
        (scaleRoot c x i)⁻¹ * ((scale c x i)⁻¹) ^ m *
          (-loweringParameter c i) ^ (m - n) * Ring.choose ((m : ℂ) + 1 / 2) (m - n)
      else 0

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  simpa [rejected, realize] using h (x := (1 : ℝ) / 2) (by norm_num) (by norm_num) .A .P 0 1

def family : Registration arena (type_of% (@coefficient_rawLocal_pow_div_halfJacobian)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficient_rawLocal_pow_div_halfJacobian, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coefficient_rawLocal_pow_div_halfJacobian) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets.Monomial.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets.Monomial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Monomial

namespace Substitution

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f : ℂ → ℂ} (_hf : AnalyticAt ℂ f 0)
      {x : ℝ} (_hx : 0 < x) (_hx1 : x < 1) (c : Chart) (i : Puncture) (m : ℕ),
    R.readout () m (fun u => f (rawLocal c x i u) / halfJacobian c x i (inverseRoot c x i u)) =
      ∑ n ∈ Finset.range (m + 1),
        coefficient n f * ((scaleRoot c x i)⁻¹ * ((scale c x i)⁻¹) ^ m *
          (-loweringParameter c i) ^ (m - n) * Ring.choose ((m : ℂ) + 1 / 2) (m - n))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  simpa [rejected, realize, coefficient] using
    h (f := fun _ => 0) analyticAt_const (x := (1 : ℝ) / 2) (by norm_num) (by norm_num) .A .P 0

def family : Registration arena (type_of% (@coefficient_comp_rawLocal_div_halfJacobian)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficient_comp_rawLocal_div_halfJacobian, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coefficient_comp_rawLocal_div_halfJacobian) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets.Substitution.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets.Substitution.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Substitution

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMInverseJets
