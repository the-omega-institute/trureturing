import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Observations of signed residuals as functions of the initial vector. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual


noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private abbrev Params := Σ D : ℕ, Σ _ : Matrix (Fin D) (Fin D) ℤ, Σ _ : Fin D → ℤ, ℕ

namespace ResidualAsPower

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Params (fun p => Fin p.1 → ℤ) (fun _ => ℤ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ p v => residual p.2.1 v p.2.2.1 p.2.2.2)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p v => residual p.2.1 v p.2.2.1 p.2.2.2 + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {D : ℕ} (M : Matrix (Fin D) (Fin D) ℤ) (v e : Fin D → ℤ) (t : ℕ),
    R.readout () ⟨D, M, e, t⟩ v =
      dotProduct (residualVector M v) ((M ^ t).mulVec e)

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := h (0 : Matrix (Fin 1) (Fin 1) ℤ) (fun _ => 0) (fun _ => 0) 0
  have right := residual_as_power (0 : Matrix (Fin 1) (Fin 1) ℤ)
    (fun _ => 0) (fun _ => 0) 0
  change residual (0 : Matrix (Fin 1) (Fin 1) ℤ) (fun _ => 0) (fun _ => 0) 0 + 1 = _
    at wrong
  omega

def family : Registration arena (type_of% @residual_as_power) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨residual_as_power, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨⟨1, 1, (fun _ => 1), 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    change residual (1 : Matrix (Fin 1) (Fin 1) ℤ) (fun _ => 0) (fun _ => 1) 0 ≠
      residual (1 : Matrix (Fin 1) (Fin 1) ℤ) (fun _ => 1) (fun _ => 1) 0
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@residual_as_power) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635Residual.residual_as_power.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual
    definition := none
    coordinates := #[0, 1, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ResidualAsPower


end

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual
