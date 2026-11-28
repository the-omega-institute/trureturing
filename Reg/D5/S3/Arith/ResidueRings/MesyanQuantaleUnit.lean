import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ResidueRings.MesyanQuantaleUnit
import Reg.Support.SingleDependentReadout

/-! Left multiplication by the top additive submonoid, observed on the full
submonoid domain. The ring and the right identity law are fixed. -/

namespace Reg.D5.S3.Arith.ResidueRings.MesyanQuantaleUnit

open _root_.D5.S3.Arith.ResidueRings.MesyanQuantaleUnit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Pointwise

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => AddSubmonoid ↥finiteSupportSubring)
    (fun _ => AddSubmonoid ↥finiteSupportSubring)

def actual : Realization signature :=
  realize signature (fun _ _ M => (⊤ : AddSubmonoid ↥finiteSupportSubring) * M) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    (∃ a : ↥finiteSupportSubring, a ≠ 0) ∧
    (∀ e : ↥finiteSupportSubring, ∃ a : ↥finiteSupportSubring, e * a ≠ a ∨ a * e ≠ a) ∧
    (∀ M : AddSubmonoid ↥finiteSupportSubring,
      R.readout () () M = M ∧ M * (⊤ : AddSubmonoid ↥finiteSupportSubring) = M)

private theorem bot_ne_top : (⊥ : AddSubmonoid ↥finiteSupportSubring) ≠ ⊤ := by
  obtain ⟨a, ha⟩ := finiteSupportSubring_properties.1
  intro h
  have hm : a ∈ (⊥ : AddSubmonoid ↥finiteSupportSubring) := h.symm ▸ AddSubmonoid.mem_top a
  exact ha (AddSubmonoid.mem_bot.mp hm)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact bot_ne_top (h.2.2 ⊤).1

def family : Registration arena (type_of% finiteSupportSubring_properties) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finiteSupportSubring_properties, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), (⊥ : AddSubmonoid ↥finiteSupportSubring),
      (⊤ : AddSubmonoid ↥finiteSupportSubring), ?_⟩
    change (⊤ : AddSubmonoid ↥finiteSupportSubring) * ⊥ ≠ ⊤ * ⊤
    rw [(finiteSupportSubring_properties.2.2 ⊥).1, (finiteSupportSubring_properties.2.2 ⊤).1]
    exact bot_ne_top

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    finiteSupportSubring_properties (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.ResidueRings.MesyanQuantaleUnit.auditUnit
  realizationName := `Reg.D5.S3.Arith.ResidueRings.MesyanQuantaleUnit.family
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
    (fun _ _ M => (⊤ : AddSubmonoid ↥finiteSupportSubring) * M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.ResidueRings.MesyanQuantaleUnit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.ResidueRings.MesyanQuantaleUnit
