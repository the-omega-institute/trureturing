import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Probability.BinaryEndpointLaw
import Mathlib.Algebra.Module.ULift
import Reg.Support.DependentFamily

/-! The mass function depends on the endpoint choices. -/

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Probability.BinaryEndpointLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Probability.BinaryEndpointLaw

noncomputable section
universe u v

private structure Parameters where
  Index : Type u
  Space : Type v
  [finiteIndex : Fintype Index]
  [finiteSpace : Fintype Space]
  [additiveSpace : AddCommGroup Space]
  [binarySpace : Module (ZMod 2) Space]
  generator : Index → Space

attribute [instance] Parameters.finiteIndex Parameters.finiteSpace
  Parameters.additiveSpace Parameters.binarySpace

private abbrev signature : Signature where
  Params := Parameters.{u, v}
  State c := c.Index → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ c := c.Space → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def uniform (c : Parameters.{u, v}) : c.Space → ℂ :=
  fun _ => (Fintype.card c.Space : ℂ)⁻¹

private def actual : Realization signature.{u, v} :=
  realize signature (fun _ c p => mass c.generator p) (fun e => nomatch e)

private def rejected : Realization signature.{u, v} :=
  realize signature (fun _ c _ => uniform c) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {ι : Type u} {V : Type v} [Fintype ι] [Fintype V]
    [AddCommGroup V] [Module (ZMod 2) V] (a : ι → V) (p : ι → ℂ),
    let c : Parameters := ⟨ι, V, a⟩
    (R.readout () c p = uniform c) ↔
      Submodule.span (ZMod 2) {v | ∃ i, p i = 1 / 2 ∧ a i = v} = ⊤

private def exampleParameters : Parameters.{u, v} :=
  ⟨ULift.{u} Unit, ULift.{v} (ZMod 2), fun _ => ⟨1⟩⟩

private theorem zero_not_fair :
    Submodule.span (ZMod 2) {x : exampleParameters.{u, v}.Space |
      ∃ i : exampleParameters.{u, v}.Index,
        (0 : ℂ) = 1 / 2 ∧ exampleParameters.{u, v}.generator i = x} ≠ ⊤ := by
  have h : (0 : ℂ) ≠ 1 / 2 := by norm_num
  simpa [h] using
    (bot_ne_top : (⊥ : Submodule (ZMod 2) (ULift.{v} (ZMod 2))) ≠ ⊤)

private theorem fair_spans :
    Submodule.span (ZMod 2) {x : exampleParameters.{u, v}.Space |
      ∃ i : exampleParameters.{u, v}.Index,
        (1 / 2 : ℂ) = 1 / 2 ∧ exampleParameters.{u, v}.generator i = x} = ⊤ := by
  apply top_unique
  intro x _
  have hgen : (⟨1⟩ : ULift.{v} (ZMod 2)) ∈
      Submodule.span (ZMod 2) {x : exampleParameters.{u, v}.Space |
        ∃ i : exampleParameters.{u, v}.Index,
          (1 / 2 : ℂ) = 1 / 2 ∧ exampleParameters.{u, v}.generator i = x} :=
    Submodule.subset_span ⟨⟨()⟩, rfl, rfl⟩
  convert (Submodule.span (ZMod 2) _).smul_mem x.down hgen using 1
  exact ULift.ext _ _ (by simp)

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  exact zero_not_fair ((h exampleParameters.generator (fun _ => 0)).mp rfl)

private theorem actual_varies :
    actual.{u, v}.readout () exampleParameters (fun _ => 0) ≠
      actual.{u, v}.readout () exampleParameters (fun _ => 1 / 2) := by
  intro h
  exact zero_not_fair ((mass_eq_uniform_iff_span exampleParameters.generator (fun _ => 0)).mp
    (h.trans ((mass_eq_uniform_iff_span exampleParameters.generator (fun _ => 1 / 2)).mpr
      fair_spans)))

def evidence : Registration arena.{u, v} (type_of% (@mass_eq_uniform_iff_span.{u, v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mass_eq_uniform_iff_span, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := fun _ => ⟨exampleParameters, fun _ => 0, fun _ => 1 / 2, actual_varies⟩

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@mass_eq_uniform_iff_span.{u, v}) (Realization signature.{u, v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Probability.BinaryEndpointLaw.mass_eq_uniform_iff_span
  realizationName := `Reg.D5.S3.Combinatorics.Probability.BinaryEndpointLaw.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨evidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c p => mass c.generator p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Probability.BinaryEndpointLaw
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Probability.BinaryEndpointLaw
