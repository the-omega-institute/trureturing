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

private abbrev Parameters :=
  Σ ι : Type u, Σ V : Type v, Σ _ : Fintype ι, Σ _ : AddCommGroup V, (ι → V)

private abbrev Parameters.Index (c : Parameters.{u, v}) : Type u := c.1

private abbrev Parameters.Space (c : Parameters.{u, v}) : Type v := c.2.1

private instance (c : Parameters.{u, v}) : Fintype c.Index := c.2.2.1

private instance (c : Parameters.{u, v}) : AddCommGroup c.Space := c.2.2.2.1

private abbrev Parameters.generator (c : Parameters.{u, v}) : c.Index → c.Space :=
  c.2.2.2.2

private abbrev parameters {ι : Type u} {V : Type v} [Fintype ι]
    [AddCommGroup V] (a : ι → V) : Parameters.{u, v} :=
  ⟨ι, V, inferInstance, inferInstance, a⟩

private abbrev signature : Signature where
  Params := Parameters.{u, v}
  State c := c.Index → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ c := c.Space → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u, v} :=
  realize signature (fun _ c p => mass c.generator p) (fun e => nomatch e)

private def rejected : Realization signature.{u, v} :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ {ι : Type u} {V : Type v} [Fintype ι] [Fintype V]
    [AddCommGroup V] [Module (ZMod 2) V] (a : ι → V) (p : ι → ℂ),
    (R.readout () (parameters a) p = fun _ => (Fintype.card V : ℂ)⁻¹) ↔
      Submodule.span (ZMod 2) {v | ∃ i, p i = 1 / 2 ∧ a i = v} = ⊤

private def exampleParameters : Parameters.{u, v} :=
  parameters (fun _ : ULift.{u} Unit => (⟨1⟩ : ULift.{v} (ZMod 2)))

private instance : Module (ZMod 2) exampleParameters.{u, v}.Space :=
  inferInstanceAs (Module (ZMod 2) (ULift.{v} (ZMod 2)))

private instance : Fintype exampleParameters.{u, v}.Space :=
  inferInstanceAs (Fintype (ULift.{v} (ZMod 2)))

private theorem zero_not_fair :
    Submodule.span (ZMod 2) {x : exampleParameters.{u, v}.Space |
      ∃ i : exampleParameters.{u, v}.Index,
        (0 : ℂ) = 1 / 2 ∧ exampleParameters.{u, v}.generator i = x} ≠ ⊤ := by
  have h : (0 : ℂ) ≠ 1 / 2 := by norm_num
  simp only [h, false_and, exists_false, Set.setOf_false, Submodule.span_empty]
  exact (bot_ne_top : (⊥ : Submodule (ZMod 2) (ULift.{v} (ZMod 2))) ≠ ⊤)

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
  have hx : x.down • (⟨1⟩ : exampleParameters.{u, v}.Space) = x :=
    ULift.ext (mul_one x.down)
  rw [← hx]
  exact (Submodule.span (ZMod 2) _).smul_mem x.down hgen

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  have he := (h exampleParameters.generator (fun _ => 1 / 2)).mpr fair_spans
  have hz : (0 : ℂ) = (Fintype.card exampleParameters.{u, v}.Space : ℂ)⁻¹ :=
    congrFun he ⟨0⟩
  exact (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) hz.symm

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
    coordinates := #[0, 1, 6]
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
