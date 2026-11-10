import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.LeastConfirmationGeneration
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Foundation.LeastConfirmationGeneration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Module

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.LeastConfirmationGeneration

/-- The carrier and its algebraic structures remain parameters of the whole family. -/
structure Carrier where
  space : Type u
  addition : AddCommGroup space
  scalar : @Module ℝ space _ addition.toAddCommMonoid

attribute [instance] Carrier.addition Carrier.scalar

abbrev signature : Signature where
  Params := Carrier.{u}
  State k := k.space →ₗ[ℝ] ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ k := (k.space →ₗ[ℝ] ℝ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => Eq f) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
    {P : Set A} (C : ConfirmationSystem P) (f : A →ₗ[ℝ] ℝ) (_hf : Positive P f),
    ∃ l : List (ℝ × P), (∀ a ∈ l, 0 < a.1) ∧
      R.readout () ⟨A, inferInstance, inferInstance⟩ f
        ((l.map (fun a => a.1 • C.effect a.2)).sum) ∧
      l.Pairwise (fun a b => C.effect b.2 a.2 = 0 ∧ C.effect a.2 b.2 = 0) ∧
      (∀ q : P, ((l.map (fun a => C.effect a.2)).sum) q ≤ C.unit q) ∧
      l.length ≤ finrank ℝ A ∧ (f = C.unit → ∀ a ∈ l, a.1 = 1)

private def zeroSystem : ConfirmationSystem (∅ : Set (ULift.{u} (Fin 0 → ℝ))) where
  unit := 0
  spanning := Subsingleton.elim _ _
  normalized p := False.elim p.property
  effect p := False.elim p.property
  proper p := False.elim p.property
  confirms p := False.elim p.property
  least p := False.elim p.property
  maximum f _ hne := (hne (Subsingleton.elim _ _)).elim

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨l, _, hfalse, _⟩ := h zeroSystem 0 (by intro p; exact False.elim p.property)
  exact hfalse

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let k : Carrier.{u} := ⟨ULift.{u} ℝ, inferInstance, inferInstance⟩
  let f : k.space →ₗ[ℝ] ℝ := ULift.moduleEquiv.toLinearMap
  refine ⟨k, 0, f, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : k.space →ₗ[ℝ] ℝ) = 0) = (f = 0) at he
  have hf : f = 0 := Eq.mp he rfl
  have hh := LinearMap.congr_fun hf (ULift.up 1)
  change (1 : ℝ) = 0 at hh
  exact one_ne_zero hh

def family : Registration arena.{u} (type_of% @positive_dual_generation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_dual_generation.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@positive_dual_generation.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Foundation.LeastConfirmationGeneration.unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.LeastConfirmationGeneration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ f => Eq f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.LeastConfirmationGeneration
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 6
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Foundation.LeastConfirmationGeneration
