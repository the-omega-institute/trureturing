import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.LeastConfirmationGeneration
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Foundation.LeastConfirmationGeneration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Module

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Foundation.LeastConfirmationGeneration

/-- Lists of arbitrary probes are states; the observation is their actual length. -/
abbrev signature : Signature where
  Params := Σ A : Type u, Set A
  State k := List (ℝ × k.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ l => l.length) (fun e => Empty.elim e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
    {P : Set A} (C : ConfirmationSystem P) (f : A →ₗ[ℝ] ℝ) (_hf : Positive P f),
    ∃ l : List (ℝ × P), (∀ a ∈ l, 0 < a.1) ∧
      f = (l.map (fun a => a.1 • C.effect a.2)).sum ∧
      l.Pairwise (fun a b => C.effect b.2 a.2 = 0 ∧ C.effect a.2 b.2 = 0) ∧
      (∀ q : P, ((l.map (fun a => C.effect a.2)).sum) q ≤ C.unit q) ∧
      R.readout () ⟨A, P⟩ l ≤ finrank ℝ A ∧ (f = C.unit → ∀ a ∈ l, a.1 = 1)

private def zeroSystem : ConfirmationSystem (∅ : Set (ULift.{u} (Fin 0 → ℝ))) where
  unit := 0
  normalized p := False.elim p.property
  effect p := False.elim p.property
  proper p := False.elim p.property
  confirms p := False.elim p.property
  least p := False.elim p.property
  maximum f _ hne := (hne (Subsingleton.elim _ _)).elim

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨l, _, _, _, _, hbound, _⟩ :=
    h zeroSystem 0 (by intro p; exact False.elim p.property)
  have hh : (1 : ℕ) ≤ 0 := by simpa [rejected, realize] using hbound
  omega

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let k : signature.{u}.Params := ⟨ULift.{u} ℝ, {ULift.up 1}⟩
  let a : ℝ × k.2 := (1, ⟨ULift.up 1, Set.mem_singleton _⟩)
  refine ⟨k, [], [a], ?_⟩
  simp [actual, realize]

def family : Registration arena.{u} (type_of% @positive_dual_generation.{u}) where
  actual := realize signature.{u} (fun _ _ l => l.length) (fun e => Empty.elim e)
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
  readout := some (realize signature.{u} (fun _ _ l => l.length) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.LeastConfirmationGeneration
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Foundation.LeastConfirmationGeneration
