import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.GraphSubstitution.IndependenceFibers

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.GraphSubstitution.IndependenceFibers

namespace Reg.D5.S3.Combinatorics.GraphSubstitution.IndependenceFibers

universe u v

structure Parameters where
  V : Type u
  W : V → Type v
  B : SimpleGraph V
  H : ∀ i, SimpleGraph (W i)

abbrev signature : Signature where
  Params := Parameters.{u, v}
  State p := Set (Σ i, p.W i)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ p T => (substitution p.B p.H).IsIndepSet T)
    (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law R := ∀ p : Parameters.{u, v}, ∀ T : Set (Σ i, p.W i),
    R.readout () p T ↔
      p.B.IsIndepSet (support T) ∧ ∀ i, (p.H i).IsIndepSet (fiber T i)

private theorem bridge :
    (type_of% (@isIndepSet_substitution_iff.{u, v})) ↔ arena.{u, v}.Law actual := by
  constructor
  · intro h p T
    exact h p.B p.H T
  · intro h V W B H T
    exact h ⟨V, W, B, H⟩ T

private abbrev edgeParameters : Parameters.{u, v} where
  V := ULift.{u} Unit
  W _ := ULift.{v} Bool
  B := ⊥
  H _ := ⊤

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hright : edgeParameters.B.IsIndepSet (support (∅ : Set (Σ i, edgeParameters.W i))) ∧
      ∀ i, (edgeParameters.H i).IsIndepSet (fiber ∅ i) := by
    constructor
    · rintro i ⟨x, hx, _⟩
      exact hx.elim
    · intro i a ha
      exact ha.elim
  exact (h edgeParameters ∅).mpr hright

private theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  refine ⟨edgeParameters, ∅, Set.univ, ?_⟩
  intro h
  change (substitution edgeParameters.B edgeParameters.H).IsIndepSet ∅ =
    (substitution edgeParameters.B edgeParameters.H).IsIndepSet Set.univ at h
  have hempty : (substitution edgeParameters.B edgeParameters.H).IsIndepSet ∅ := by
    intro x hx
    exact hx.elim
  have hfull := Eq.mp h hempty
  have hne : (⟨⟨()⟩, ⟨false⟩⟩ : Σ j, edgeParameters.W j) ≠ ⟨⟨()⟩, ⟨true⟩⟩ := by
    simp
  apply hfull (Set.mem_univ _) (Set.mem_univ _) hne
  exact Or.inr ⟨⟨()⟩, ⟨false⟩, ⟨true⟩, rfl, rfl, by simp [edgeParameters]⟩

def family : Registration arena.{u, v} (type_of% (@isIndepSet_substitution_iff.{u, v})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@isIndepSet_substitution_iff.{u, v}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@isIndepSet_substitution_iff.{u, v}) (Realization signature.{u, v}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.GraphSubstitution.IndependenceFibers.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.GraphSubstitution.IndependenceFibers.family
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
    (fun _ p T => (substitution p.B p.H).IsIndepSet T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.GraphSubstitution.IndependenceFibers
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.GraphSubstitution.IndependenceFibers
