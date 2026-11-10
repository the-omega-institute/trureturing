import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Walks.GallaiRoy

set_option autoImplicit false
noncomputable section
open scoped Classical
open LeanInformationAudit SimpleGraph
open _root_.GallaiRoy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Walks.GallaiRoy
universe u

abbrev signature : Signature where
  Params := (V : Type u) × ℕ
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ),
    r.readout () ⟨V, k⟩ G = true ↔
      ∃ o : V → V → Prop, IsOrientation G o ∧
        ∀ (m : ℕ) (f : Fin m → V), IsDirectedPath o f → m ≤ k

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V : Type u := ULift.{u} Empty
  have hp := (colorable_iff_exists_orientation (⊥ : SimpleGraph V) 0).mp
    (Colorable.of_isEmpty (G := (⊥ : SimpleGraph V)) 0)
  have hf : false = true := (h (⊥ : SimpleGraph V) 0).mpr hp
  cases hf

def family : Registration arena.{u} (type_of% (@colorable_iff_exists_orientation.{u})) where
  actual := realize signature (fun _ p G => decide (G.Colorable p.2)) (fun e => nomatch e)
  bridge := by simp only [arena, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, realize, decide_eq_true_eq] using
    @colorable_iff_exists_orientation.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    let V : Type u := ULift.{u} Bool
    refine ⟨⟨V, 1⟩, ⊥, ⊤, ?_⟩
    have hne : (⊤ : SimpleGraph V) ≠ ⊥ := by
      intro he
      have hp := congrArg (fun G : SimpleGraph V => G.Adj ⟨false⟩ ⟨true⟩) he
      simp at hp
    simp [realize, colorable_one_iff, hne]

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@colorable_iff_exists_orientation.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `GallaiRoy.colorable_iff_exists_orientation.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.GallaiRoy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p G => decide (G.Colorable p.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.GallaiRoy
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Combinatorics.Graph.Walks.GallaiRoy
