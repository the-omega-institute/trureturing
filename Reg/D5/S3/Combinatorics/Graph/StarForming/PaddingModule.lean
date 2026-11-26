import D5.S3.Combinatorics.Graph.StarForming.PaddingModule
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.StarForming.PaddingModule
open _root_.D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace Reg.D5.S3.Combinatorics.Graph.StarForming.PaddingModule

abbrev signature : Signature where
  Params := Type
  State I := Finset (Fin 14 ⊕ (I × Fin 20))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (I : Type), Finset (Fin 14 ⊕ (I × Fin 20)) → ℕ :=
  fun _ _ S => S.card

def noAnchor : ∀ (_ : Empty) (I : Type), Finset (Fin 14 ⊕ (I × Fin 20)) :=
  fun e => nomatch e

def actual : Realization signature := realize signature observation noAnchor

def bad : Realization signature := realize signature (fun _ _ _ => 20) noAnchor

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {I : Type} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) (mark : I) (S : Finset (Fin 14 ⊕ (I × Fin 20))),
    IsKIndependent (graph e mark) 2 S → r.readout () I S ≤ 7+12*Fintype.card I

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hi : IsKIndependent (graph (Equiv.refl Unit) ()) 2
      (∅ : Finset (Fin 14 ⊕ (Unit × Fin 20))) := by simp [IsKIndependent]
  have hh := h (Equiv.refl Unit) () ∅ hi
  change (20 : ℕ) ≤ 7+12*Fintype.card Unit at hh
  norm_num at hh

abbrev SourceClaim : Prop := ∀ {I : Type} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) (mark : I) (S : Finset (Fin 14 ⊕ (I × Fin 20))),
    IsKIndependent (graph e mark) 2 S → S.card ≤ 7+12*Fintype.card I

def family : Registration arena SourceClaim where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := ⟨fun e mark S hS => beta_cap e mark S hS,bad,bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨Unit,∅,{Sum.inl 0},?_⟩
    change (∅ : Finset (Fin 14 ⊕ (Unit × Fin 20))).card ≠
      ({Sum.inl 0} : Finset (Fin 14 ⊕ (Unit × Fin 20))).card
    simp

noncomputable def betaCapRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Combinatorics.Graph.StarForming.PaddingModule.beta_cap)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.StarForming.PaddingModule.beta_cap.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.StarForming.PaddingModule.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation noAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.StarForming.PaddingModule
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.StarForming.PaddingModule
