import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.GroupWords.InvolutionExactLength
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Group.Int.Defs

set_option autoImplicit false
namespace Reg.D5.S3.Combinatorics.GroupWords.InvolutionExactLength
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.GroupWords.InvolutionExactLength
open scoped Pointwise
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => Set.Icc (-(m : ℤ)) (m + 1)) Empty.elim

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) Empty.elim

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {G : Type u} [Group G] (x v : G)
    (_ : x * x = 1) (_ : v * v = 1) (m : ℕ),
    ({x, v} : Set G) ^ (2 * m) =
      (fun k : ℤ => (x * v) ^ k) '' Set.Icc (-(m : ℤ)) m ∧
    ({x, v} : Set G) ^ (2 * m + 1) =
      (fun k : ℤ => x * (x * v) ^ k) '' R.readout () () m

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have bad := (h (G := ULift.{u} (Multiplicative ℤ)) 1 1 (by simp) (by simp) 0).2
  simpa [rejected, realize] using bad

def evidence : Registration arena.{u} (type_of% (@exact_length_products.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exact_length_products.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Set.Icc (-(0 : ℤ)) (0 + 1) ≠ Set.Icc (-(1 : ℤ)) (1 + 1)
    intro he
    have hm : (-1 : ℤ) ∈ Set.Icc (-(1 : ℤ)) (1 + 1) := by constructor <;> decide
    rw [← he] at hm
    norm_num at hm

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exact_length_products.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.GroupWords.InvolutionExactLength.exact_length_products.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.GroupWords.InvolutionExactLength.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.GroupWords.InvolutionExactLength
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration
end Reg.D5.S3.Combinatorics.GroupWords.InvolutionExactLength
