import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.IsolatedSmallSource
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.IsolatedSmallSource

namespace Reg.D5.S3.Combinatorics.Circle.IsolatedSmallSource
universe u
noncomputable section

/-- The actual weight operand in the returned word's strip condition. -/
abbrev signature : Signature where
  Params := Σ α : Type u, α → ℤ
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p i => p.2 i) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Hypotheses and the zero sum retain the original weights; the selected
source operand belongs only to the returned strip observation. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [Fintype α] [Nonempty α]
    (σ : Equiv.Perm α) (w : α → ℤ) (Q : ℤ) (hQ : 2 ≤ Q)
    (hbound : ∀ i, -(2 * Q - 1) ≤ w i ∧ w i ≤ 2 * Q - 1)
    (hstep : ∀ i, w (σ i) = doubleStep (4 * Q - 1) (w i))
    (hsmall : (∀ i, |w i| < Q → 0 ≤ w i) ∨
      (∀ i, |w i| < Q → w i ≤ 0))
    (hisolated : ∀ i, |w i| < Q → Q ≤ |w (σ i)|),
    ∃ word : List α, word.Perm (Finset.univ.toList : List α) ∧
      InStrip (R.readout () ⟨α, w⟩) (2 * Q - 1) 0 word ∧
      (word.map w).sum = 0

private def sampleRotate : Equiv.Perm (ULift.{u} (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.swap (0 : Fin 2) 1).trans Equiv.ulift.symm)

private def sampleWeight (i : ULift.{u} (Fin 2)) : ℤ :=
  if i.down = 0 then 5 else -5

private theorem sample_abs (i : ULift.{u} (Fin 2)) : |sampleWeight i| = 5 := by
  unfold sampleWeight
  split_ifs <;> norm_num

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  have hnosmall (i : ULift.{u} (Fin 2)) : ¬|sampleWeight i| < 4 := by
    rw [sample_abs]
    norm_num
  obtain ⟨word, hp, hs, _⟩ := h sampleRotate sampleWeight 4
    (by norm_num)
    (by intro i; unfold sampleWeight; split_ifs <;> norm_num)
    (by
      intro i
      obtain ⟨i⟩ := i
      fin_cases i <;>
        norm_num [sampleRotate, sampleWeight, Equiv.swap_apply_def, doubleStep])
    (Or.inl (fun i hi => False.elim (hnosmall i hi)))
    (fun i hi => False.elim (hnosmall i hi))
  have hmem : (ULift.up (0 : Fin 2)) ∈ word := hp.mem_iff.mpr (by simp)
  change InStrip (fun _ : ULift.{u} (Fin 2) => (-1 : ℤ)) 7 0 word at hs
  cases word with
  | nil => simpa using hmem
  | cons a tail =>
    have hh := (inStrip_prefix hs 1).1
    norm_num at hh

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 2), sampleWeight⟩,
    ULift.up (0 : Fin 2), ULift.up (1 : Fin 2), ?_⟩
  norm_num [actual, realize, sampleWeight]

def source_registration : Registration arena.{u}
    (type_of% (@finite_isolated_small_completion.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_isolated_small_completion.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- Source selection addresses the weight operand inside the existential
word's InStrip conjunct, preserving every other source occurrence. -/
def audit.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Circle.IsolatedSmallSource.finite_isolated_small_completion.{u_1})
    (type_of% (realize signature.{u_1} (fun _ p i => p.2 i) (fun e => nomatch e)))
    Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.IsolatedSmallSource.finite_isolated_small_completion.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.IsolatedSmallSource.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1}⟩
  objectArena := .source ⟨arena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1} ⟨source_registration.{u_1}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1} (fun _ p i => p.2 i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.IsolatedSmallSource
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration

end
end Reg.D5.S3.Combinatorics.Circle.IsolatedSmallSource
