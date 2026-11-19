import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Permutation.Verkama62Result

/-! Source-bound inversion observations for the exact rational lower bound. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Permutation.Verkama62Result

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.Verkama62Local
open _root_.D5.S3.Combinatorics.IndecomposableInversion

def rev3 : Equiv.Perm (Fin 3) where
  toFun := ![2,1,0]
  invFun := ![2,1,0]
  left_inv := by decide
  right_inv := by decide

theorem rev3_avoid : ¬ ContainsOneBased rev3 := by
  rintro ⟨f, hf⟩
  have := Fintype.card_le_of_injective f f.injective
  norm_num at this

theorem rev3_adj (a b : Fin 3) (hab : a ≠ b) :
    (valueGraph rev3).Adj a b := by
  fin_cases a <;> fin_cases b <;> norm_num [valueGraph, rev3] at *

theorem rev3_connected : (valueGraph rev3).Connected := by
  refine ⟨?_⟩
  intro a b
  by_cases h : a = b
  · subst b; exact .refl _
  · exact (rev3_adj a b h).reachable

theorem rev3_deleted (v : Fin 3) : ((valueGraph rev3).induce {v}ᶜ).Connected := by
  haveI : Nonempty {w : Fin 3 // w ∈ ({v}ᶜ : Set (Fin 3))} := by
    fin_cases v
    · exact ⟨⟨1, by decide⟩⟩
    · exact ⟨⟨0, by decide⟩⟩
    · exact ⟨⟨0, by decide⟩⟩
  refine ⟨?_⟩
  intro a b
  by_cases h : a = b
  · subst b; exact .refl _
  · exact SimpleGraph.Adj.reachable (rev3_adj a.val b.val (by
      intro he; exact h (Subtype.ext he)))

abbrev signature : Signature where
  Params := ℕ
  State n := Equiv.Perm (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ π => FranklinInversionDefs.inv (PSW.word π))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (π : Equiv.Perm (Fin n)), 3 ≤ n →
    ¬ ContainsOneBased π → (valueGraph π).Connected →
    (∀ v, ((valueGraph π).induce {v}ᶜ).Connected) →
      (7 / 4 : ℚ) * n - 3 ≤ ((R.readout () n π : ℕ) : ℚ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := @h 3 rev3 (by omega) rev3_avoid rev3_connected rev3_deleted
  change (7 / 4 : ℚ) * 3 - 3 ≤ 0 at he
  norm_num at he

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨3, Equiv.refl _, rev3, ?_⟩
    change FranklinInversionDefs.inv (PSW.word (Equiv.refl (Fin 3))) ≠
      FranklinInversionDefs.inv (PSW.word rev3)
    decide

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@result) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Result.family
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
    (fun _ _ π => FranklinInversionDefs.inv (PSW.word π)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

theorem run3 : EarRun rev3 Finset.univ := complete_run rev3 (by omega) rev3_connected rev3_deleted

theorem no_run_id {n : ℕ} {S : Finset (Fin n)} : ¬ EarRun (Equiv.refl _) S := by
  have has_edge {π : Equiv.Perm (Fin n)} {T : Finset (Fin n)} (h : EarRun π T) :
      ∃ a b, a < b ∧ π b < π a := by
    induction h with
    | triangle a b c hab hbc hba hcb => exact ⟨a,b,hab,hba⟩
    | square a b c d hab hbc hcd hcv hda hav => exact ⟨a,c,hab.trans hbc,hcv.trans hda⟩
    | singleton run x hx hd ih => exact ih
    | double run e ih => exact ih
  intro h
  obtain ⟨a,b,hab,hba⟩ := has_edge h
  exact (not_lt_of_ge hab.le) hba

theorem run_nonempty {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)}
    (h : EarRun π S) : S.Nonempty := by
  induction h with
  | triangle a b c hab hbc hba hcb => exact ⟨a, by simp⟩
  | square a b c d hab hbc hcd hcv hda hav => exact ⟨a, by simp⟩
  | singleton run x hx hd ih => exact ⟨x, by simp⟩
  | double run e ih => exact ⟨e.u, by simp⟩

namespace Complete

abbrev signature : Signature where
  Params := ℕ
  State n := Equiv.Perm (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ π => EarRun π Finset.univ)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (π : Equiv.Perm (Fin n)), 3 ≤ n → (valueGraph π).Connected →
    (∀ v, ((valueGraph π).induce {v}ᶜ).Connected) → R.readout () n π
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact @h 3 rev3 (by omega) rev3_connected rev3_deleted

def family : Registration arena (type_of% (@complete_run)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complete_run, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨3, rev3, Equiv.refl _, ?_⟩
    intro h
    exact no_run_id (Eq.mp h run3)

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@complete_run) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.complete_run.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Result.Complete.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ π => EarRun π Finset.univ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Result
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Complete

end Reg.D5.S3.Combinatorics.Permutation.Verkama62Result
