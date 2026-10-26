import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.RealRootedPermutations.LogConcave
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

namespace Reg.D5.S3.Combinatorics.RealRootedPermutations.LogConcave
open _root_.D5.S3.Combinatorics.RealRootedPermutations
open _root_.D5.S3.Combinatorics.RealRootedPermutations.LogConcave
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State n := Equiv.Perm (Fin (n + 1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Equiv.Perm (Fin (n + 1))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ π => π) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n _ => Equiv.swap 0 (1 : Fin (n + 1))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (π : Equiv.Perm (Fin (n + 1))), Arises π →
    IsUnimodal (R.readout () n π)

private theorem reverse_three_arises : Arises (Equiv.swap (0 : Fin 3) 2) := by
  refine ⟨fun _ => 1, fun _ => zero_lt_one, ?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b <;> norm_num at hab <;>
    norm_num [_root_.D5.S3.Combinatorics.RealRootedPermutations.coeffs, Fin.prod_const, Polynomial.coeff_one_add_X_pow,
      Equiv.swap_apply_def]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := @h 2 (Equiv.swap (0 : Fin 3) 2) reverse_three_arises
  change IsUnimodal (Equiv.swap (0 : Fin 3) 1) at hx
  have ht := hx.1 0 1 (by decide) (by decide)
  norm_num [Equiv.swap_apply_def] at ht

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, Equiv.refl _, Equiv.swap (0 : Fin 2) 1, ?_⟩
  change Equiv.refl (Fin 2) ≠ Equiv.swap (0 : Fin 2) 1
  intro he
  have ht := congrArg (fun e : Equiv.Perm (Fin 2) => e 0) he
  norm_num [Equiv.swap_apply_def] at ht

def registration : Registration arena (type_of% @unimodal_of_arises) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unimodal_of_arises, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@unimodal_of_arises) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.RealRootedPermutations.LogConcave.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.RealRootedPermutations.LogConcave.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ π => π) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.RealRootedPermutations.LogConcave
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit
end
end Reg.D5.S3.Combinatorics.RealRootedPermutations.LogConcave
