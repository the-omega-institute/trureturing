import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.RealRootedPermutations.Realization
import D5.S3.Combinatorics.RealRootedPermutations.LogConcave
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

namespace Reg.D5.S3.Combinatorics.RealRootedPermutations.Realization
open _root_.D5.S3.Combinatorics.RealRootedPermutations
open _root_.D5.S3.Combinatorics.RealRootedPermutations.Realization
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
  Law R := ∀ {n : ℕ} (π : Equiv.Perm (Fin (n + 1))), IsUnimodal π →
    ∃ r : Fin (n + 1) → ℝ, (∀ i, 0 < r i) ∧
      StrictMono (fun t : Fin (n + 1) => coeffs r (((R.readout () n π) t : ℕ) + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hid : IsUnimodal (Equiv.refl (Fin 3)) := by
    constructor
    · intro i j hij _
      exact hij
    · intro i j hi hij
      change Fin.last 2 ≤ i at hi
      have hj := j.isLt
      change i.val < j.val at hij
      change 2 ≤ i.val at hi
      omega
  obtain ⟨r, hr, hs⟩ := @h 2 (Equiv.refl _) hid
  have hu := LogConcave.unimodal_of_arises (Equiv.swap (0 : Fin 3) 1)
    ⟨r, hr, hs.monotone⟩
  have ht := hu.1 0 1 (by decide) (by decide)
  norm_num [Equiv.swap_apply_def] at ht

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, Equiv.refl _, Equiv.swap (0 : Fin 2) 1, ?_⟩
  change Equiv.refl (Fin 2) ≠ Equiv.swap (0 : Fin 2) 1
  intro he
  have ht := congrArg (fun e : Equiv.Perm (Fin 2) => e 0) he
  norm_num [Equiv.swap_apply_def] at ht

def registration : Registration arena (type_of% @realize_strict) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨realize_strict, rejected, rejected_law⟩
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
    (@realize_strict) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.RealRootedPermutations.Realization.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.RealRootedPermutations.Realization.registration
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
    owner := `D5.S3.Combinatorics.RealRootedPermutations.Realization
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg", "body", "arg", "fn", "arg", "arg", "fn", "arg"]
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
end Reg.D5.S3.Combinatorics.RealRootedPermutations.Realization
