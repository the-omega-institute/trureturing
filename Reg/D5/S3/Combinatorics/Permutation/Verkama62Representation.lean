import Reg.D5.S3.Combinatorics.Permutation.Verkama62Result

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Permutation.Verkama62Representation
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.Verkama62Local
open _root_.D5.S3.Combinatorics.IndecomposableInversion
open Reg.D5.S3.Combinatorics.Permutation.Verkama62Result

namespace Word
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (π : Equiv.Perm (Fin n)), R.readout () n π = inversions π Finset.univ
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := @h 3 rev3
  change 0 = inversions rev3 Finset.univ at he
  have hi : inversions rev3 Finset.univ = 3 := by decide
  omega
def family : Registration arena (type_of% (@word_inversions)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_inversions, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := Reg.D5.S3.Combinatorics.Permutation.Verkama62Result.family.dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@word_inversions) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.word_inversions.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Representation.Word.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ π => FranklinInversionDefs.inv (PSW.word π)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Representation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Word

namespace Bound
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (π : Equiv.Perm (Fin n)), ¬ ContainsOneBased π → EarRun π Finset.univ → (7 / 4 : ℚ) * n - 3 ≤ ((R.readout () n π : ℕ) : ℚ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := @h 3 rev3 rev3_avoid run3
  change (7 / 4 : ℚ) * 3 - 3 ≤ 0 at he
  norm_num at he
def family : Registration arena (type_of% (@rational_bound_of_ear_run)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_bound_of_ear_run, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := Reg.D5.S3.Combinatorics.Permutation.Verkama62Result.family.dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@rational_bound_of_ear_run) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.rational_bound_of_ear_run.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Representation.Bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ π => FranklinInversionDefs.inv (PSW.word π)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Representation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Bound
end Reg.D5.S3.Combinatorics.Permutation.Verkama62Representation
