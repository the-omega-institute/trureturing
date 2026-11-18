import Reg.D5.S3.Combinatorics.Permutation.Verkama62Count

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Permutation.Verkama62Charge
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.Verkama62Local
open _root_.D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)
open Reg.D5.S3.Combinatorics.Permutation.Verkama62Result (rev3 run3)
open Reg.D5.S3.Combinatorics.Permutation.Verkama62Count

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)},
    EarRun π S → ¬ Contains pattern π → 7 * S.card ≤ 4 * R.readout () ⟨n,π⟩ S + 12
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha : ¬ Contains pattern rev3 := by
    rintro ⟨f, hf⟩
    have := Fintype.card_le_of_injective f f.injective
    norm_num at this
  have he := @h 3 rev3 Finset.univ run3 ha
  change 7 * (Finset.univ : Finset (Fin 3)).card ≤ 4 * 0 + 12 at he
  norm_num at he

def family : Registration arena (type_of% (@ear_run_bound)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ear_run_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := observation_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@ear_run_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.ear_run_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62Charge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p S => inversions p.2 S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62Charge
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Permutation.Verkama62Charge
