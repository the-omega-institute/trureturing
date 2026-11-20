import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet
import Reg.Support.SingleDependentReadout

/-! Source-bound audits for the adjacent swap and deletion lemmas. -/

namespace Reg.D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet

open _root_.D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Equiv

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev AdjacentPosition := (n : ℕ) × Fin (n + 1)

abbrev swap_signature : Signature :=
  Reg.Support.SingleDependentReadout.signature AdjacentPosition
    (fun q => Perm (Fin (q.1 + 2))) (fun q => Fin (q.1 + 2))

def swap_actual : Realization swap_signature :=
  realize swap_signature (fun _ q p => p q.2.castSucc) (fun e => nomatch e)

def swap_rejected : Realization swap_signature :=
  realize swap_signature (fun _ q _ => q.2.castSucc) (fun e => nomatch e)

abbrev swap_arena : Arena where
  signature := swap_signature
  Law R := ∀ {n : ℕ} (a : Fin (n + 1)) (S : Set (Fin (n + 2))),
    a.castSucc ∈ S → a.succ ∉ S → ∀ p : Perm (Fin (n + 2)),
    (HasExactExcedances p S ∧ R.readout () ⟨n, a⟩ p = a.succ) ↔
      (HasExactExcedances (swapPositions a.castSucc a.succ p) (S \ {a.castSucc}) ∧
        swapPositions a.castSucc a.succ p a.succ = a.succ)

private theorem swap_rejected_law : ¬ swap_arena.Law swap_rejected := by
  intro law
  let a : Fin (0 + 1) := 0
  let S : Set (Fin (0 + 2)) := {a.castSucc}
  let p := Equiv.swap a.castSucc a.succ
  have hl : a.castSucc ∈ S := by simp [S]
  have hr : a.succ ∉ S := by simpa [S] using a.castSucc_lt_succ.ne.symm
  have hsource : HasExactExcedances p S := by
    intro j
    fin_cases j <;> decide
  have hright := (exact_swap_fixed_iff a S hl hr p).mp ⟨hsource, Equiv.swap_apply_left ..⟩
  exact a.castSucc_lt_succ.ne ((law a S hl hr p).mpr hright).2

private theorem swap_dependence : ObservationalDependence swap_signature swap_actual := by
  intro role
  let a : Fin (0 + 1) := 0
  refine ⟨⟨0, a⟩, Equiv.refl _, Equiv.swap a.castSucc a.succ, ?_⟩
  change a.castSucc ≠ Equiv.swap a.castSucc a.succ a.castSucc
  rw [Equiv.swap_apply_left]
  exact a.castSucc_lt_succ.ne

def swap_source : Registration swap_arena (type_of% (@exact_swap_fixed_iff)) where
  actual := swap_actual
  bridge := Iff.rfl
  variation := ⟨@exact_swap_fixed_iff, swap_rejected, swap_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity swap_arena.Law
    swap_actual swap_rejected swap_rejected_law
  dependence := swap_dependence

def swap_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exact_swap_fixed_iff) (Realization swap_signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet.exact_swap_fixed_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet.swap_source
  realizationSource := none
  generated := false
  arena := .source ⟨swap_arena⟩
  objectArena := .source ⟨swap_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source swap_arena ⟨swap_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize swap_signature
    (fun _ q p => p q.2.castSucc) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev deletion_signature : Signature :=
  Reg.Support.SingleDependentReadout.signature AdjacentPosition
    (fun q => Set (Fin (q.1 + 2))) (fun q => Set (Fin (q.1 + 1)))

def deletion_actual : Realization deletion_signature :=
  realize deletion_signature (fun _ q S => q.2.succ.succAbove ⁻¹' (S \ {q.2.castSucc}))
    (fun e => nomatch e)

def deletion_rejected : Realization deletion_signature :=
  realize deletion_signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev deletion_arena : Arena where
  signature := deletion_signature
  Law R := ∀ {n : ℕ} (a : Fin (n + 1)) (S : Set (Fin (n + 2))), a.succ ∉ S →
    R.readout () ⟨n, a⟩ S = a.castSucc.succAbove ⁻¹' S

private theorem deletion_rejected_law : ¬ deletion_arena.Law deletion_rejected := by
  intro law
  let a : Fin (1 + 1) := 0
  let S : Set (Fin (1 + 2)) := {2}
  have hr : a.succ ∉ S := by
    simp only [S, Set.mem_singleton_iff]
    decide
  have h := law a S hr
  change (∅ : Set (Fin 2)) = a.castSucc.succAbove ⁻¹' S at h
  have hm : (1 : Fin 2) ∈ a.castSucc.succAbove ⁻¹' S := by
    change a.castSucc.succAbove (1 : Fin 2) ∈ S
    rw [Fin.succAbove_castSucc_of_le _ _ (by decide : a ≤ 1)]
    simp only [S, Set.mem_singleton_iff]
    decide
  rw [← h] at hm
  simp at hm

private theorem deletion_dependence :
    ObservationalDependence deletion_signature deletion_actual := by
  intro role
  let a : Fin (1 + 1) := 0
  let S : Set (Fin (1 + 2)) := {2}
  refine ⟨⟨1, a⟩, ∅, S, ?_⟩
  change a.succ.succAbove ⁻¹' (∅ \ {a.castSucc}) ≠ a.succ.succAbove ⁻¹' (S \ {a.castSucc})
  intro he
  have hm : (1 : Fin 2) ∈ a.succ.succAbove ⁻¹' (S \ {a.castSucc}) := by
    change a.succ.succAbove (1 : Fin 2) ∈ S \ {a.castSucc}
    rw [Fin.succAbove_succ_of_lt _ _ (by decide : a < 1)]
    simp only [S, Set.mem_sdiff, Set.mem_singleton_iff]
    decide
  rw [← he] at hm
  simp at hm

def deletion_source : Registration deletion_arena (type_of% (@delete_swap_set)) where
  actual := deletion_actual
  bridge := Iff.rfl
  variation := ⟨@delete_swap_set, deletion_rejected, deletion_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity deletion_arena.Law
    deletion_actual deletion_rejected deletion_rejected_law
  dependence := deletion_dependence

def deletion_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@delete_swap_set) (Realization deletion_signature) Unit Unit := {
  unitName :=
    `D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet.delete_swap_set.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet.deletion_source
  realizationSource := none
  generated := false
  arena := .source ⟨deletion_arena⟩
  objectArena := .source ⟨deletion_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deletion_arena ⟨deletion_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize deletion_signature
    (fun _ q S => q.2.succ.succAbove ⁻¹' (S \ {q.2.castSucc})) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.Permutation.AdjacentExcedanceSet
