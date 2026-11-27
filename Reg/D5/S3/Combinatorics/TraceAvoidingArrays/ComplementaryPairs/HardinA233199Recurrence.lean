import D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233199Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The exact literal recurrence as a dependent-family observation law. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233199Recurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233199Recurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n : ℤ) + if n = 12 then 1 else 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (_ : 12 ≤ n),
    R.readout () () n = 736 * R.readout () () (n - 1) - 203776 * R.readout () () (n - 2)
      + 33062912 * R.readout () () (n - 3) - 3665821696 * R.readout () () (n - 4)
      + 270851375104 * R.readout () () (n - 5) - 10685878632448 * R.readout () () (n - 6)
      - 116548232544256 * R.readout () () (n - 7) + 35184372088832000 * R.readout () () (n - 8)
      - 1423137482249076736 * R.readout () () (n - 9)
      + 18446744073709551616 * R.readout () () (n - 10)

attribute [local irreducible] a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := result 12 (by decide)
  have hb := h 12 (by decide)
  dsimp only [rejected, realize] at hb
  norm_num only [Nat.reduceSub, Nat.reduceEqDiff, ite_true, ite_false, add_zero] at ha hb
  linarith

private theorem positive_two : 0 < a 2 := by
  unfold a
  apply Finset.card_pos.mpr
  let f : Fin 2 × Fin 5 → Fin 8 :=
    fun p => if p.1 = 0 then ![0, 1, 2, 0, 1] p.2 else ![2, 0, 1, 2, 0] p.2
  refine ⟨f, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  subst f
  decide +kernel

private theorem dependence_at_positive_heights :
    ∃ m : ℕ, 2 ≤ m ∧ (a m : ℤ) ≠ a 2 := by
  by_contra! h
  have hrec := result 12 (by decide)
  norm_num only [Nat.reduceSub] at hrec
  rw [h 12 (by decide), h 11 (by decide), h 10 (by decide), h 9 (by decide),
    h 8 (by decide), h 7 (by decide), h 6 (by decide), h 5 (by decide),
    h 4 (by decide), h 3 (by decide)] at hrec
  have hp : (0 : ℤ) < a 2 := by exact_mod_cast positive_two
  linarith

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    obtain ⟨m, _, hm⟩ := dependence_at_positive_heights
    exact ⟨(), m, 2, hm⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233199Recurrence.unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (a n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233199Recurrence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233199Recurrence
