import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds
import Reg.Support.SingleDependentReadout
import Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts

/-! Source-bound readouts for the original coefficient proof. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs
open Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts
open PowerSeries Finset

namespace Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds

private noncomputable def upper (n : ℕ) : ℝ :=
  ∑ a ∈ range (⌊Real.sqrt (2 * (n : ℝ) + 1 / 2) + 1 / 2⌋₊),
    (Real.sqrt ((Real.sqrt (2 * (n : ℝ) + 1 / 2)) ^ 2 -
      ((a : ℝ) + 1 / 2) ^ 2) / 2 + 3 / 4)
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  ℕ (fun _ => Finset (ℕ × ℕ)) (fun _ => ℝ)
noncomputable def actual : Realization signature :=
  realize signature (fun _ _ s => (s.card : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (s : Finset (ℕ × ℕ)),
    (∀ p ∈ s, (p.1+1).choose 2+(p.2+1).choose 2 ≤ n ∧
      ((p.1+1).choose 2+(p.2+1).choose 2)%2=n%2) →
    r.readout () n s ≤ upper n
noncomputable def bad : Realization signature :=
  realize signature (fun _ n _ => upper n+1) (fun e => nomatch e)
theorem bad_not_law : ¬ arena.Law bad := by
  intro h
  have hx := h 0 ∅ (by simp)
  change upper 0+1 ≤ upper 0 at hx
  linarith
noncomputable def registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds.gauss_pair_count_le_sqrt_sum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds.gauss_pair_count_le_sqrt_sum,
    bad, bad_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_not_law
  dependence := by
    intro i
    refine ⟨0, ∅, {(0,0)}, ?_⟩
    change ((∅ : Finset (ℕ × ℕ)).card : ℝ) ≠
      (({(0,0)} : Finset (ℕ × ℕ)).card : ℝ)
    simp only [card_empty, card_singleton, Nat.cast_zero, Nat.cast_one, ne_eq, zero_ne_one, not_false_eq_true]

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds.gauss_pair_count_le_sqrt_sum)
    (type_of% (realize signature (fun _ _ s => (s.card : ℝ)) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds.gauss_pair_count_le_sqrt_sum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => (s.card : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds
