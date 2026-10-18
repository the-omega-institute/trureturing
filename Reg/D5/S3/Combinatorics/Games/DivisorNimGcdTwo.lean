import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Games.DivisorNimGcdTwo
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Games.DivisorNimGcdTwo

open _root_.D5.S3.Combinatorics.Games.DivisorNimGrundy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Position
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ A n => fixedSequence A n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A : Position}, Positive A → 2 ≤ A.card → A.gcd = 2 →
    (∃ N, ∀ n, N ≤ n →
      R.readout () A (n + comparisonSpacing A) = R.readout () A n) ∧
    leastTailPeriod A ∣ comparisonSpacing A ∧
    leastTailPeriod A / Nat.gcd (leastTailPeriod A) (comparisonSpacing A) = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : Positive ({2, 2} : Position) := by
    intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> decide
  have hc : 2 ≤ ({2, 2} : Position).card := by simp
  have hg : ({2, 2} : Position).gcd = 2 := by simp
  obtain ⟨N, hN⟩ := (h hp hc hg).1
  have he := hN N le_rfl
  change N + comparisonSpacing ({2, 2} : Position) = N at he
  have hpos := (comparison_spacing_signal hp (by simp)).1
  exact (Nat.ne_of_gt hpos) (Nat.add_left_cancel he)

private theorem actual_family_dependence {A : Position} (hp : Positive A)
    (hg : A.gcd = 2) : ∃ n m, fixedSequence A n ≠ fixedSequence A m := by
  have hr : sixZeroPhase A = 0 ∨ sixZeroPhase A = 2 := by
    unfold sixZeroPhase
    split_ifs <;> simp
  have hz : fixedSequence A (4 + sixZeroPhase A) = 0 :=
    (gcd_two_zero_pattern hp hg _).mpr (by rcases hr with hr | hr <;> rw [hr])
  refine ⟨1, 4 + sixZeroPhase A, ?_⟩
  rw [hz]
  intro h
  have he := (gcd_two_zero_pattern hp hg 1).mp h
  rcases hr with hr | hr <;> rw [hr] at he <;> norm_num at he

noncomputable def registration : Registration arena (type_of% (@gcd_two_spacing)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gcd_two_spacing, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    have hp : Positive ({2, 2} : Position) := by
      intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> decide
    obtain ⟨n, m, hnm⟩ := actual_family_dependence hp (by simp)
    exact ⟨{2, 2}, n, m, hnm⟩

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@gcd_two_spacing)
      (type_of% (realize signature (fun _ A n => fixedSequence A n)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Games.DivisorNimGcdTwo.informationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Games.DivisorNimGcdTwo.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ A n => fixedSequence A n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Games.DivisorNimGcdTwo
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "body",
        "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Games.DivisorNimGcdTwo
