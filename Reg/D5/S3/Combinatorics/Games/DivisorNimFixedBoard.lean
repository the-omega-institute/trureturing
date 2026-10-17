import Reg.D5.S3.Combinatorics.Games.DivisorNimGcdTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Games.DivisorNimFixedBoard

open _root_.D5.S3.Combinatorics.Games.DivisorNimGrundy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := Reg.D5.S3.Combinatorics.Games.DivisorNimGcdTwo.signature

noncomputable def actual : Realization signature :=
  realize signature (fun _ A n => fixedSequence A n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A : Position}, Positive A → A ≠ 0 →
    ∃ T, 0 < T ∧ ∃ N, ∀ n, N ≤ n →
      R.readout () A (n + T) = R.readout () A n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : Positive ({2} : Position) := by
    intro x hx
    have : x = 2 := by simpa using hx
    omega
  obtain ⟨T, hT, N, hN⟩ := h hp (by simp)
  have he := hN N le_rfl
  change N + T = N at he
  exact (Nat.ne_of_gt hT) (Nat.add_left_cancel he)

private theorem actual_family_dependence {A : Position} (hp : Positive A)
    (ha : A ≠ 0) : ∃ n m, fixedSequence A n ≠ fixedSequence A m := by
  obtain ⟨k, hk⟩ := exists_depth ha
  let p := 2 ^ (k + 1)
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hp2 : 2 ≤ p := by
    change 2 ^ 1 ≤ 2 ^ (k + 1)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hchar : ∀ n, 0 < n → (fixedSequence A n = 0 ↔
      n % p = if Even (countAt A k) then 0 else 2 ^ k) := by
    intro n hn
    simpa [fixedSequence, adjoinHeap, Nat.ne_of_gt hn, p] using fixed_zero_residue hp hk hn
  by_cases he : Even (countAt A k)
  · have hz : fixedSequence A p = 0 := (hchar p hp0).mpr (by simp [he])
    refine ⟨p, p + 1, ?_⟩
    rw [hz]
    intro h
    have hm := (hchar (p + 1) (by omega)).mp h.symm
    simp [he, Nat.add_mod, Nat.mod_eq_of_lt (show 1 < p by omega)] at hm
  · have hpow : 0 < 2 ^ k := by positivity
    have hlt : 2 ^ k < p := by dsimp [p]; rw [pow_succ]; omega
    have hz : fixedSequence A (p + 2 ^ k) = 0 :=
      (hchar _ (by omega)).mpr (by simp [he, Nat.add_mod, Nat.mod_eq_of_lt hlt])
    refine ⟨p, p + 2 ^ k, ?_⟩
    rw [hz]
    intro h
    have hm := (hchar p hp0).mp h
    simp only [Nat.mod_self, if_neg he] at hm
    exact (Nat.ne_of_gt hpow) hm.symm

noncomputable def registration :
    Registration arena (type_of% (@fixed_board_eventually_periodic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_board_eventually_periodic, rejected, rejected_law⟩
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
      (@fixed_board_eventually_periodic)
      (type_of% (realize signature (fun _ A n => fixedSequence A n)
        (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Games.DivisorNimFixedBoard.informationUnit
  realizationName := `Reg.D5.S3.Combinatorics.Games.DivisorNimFixedBoard.registration
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
    owner := `D5.S3.Combinatorics.Games.DivisorNimFixedBoard
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg", "body",
        "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Games.DivisorNimFixedBoard
