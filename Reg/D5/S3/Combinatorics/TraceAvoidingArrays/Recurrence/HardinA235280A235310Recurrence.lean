import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence
import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Tactic.FinCases

/-! Source-bound readouts for the literal rectangle recurrences of orders 9, 14, and 18. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Alphabet
  (C Grid Low count_eq)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℤ)

private def lowDecidable (d n k : ℕ) (a : Grid d n k) : Decidable (Low d a) := by
  unfold Low
  infer_instance

private def lowCard (d n k : ℕ) : ℕ :=
  letI : DecidablePred (Low (M := d) (n := n) (k := k) d) := lowDecidable d n k
  (Finset.univ.filter (Low (M := d) (n := n) (k := k) d)).card

private theorem count_eq_twice_lowCard (M d n k : ℕ) (hd : d < M) :
    C M (2 * M - d) (n + 1) (k + 1) = 2 * lowCard d (n + 1) (k + 1) := by
  let _ : DecidablePred (Low (M := d) (n := n + 1) (k := k + 1) d) :=
    lowDecidable d (n + 1) (k + 1)
  unfold lowCard
  rw [count_eq M d (n + 1) (k + 1) hd (Nat.succ_pos _) (Nat.succ_pos _),
    Nat.card_eq_fintype_card, Fintype.card_subtype]

namespace A235280

private def actual : Realization signature :=
  realize signature (fun _ n k => (C 4 5 n k : ℤ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ n k =>
    if n = 10 ∧ k = 1 then (C 4 5 n k : ℤ) + 1 else (C 4 5 n k : ℤ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), 0 < n → 0 < k →
    (R.readout () (n + 9) k =
      R.readout () (n + 8) k + 15 * R.readout () (n + 7) k - 15 * R.readout () (n + 6) k
       - 80 * R.readout () (n + 5) k + 80 * R.readout () (n + 4) k + 180 * R.readout () (n + 3) k
       - 180 * R.readout () (n + 2) k - 144 * R.readout () (n + 1) k + 144 * R.readout () n k) ∧
    (R.readout () n (k + 9) =
      R.readout () n (k + 8) + 15 * R.readout () n (k + 7) - 15 * R.readout () n (k + 6)
       - 80 * R.readout () n (k + 5) + 80 * R.readout () n (k + 4) + 180 * R.readout () n (k + 3)
       - 180 * R.readout () n (k + 2) - 144 * R.readout () n (k + 1) + 144 * R.readout () n k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 1 1 (by decide) (by decide)).1
  have good := (a235280_all_rows_and_columns 1 1 (by decide) (by decide)).1
  change (C 4 5 10 1 : ℤ) + 1 =
      (C 4 5 9 1 : ℤ) + 15 * (C 4 5 8 1 : ℤ) - 15 * (C 4 5 7 1 : ℤ)
       - 80 * (C 4 5 6 1 : ℤ) + 80 * (C 4 5 5 1 : ℤ) + 180 * (C 4 5 4 1 : ℤ)
       - 180 * (C 4 5 3 1 : ℤ) - 144 * (C 4 5 2 1 : ℤ) + 144 * (C 4 5 1 1 : ℤ) at bad
  change (C 4 5 10 1 : ℤ) =
      (C 4 5 9 1 : ℤ) + 15 * (C 4 5 8 1 : ℤ) - 15 * (C 4 5 7 1 : ℤ)
       - 80 * (C 4 5 6 1 : ℤ) + 80 * (C 4 5 5 1 : ℤ) + 180 * (C 4 5 4 1 : ℤ)
       - 180 * (C 4 5 3 1 : ℤ) - 144 * (C 4 5 2 1 : ℤ) + 144 * (C 4 5 1 1 : ℤ) at good
  omega

set_option maxRecDepth 64000 in
set_option maxHeartbeats 5000000 in
private theorem small_counts : C 4 5 1 1 = 40 ∧ C 4 5 1 2 = 100 := by
  rw [count_eq_twice_lowCard 4 3 0 0 (by decide),
    count_eq_twice_lowCard 4 3 0 1 (by decide)]
  decide +kernel

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  change (C 4 5 1 1 : ℤ) ≠ (C 4 5 1 2 : ℤ)
  rw [small_counts.1, small_counts.2]
  decide

def family : Registration arena (type_of% @a235280_all_rows_and_columns) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨a235280_all_rows_and_columns, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@a235280_all_rows_and_columns) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence.A235280.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence.A235280.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => (C 4 5 n k : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end A235280

namespace A235310

private def actual : Realization signature :=
  realize signature (fun _ n k => (C 5 6 n k : ℤ)) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ n k =>
    if n = 15 ∧ k = 1 then (C 5 6 n k : ℤ) + 1 else (C 5 6 n k : ℤ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), 0 < n → 0 < k →
    (R.readout () (n + 14) k =
      4 * R.readout () (n + 13) k + 25 * R.readout () (n + 12) k - 112 * R.readout () (n + 11) k
       - 231 * R.readout () (n + 10) k + 1260 * R.readout () (n + 9) k + 875 * R.readout () (n + 8) k
       - 7280 * R.readout () (n + 7) k - 224 * R.readout () (n + 6) k + 22736 * R.readout () (n + 5) k
       - 7980 * R.readout () (n + 4) k - 36288 * R.readout () (n + 3) k + 21456 * R.readout () (n + 2) k
       + 23040 * R.readout () (n + 1) k - 17280 * R.readout () n k) ∧
    (R.readout () n (k + 14) =
      4 * R.readout () n (k + 13) + 25 * R.readout () n (k + 12) - 112 * R.readout () n (k + 11)
       - 231 * R.readout () n (k + 10) + 1260 * R.readout () n (k + 9) + 875 * R.readout () n (k + 8)
       - 7280 * R.readout () n (k + 7) - 224 * R.readout () n (k + 6) + 22736 * R.readout () n (k + 5)
       - 7980 * R.readout () n (k + 4) - 36288 * R.readout () n (k + 3) + 21456 * R.readout () n (k + 2)
       + 23040 * R.readout () n (k + 1) - 17280 * R.readout () n k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 1 1 (by decide) (by decide)).1
  have good := (a235310_all_rows_and_columns 1 1 (by decide) (by decide)).1
  change (C 5 6 15 1 : ℤ) + 1 =
      4 * (C 5 6 14 1 : ℤ) + 25 * (C 5 6 13 1 : ℤ) - 112 * (C 5 6 12 1 : ℤ)
       - 231 * (C 5 6 11 1 : ℤ) + 1260 * (C 5 6 10 1 : ℤ) + 875 * (C 5 6 9 1 : ℤ)
       - 7280 * (C 5 6 8 1 : ℤ) - 224 * (C 5 6 7 1 : ℤ) + 22736 * (C 5 6 6 1 : ℤ)
       - 7980 * (C 5 6 5 1 : ℤ) - 36288 * (C 5 6 4 1 : ℤ) + 21456 * (C 5 6 3 1 : ℤ)
       + 23040 * (C 5 6 2 1 : ℤ) - 17280 * (C 5 6 1 1 : ℤ) at bad
  change (C 5 6 15 1 : ℤ) =
      4 * (C 5 6 14 1 : ℤ) + 25 * (C 5 6 13 1 : ℤ) - 112 * (C 5 6 12 1 : ℤ)
       - 231 * (C 5 6 11 1 : ℤ) + 1260 * (C 5 6 10 1 : ℤ) + 875 * (C 5 6 9 1 : ℤ)
       - 7280 * (C 5 6 8 1 : ℤ) - 224 * (C 5 6 7 1 : ℤ) + 22736 * (C 5 6 6 1 : ℤ)
       - 7980 * (C 5 6 5 1 : ℤ) - 36288 * (C 5 6 4 1 : ℤ) + 21456 * (C 5 6 3 1 : ℤ)
       + 23040 * (C 5 6 2 1 : ℤ) - 17280 * (C 5 6 1 1 : ℤ) at good
  omega

set_option maxRecDepth 64000 in
set_option maxHeartbeats 5000000 in
private theorem small_counts : C 5 6 1 1 = 70 ∧ C 5 6 1 2 = 210 := by
  rw [count_eq_twice_lowCard 5 4 0 0 (by decide),
    count_eq_twice_lowCard 5 4 0 1 (by decide)]
  decide +kernel

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  change (C 5 6 1 1 : ℤ) ≠ (C 5 6 1 2 : ℤ)
  rw [small_counts.1, small_counts.2]
  decide

def family : Registration arena (type_of% @a235310_all_rows_and_columns) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨a235310_all_rows_and_columns, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@a235310_all_rows_and_columns) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence.A235310.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence.A235310.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => (C 5 6 n k : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end A235310

namespace A235319

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ n k => (C 6 7 n k : ℤ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n k =>
    if n = 19 ∧ k = 1 then (C 6 7 n k : ℤ) + 1 else (C 6 7 n k : ℤ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), 0 < n → 0 < k →
    let count := fun (n k : ℕ) => R.readout () n k
    (count (n + 18) k =
      4 * count (n + 17) k + 47 * count (n + 16) k - 200 * count (n + 15) k
      - 901 * count (n + 14) k + 4204 * count (n + 13) k + 8957 * count (n + 12) k
      - 48440 * count (n + 11) k - 47194 * count (n + 10) k + 334096 * count (n + 9) k
      + 101948 * count (n + 8) k - 1410080 * count (n + 7) k + 170136 * count (n + 6) k
      + 3549696 * count (n + 5) k - 1446912 * count (n + 4) k - 4861440 * count (n + 3) k
      + 2954880 * count (n + 2) k + 2764800 * count (n + 1) k - 2073600 * count n k) ∧
    (count n (k + 18) =
      4 * count n (k + 17) + 47 * count n (k + 16) - 200 * count n (k + 15)
      - 901 * count n (k + 14) + 4204 * count n (k + 13) + 8957 * count n (k + 12)
      - 48440 * count n (k + 11) - 47194 * count n (k + 10) + 334096 * count n (k + 9)
      + 101948 * count n (k + 8) - 1410080 * count n (k + 7) + 170136 * count n (k + 6)
      + 3549696 * count n (k + 5) - 1446912 * count n (k + 4) - 4861440 * count n (k + 3)
      + 2954880 * count n (k + 2) + 2764800 * count n (k + 1) - 2073600 * count n k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 1 1 (by decide) (by decide)).1
  have good := (a235319_all_rows_and_columns 1 1 (by decide) (by decide)).1
  dsimp [rejected, realize] at bad
  norm_num at bad good
  omega

private def Literal (n k : ℕ) (a : Fin (n + 1) → Fin (k + 1) → Fin 7) : Prop :=
  ∀ (i : Fin n) (j : Fin k),
    Int.natAbs (((a i.castSucc j.castSucc).val : ℤ) + ((a i.succ j.succ).val : ℤ) -
      (((a i.succ j.castSucc).val : ℤ) + ((a i.castSucc j.succ).val : ℤ))) = 7

private theorem count_eq_literal_card (n k : ℕ) :
    C 6 7 n k = Nat.card {a // Literal n k a} := by
  unfold C
  exact Nat.card_congr {
    toFun := fun a => ⟨fun i j => a.1 (i, j), fun i j => by
      simpa only [add_comm] using a.2 i j⟩
    invFun := fun a => ⟨fun (i, j) => a.1 i j, fun i j => by
      simpa only [add_comm] using a.2 i j⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private abbrev LegalGrid (k : ℕ) :=
  {a : Fin 2 → Fin (k + 1) → Fin 7 // Literal 1 k a}

/-- Repeating the first column extends a legal two-column grid. -/
private def repeatColumn (a : LegalGrid 1) : LegalGrid 2 :=
  ⟨fun i => ![a.1 i 0, a.1 i 1, a.1 i 0], by
    unfold Literal
    rw [Fin.forall_fin_one, Fin.forall_fin_two]
    refine ⟨a.2 0 0, ?_⟩
    have h := a.2 0 0
    change (((a.1 0 0).val : ℤ) + (a.1 1 1).val -
      ((a.1 1 0).val + (a.1 0 1).val)).natAbs = 7 at h
    change (((a.1 0 1).val : ℤ) + (a.1 1 0).val -
      ((a.1 1 1).val + (a.1 0 0).val)).natAbs = 7
    rw [show ((a.1 0 1).val : ℤ) + (a.1 1 0).val - ((a.1 1 1).val + (a.1 0 0).val) =
      -((a.1 0 0).val + (a.1 1 1).val - ((a.1 1 0).val + (a.1 0 1).val)) by ring,
      Int.natAbs_neg]
    exact h⟩

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 1, 2, ?_⟩
  change (C 6 7 1 1 : ℤ) ≠ (C 6 7 1 2 : ℤ)
  classical
  rw [count_eq_literal_card, count_eq_literal_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  simp only [ne_eq, Nat.cast_inj]
  apply Nat.ne_of_lt
  let extra : LegalGrid 2 := ⟨![![0, 6, 1], ![1, 0, 2]], by unfold Literal; decide⟩
  apply Fintype.card_lt_of_injective_of_notMem repeatColumn (b := extra)
  · intro a b h
    apply Subtype.ext
    funext i j
    fin_cases j
    · exact congrArg (fun grid : LegalGrid 2 => grid.1 i 0) h
    · exact congrArg (fun grid : LegalGrid 2 => grid.1 i 1) h
  · rintro ⟨a, ha⟩
    have first : a.1 0 0 = (0 : Fin 7) :=
      congrArg (fun grid : LegalGrid 2 => grid.1 0 0) ha
    have last : a.1 0 0 = (1 : Fin 7) :=
      congrArg (fun grid : LegalGrid 2 => grid.1 0 2) ha
    exact (by decide : (0 : Fin 7) ≠ 1) (first.symm.trans last)

def family : Registration arena (type_of% @a235319_all_rows_and_columns) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨a235319_all_rows_and_columns, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@a235319_all_rows_and_columns) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence.A235319.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence.A235319.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => (C 6 7 n k : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end A235319

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235280A235310Recurrence
