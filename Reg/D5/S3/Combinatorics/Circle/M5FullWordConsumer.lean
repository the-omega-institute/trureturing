import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.M5FullWordConsumer
import Reg.Support.DependentFamily

/-! # Source-bound registration for the complete original M5 implication -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Circle.M5FullWordConsumer

open _root_.D5.S3.Combinatorics.Circle.M5FullWordConsumer
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open Fin.NatCast

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State p := Fin p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p => actualSource p.1 p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k t L : ℕ} {a b : ℤ} {p d x : Fin k},
    OriginalM5 k t L a b p d x →
    let s := R.readout () ⟨k, t⟩
    ∃ word : List (Fin k), word.Perm (List.finRange k) ∧
      word.head? = some x ∧ (word.map s).sum = 0 ∧
      ∀ j : ℕ, 0 ≤ ((word.take j).map s).sum ∧
        ((word.take j).map s).sum ≤ halfCapacity k

private theorem source_offset_eq {k : ℕ} (t : ℕ) (x : Fin k) (i : ℕ) :
    sourceOffset t x i =
      if hi : i < (largeOffsets t x).card then
        ((largeOffsets t x).sort[i]'(by simpa using hi)).val
      else k := by
  simp only [sourceOffset, cut, Finset.orderEmbOfFin_apply, Fin.getElem_fin]

private theorem lower_control : OriginalM5 21 1864540 2 203877 236263 15 2 20 := by
  have hs : actualSource 21 1864540 = (![-232611,-465222,-930444,236263,472526,945052,-207047,-414094,-828188,440775,881550,-334051,-668102,760947,-575257,946637,-203877,-407754,-815508,466135,932270] : Fin 21 → ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  have hl : largeOffsets 1864540 (20 : Fin 21) = ({0,3,6,9,11,13,14,15,16,19} : Finset (Fin 21)) := by
    unfold largeOffsets
    rw [hs]
    decide +kernel
  have hcard : ({0,3,6,9,11,13,14,15,16,19} : Finset (Fin 21)).card = 10 := by decide +kernel
  have hsort : ({0,3,6,9,11,13,14,15,16,19} : Finset (Fin 21)).sort = [0,3,6,9,11,13,14,15,16,19] := by
    refine (Finset.sortedLT_sort _).eq_of_mem_iff ?_ ?_
    · norm_num [List.sortedLT_iff_pairwise]
    · intro i; simp
  refine {
    nonzero := ?_, a_positive := ?_, minimum_inequalities := ?_,
    negative_minimum := ?_, positive_minimum := ?_,
    negative_attained := ?_, positive_attained := ?_,
    p_maximum := ?_, d_minimum := ?_, five_positive := ?_, five_negative := ?_,
    x_positive_large := ?_, incoming_d := ?_,
    p_row := {proper := ?_, parent_large := ?_, small := ?_, terminal_large := ?_},
    x_row_length := ?_, d_row_length := ?_, beta_row_length := ?_,
    gamma_row_short := ?_, c0_hard := ?_, beta_alternative := ?_,
    delta_positive := ?_, delta_hard := ?_, b1_hard := ?_, w_bounds := ?_,
    w_hard := ?_, w_row_length := ?_, nonET := ?_, u_above_z := ?_,
    power_branch := ?_, a0_bound := ?_ }
  all_goals
    (try simp [sourceSeed, sourceLength, sourceParent, source_offset_eq, hl, hcard, hsort, hs]) <;>
      exact of_decide_eq_true rfl

private theorem half_control : OriginalM5 22 3729116 2 407753 472807 16 2 21 := by
  have hs : actualSource 22 3729116 = (![-465187,-930374,-1860748,472807,945614,1891228,-411847,-823694,-1647388,899527,1799054,-596195,-1192390,1809523,-575257,-1150514,1893275,-407753,-815506,-1631012,932279,1864558] : Fin 22 → ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  have hl : largeOffsets 3729116 (21 : Fin 22) = ({0,3,6,9,11,13,14,16,17,20} : Finset (Fin 22)) := by
    unfold largeOffsets
    rw [hs]
    decide +kernel
  have hcard : ({0,3,6,9,11,13,14,16,17,20} : Finset (Fin 22)).card = 10 := by decide +kernel
  have hsort : ({0,3,6,9,11,13,14,16,17,20} : Finset (Fin 22)).sort = [0,3,6,9,11,13,14,16,17,20] := by
    refine (Finset.sortedLT_sort _).eq_of_mem_iff ?_ ?_
    · norm_num [List.sortedLT_iff_pairwise]
    · intro i; simp
  refine {
    nonzero := ?_, a_positive := ?_, minimum_inequalities := ?_,
    negative_minimum := ?_, positive_minimum := ?_,
    negative_attained := ?_, positive_attained := ?_,
    p_maximum := ?_, d_minimum := ?_, five_positive := ?_, five_negative := ?_,
    x_positive_large := ?_, incoming_d := ?_,
    p_row := {proper := ?_, parent_large := ?_, small := ?_, terminal_large := ?_},
    x_row_length := ?_, d_row_length := ?_, beta_row_length := ?_,
    gamma_row_short := ?_, c0_hard := ?_, beta_alternative := ?_,
    delta_positive := ?_, delta_hard := ?_, b1_hard := ?_, w_bounds := ?_,
    w_hard := ?_, w_row_length := ?_, nonET := ?_, u_above_z := ?_,
    power_branch := ?_, a0_bound := ?_ }
  all_goals
    (try simp [sourceSeed, sourceLength, sourceParent, source_offset_eq, hl, hcard, hsort, hs]) <;>
      exact of_decide_eq_true rfl

private theorem rejected_law {k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (hc : OriginalM5 k t L a b p d x) (hk : 0 < k) : ¬ arena.Law rejected := by
  intro h
  obtain ⟨word, hp, _, htotal, _⟩ := h hc
  have hlen := hp.length_eq
  simp only [List.length_finRange] at hlen
  have hone : (word.map (fun _ => (1 : ℤ))).sum = word.length := by simp
  change (word.map (fun _ => (1 : ℤ))).sum = 0 at htotal
  rw [hone, hlen] at htotal
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨21, 1864540⟩, 0, 1, ?_⟩
  norm_num [actual, realize, actualSource, centered, modulus]

def source_registration : Registration arena (type_of% (@exists_full_word)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_full_word, rejected, rejected_law lower_control (by decide)⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law half_control (by decide)⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.M5FullWordConsumer.exists_full_word)
    (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.M5FullWordConsumer.exists_full_word.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.M5FullWordConsumer.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => actualSource p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.M5FullWordConsumer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.M5FullWordConsumer
