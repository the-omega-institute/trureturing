import Batteries.Tactic.OpenPrivate
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.OriginalLowerFullBank
import Reg.D5.S3.Combinatorics.Circle.M5FullWordConsumer
import Reg.Support.DependentFamily

/-! # Source-bound audit of the exact LOWER retained-bank implication -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open private lower_control source_offset_eq from Reg.D5.S3.Combinatorics.Circle.M5FullWordConsumer
namespace Reg.D5.S3.Combinatorics.Circle.OriginalLowerFullBank
open _root_.D5.S3.Combinatorics.Circle.OriginalLowerFullBank
open _root_.D5.S3.Combinatorics.Circle.M5FullWordConsumer
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open Fin.NatCast
open scoped BigOperators
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
  realize signature (fun _ p _ => halfCapacity p.1 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m k t L : ℕ} {a b : ℤ} {p d x : Fin k}
    (h : OriginalSource m k t L a b p d x)
    (hLower : (2 : ℤ) ^ (sourceLength t x 6 + 1) ≤ (2 : ℤ) ^ (L + 1) / 4),
    let D := sourceCoordinates h
    let s := R.readout () ⟨k, t⟩
    ∃ (A f : ℤ) (c : ℕ)
      (Sn : Finset (Fin (sourceLength t x 2)))
      (Sw : Finset (Fin (sourceLength t x 4)))
      (Sz : Finset (Fin (sourceLength t x 0))) (word : List (Fin k)),
      1 ≤ A ∧ A ≤ D.H / 4 ∧ 0 ≤ f ∧ f ≤ (D.w - 1) / 2 ∧
      2 * f = D.n + D.w + D.Δ - 2 * A * (D.w - D.n) ∧
      2 * (D.w - D.n) * (A - 1) < D.n + D.Δ + 1 ∧
      D.n + D.Δ + 1 ≤ 2 * (D.w - D.n) * A ∧
      (∑ j ∈ Sn, (2 : ℤ) ^ j.val) = A ∧ (∑ j ∈ Sw, (2 : ℤ) ^ j.val) = D.H / 4 - A ∧ (∑ j ∈ Sz, (2 : ℤ) ^ j.val) = (c : ℤ) ∧
      (c : ℤ) ≤ D.q - 1 ∧
      (∀ j : ℕ, j < c → A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b +
        (j : ℤ) * D.z < (D.u - D.z) / 2) ∧
      (let Kfull := sourceMask t x 2 Sn ∪ sourceMask t x 4 Sw ∪
        sourceMask t x 1 Finset.univ ∪ sourceMask t x 0 Sz ∪ sourceMask t x 6 Finset.univ
       let Dold := A * D.n + (D.H / 4 - A) * D.w - (D.q - 1) * D.b
       (D.u - D.z) / 2 ≤ Dold + (c : ℤ) * D.z ∧
       Dold + (c : ℤ) * D.z ≤ D.u - (D.z + 1) / 2 ∧
       word.Nodup ∧ word.head? = some x ∧
       (∀ j : ℕ, 0 ≤ ((word.take j).map (s)).sum ∧
         ((word.take j).map (s)).sum ≤ halfCapacity k) ∧
       Disjoint word.toFinset Kfull ∧
       word.toFinsetᶜ = Kfull ∪ futureLabels m t x ∧
       Disjoint Kfull (futureLabels m t x) ∧
       2 * ((word.map (s)).sum + ∑ i ∈ Kfull, s i) = D.z + D.y ∧
       (D.e = 1 → 4 ≤ D.F → D.y ≤ 2 * b - 3 →
         ∃ (hr : sourceLength t x 6 < sourceLength t x 4)
           (Slow : Finset (Fin (sourceLength t x 4))),
           (∑ j ∈ Slow, (2 : ℤ) ^ j.val) = (2 : ℤ) ^ sourceLength t x 6 - A ∧
           (∀ j ∈ Slow, j.val < sourceLength t x 6) ∧
           Disjoint Slow {⟨sourceLength t x 6, hr⟩} ∧
           Sw = (liftMask (Nat.succ_le_of_lt hr) Finset.univ)ᶜ ∪
             {⟨sourceLength t x 6, hr⟩} ∪ Slow ∧
           sourceMask t x 4 Slow ⊆ Kfull ∧
           advance (sourceParent t x 4) (sourceLength t x 6 + 1) ∈ Kfull ∧
           (2 ≤ A → Sw ≠ Finset.univ)))

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨21, 1864540⟩, 0, 1, ?_⟩
  norm_num [actual, realize, actualSource, centered, modulus]

private theorem rejected_law
    (control : OriginalSource 5 21 1864540 2 203877 236263 15 2 20)
    (lower : (2 : ℤ) ^ (sourceLength 1864540 (20 : Fin 21) 6 + 1) ≤
      (2 : ℤ) ^ (2 + 1) / 4) : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, f, c, Sn, Sw, Sz, word, hA, hAG, hf, hfg, heq, hprev, hnext,
    hSn, hSw, hSz, hcq, hmin, rest⟩ := h control lower
  obtain ⟨_, _, _, hhead, hprefix, _⟩ := rest
  cases word with
  | nil => simp at hhead
  | cons i tail =>
    have hb := (hprefix 1).2
    change halfCapacity 21 + 1 ≤ halfCapacity 21 at hb
    omega

private theorem control : OriginalSource 5 21 1864540 2 203877 236263 15 2 20 := by
  let hc := lower_control
  exact {
    pairs := by decide,
    nonzero := hc.nonzero,
    a_positive := hc.a_positive,
    minimum_inequalities := hc.minimum_inequalities,
    negative_minimum := hc.negative_minimum,
    positive_minimum := hc.positive_minimum,
    negative_attained := hc.negative_attained,
    positive_attained := hc.positive_attained,
    p_maximum := hc.p_maximum,
    d_minimum := hc.d_minimum,
    positive_count := hc.five_positive,
    negative_count := hc.five_negative,
    x_positive_large := hc.x_positive_large,
    incoming_d := hc.incoming_d,
    p_row := hc.p_row,
    x_row_length := hc.x_row_length,
    d_row_length := hc.d_row_length,
    beta_row_length := hc.beta_row_length,
    gamma_row_short := hc.gamma_row_short,
    c0_hard := hc.c0_hard,
    beta_alternative := hc.beta_alternative,
    delta_positive := hc.delta_positive,
    delta_hard := hc.delta_hard,
    b1_hard := hc.b1_hard,
    w_bounds := hc.w_bounds,
    w_hard := hc.w_hard,
    w_row_length := hc.w_row_length,
    nonET := hc.nonET,
    u_above_z := hc.u_above_z,
    power_branch := hc.power_branch,
  }

private theorem control_lower :
    (2 : ℤ) ^ (sourceLength 1864540 (20 : Fin 21) 6 + 1) ≤ (2 : ℤ) ^ (2 + 1) / 4 := by
  have hs : actualSource 21 1864540 =
      (![-232611,-465222,-930444,236263,472526,945052,-207047,-414094,-828188,
        440775,881550,-334051,-668102,760947,-575257,946637,-203877,-407754,
        -815508,466135,932270] : Fin 21 → ℤ) := by
    funext i
    fin_cases i <;> norm_num [actualSource, centered, modulus]
  have hl : largeOffsets 1864540 (20 : Fin 21) =
      ({0,3,6,9,11,13,14,15,16,19} : Finset (Fin 21)) := by
    unfold largeOffsets
    rw [hs]
    decide +kernel
  have hcard : ({0,3,6,9,11,13,14,15,16,19} : Finset (Fin 21)).card = 10 := by
    decide +kernel
  have hsort : ({0,3,6,9,11,13,14,15,16,19} : Finset (Fin 21)).sort =
      [0,3,6,9,11,13,14,15,16,19] := by
    refine (Finset.sortedLT_sort _).eq_of_mem_iff ?_ ?_
    · norm_num [List.sortedLT_iff_pairwise]
    · intro i; simp
  norm_num [sourceLength, source_offset_eq, hl, hcard, hsort]

def source_registration : Registration arena (type_of% (@canonical_lower_full_bank)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@canonical_lower_full_bank, rejected, rejected_law control control_lower⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law control control_lower⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.OriginalLowerFullBank.canonical_lower_full_bank)
    (Realization signature) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.OriginalLowerFullBank.canonical_lower_full_bank.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.OriginalLowerFullBank.source_registration
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
    owner := `D5.S3.Combinatorics.Circle.OriginalLowerFullBank
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Circle.OriginalLowerFullBank
