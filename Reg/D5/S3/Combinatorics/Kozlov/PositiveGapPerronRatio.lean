import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Kozlov.PositiveGapPerronRatio

/-! The two readouts are the full proper and lattice gap transfers in each ground-set size. -/

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Combinatorics.Kozlov
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Combinatorics.Kozlov.PositiveGapPerronRatio

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output role n := Bool.rec (motive := fun _ => Type)
    (Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℕ) (Matrix (Fin n) (Fin n) ℕ) role
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (n δ : ℕ), 4 ≤ n → 1 ≤ δ →
    let P := obs.readout false n δ
    let L := obs.readout true n δ
    let ρP := spectralRadius ℂ (P.map (fun k : ℕ => (k : ℂ)))
    let ρL := spectralRadius ℂ (L.map (fun k : ℕ => (k : ℂ)))
    0 < ρP ∧ 0 < ρL ∧ ρP < ρL ∧ 0 < ρL.toReal ∧ ρP.toReal / ρL.toReal < 1

private abbrev observe (role : Bool) (n δ : ℕ) : signature.Output role n :=
  Bool.rec (motive := fun i => signature.Output i n)
    (properPositiveGapTransfer n δ) (latticePositiveGapTransfer n δ) role

private def actual : Realization signature := realize signature observe (fun e _ => e.elim)

private def intervention (role : Bool) : Realization signature :=
  realize signature (fun i n δ =>
    if i = role then (by cases i <;> exact 0) else actual.readout i n δ) (fun e _ => e.elim)

private theorem intervention_fails (role : Bool) : ¬ arena.Law (intervention role) := by
  intro h
  have h := h 4 1 (by decide) (by decide)
  cases role
  · have hp := h.1
    change 0 < spectralRadius ℂ ((0 : Matrix (Fin 2 ⊕ Fin 4) (Fin 2 ⊕ Fin 4) ℕ).map
      (fun k : ℕ => (k : ℂ))) at hp
    simp [Matrix.map_zero] at hp
  · have hl := h.2.1
    change 0 < spectralRadius ℂ ((0 : Matrix (Fin 4) (Fin 4) ℕ).map
      (fun k : ℕ => (k : ℂ))) at hl
    simp [Matrix.map_zero] at hl

private theorem degree_one_indeg {f : FVector 4} (ht : top f = 1) : indeg f ≤ 2 := by
  let k : Fin (4 + 1) := ⟨2, by decide⟩
  have hz : f k = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hh := le_top_of_pos hp
    change (2 : ℤ) ≤ top f at hh
    omega
  have hlt : f k < cap k := by rw [hz]; exact cap_pos k
  exact indeg_le_of_lt_cap hlt

private theorem proper_changes :
    properPositiveGapTransfer 4 1 ≠ properPositiveGapTransfer 4 4 := by
  let row : Fin 2 ⊕ Fin 4 := Sum.inr ⟨3, by decide⟩
  let col : Fin 2 ⊕ Fin 4 := Sum.inr ⟨0, by decide⟩
  intro e
  have he := congrArg (fun M : Matrix _ _ ℕ => M row col) e
  change ((properVectors 4).filter (fun f => top f = 1 ∧ (4 : ℤ) < (indeg f : ℤ) + 1)).card =
    ((properVectors 4).filter (fun f => top f = 1 ∧ (4 : ℤ) < (indeg f : ℤ) + 4)).card at he
  have h₁ : (properVectors 4).filter
      (fun f => top f = 1 ∧ (4 : ℤ) < (indeg f : ℤ) + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro f hf
    obtain ⟨_, ht, hi⟩ := Finset.mem_filter.mp hf
    have := degree_one_indeg ht
    omega
  have h₄ : 0 < ((properVectors 4).filter
      (fun f => top f = 1 ∧ (4 : ℤ) < (indeg f : ℤ) + 4)).card := by
    apply Finset.card_pos.mpr
    have hs : skeleton 4 1 ∈ SnF 4 := skeleton_mem_SnF (by decide)
    have ht : top (skeleton 4 1) = 1 := top_skeleton (⟨1, by decide⟩ : Fin (4 + 1))
    have hi : 1 < indeg (skeleton 4 1) := by
      apply (lt_indeg_iff (⟨1, by decide⟩ : Fin (4 + 1)) (SnF_bounded hs)).2
      intro j hj
      change j.val ≤ 1 at hj
      simp [skeleton, hj]
    exact ⟨_, Finset.mem_filter.mpr ⟨mem_properVectors.mpr hs, ht, by omega⟩⟩
  rw [h₁, Finset.card_empty] at he
  omega

private theorem lattice_changes :
    latticePositiveGapTransfer 4 1 ≠ latticePositiveGapTransfer 4 4 := by
  let hn : 1 ≤ (4 : ℕ) := by decide
  let row : Fin 4 := ⟨3, by decide⟩
  let col : Fin 4 := ⟨0, by decide⟩
  intro e
  have he := congrArg (fun M : Matrix _ _ ℕ => M row col) e
  change ((latticeVectors hn).filter
    (fun f => topState hn f = col ∧ positiveGapCondition 1 row f)).card =
    ((latticeVectors hn).filter
      (fun f => topState hn f = col ∧ positiveGapCondition 4 row f)).card at he
  have h₁ : (latticeVectors hn).filter
      (fun f => topState hn f = col ∧ positiveGapCondition 1 row f) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro f hf
    obtain ⟨hf, ht, hi⟩ := Finset.mem_filter.mp hf
    have ht' := topState_val hn (normalized_one_fixed hn ((mem_latticeVectors hn).mp hf))
    rw [ht] at ht'
    have := degree_one_indeg (by simpa [col] using ht'.symm)
    change 4 < indeg f + 1 at hi
    omega
  have h₄ : 0 < ((latticeVectors hn).filter
      (fun f => topState hn f = col ∧ positiveGapCondition 4 row f)).card := by
    apply Finset.card_pos.mpr
    have hs : skeleton 4 1 ∈ latticeVectors hn := skeleton_mem_latticeVectors hn (by decide)
    have ht := topState_val hn (normalized_one_fixed hn ((mem_latticeVectors hn).mp hs))
    have htop : top (skeleton 4 1) = 1 := top_skeleton (⟨1, by decide⟩ : Fin (4 + 1))
    have hstate : topState hn (skeleton 4 1) = col := by
      rw [htop] at ht
      apply Fin.ext
      change (topState hn (skeleton 4 1)).val = 0
      omega
    have hi : 1 < indeg (skeleton 4 1) := by
      apply (lt_indeg_iff (⟨1, by decide⟩ : Fin (4 + 1))
        (normalized_one_bounded hn ((mem_latticeVectors hn).mp hs))).2
      intro j hj
      change j.val ≤ 1 at hj
      simp [skeleton, hj]
    refine ⟨_, Finset.mem_filter.mpr ⟨hs, hstate, ?_⟩⟩
    change 4 < indeg (skeleton 4 1) + 4
    omega
  rw [h₁, Finset.card_empty] at he
  omega

def source_registration : Registration arena (type_of% positive_gap_perron_root_ratio) where
  actual := realize signature
    (fun i n δ => Bool.rec (motive := fun j => signature.Output j n)
      (properPositiveGapTransfer n δ) (latticePositiveGapTransfer n δ) i)
    (fun e _ => e.elim)
  bridge := Iff.rfl
  variation := ⟨positive_gap_perron_root_ratio, intervention false, intervention_fails false⟩
  sensitivity := by
    refine ⟨fun i => ⟨intervention i, ?_, rfl, intervention_fails i⟩, fun e => e.elim⟩
    intro j hji
    funext n δ
    simp [intervention, actual, realize, hji, observe]
  dependence := by
    intro i
    refine ⟨4, 1, 4, ?_⟩
    cases i
    · exact proper_changes
    · exact lattice_changes

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      positive_gap_perron_root_ratio (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Kozlov.positive_gap_perron_root_ratio.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Kozlov.PositiveGapPerronRatio.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun i n δ => Bool.rec (motive := fun j => signature.Output j n)
      (properPositiveGapTransfer n δ) (latticePositiveGapTransfer n δ) i)
    (fun e _ => e.elim))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Kozlov.PositiveGapPerronRatio
    definition := none
    coordinates := #[0]
    -- Bool.fintype lists true before false.
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "value"],
        stateBinder := 1, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "value"],
        stateBinder := 1, functionOperand := false, stateOperand := none,
        booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Kozlov.PositiveGapPerronRatio
