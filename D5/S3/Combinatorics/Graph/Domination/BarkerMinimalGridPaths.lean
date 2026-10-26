/- GID: D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths
   mirror-E: none(waiver:internal-stage-a)
   anchors: []
   utility: none
   digest: Accepted appended-mask words are unambiguously counted by the full open-grid transfer. -/

import D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridPaths

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridEncoding
open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer

/-- An accepted appended-mask word has weight one; witnesses add no choices. -/
def runWeight : (k : ℕ) → State → (Fin k → Fin 8) → ℤ
  | 0, s, _ => terminal s
  | k + 1, s, w => (if accepts (window s ⟨(w 0).val, by omega⟩) then 1 else 0) *
      runWeight k (append s (w 0)) (fun i => w i.succ)

private theorem runWeight_zero_one (k : ℕ) (s : State) (w : Fin k → Fin 8) :
    runWeight k s w = 0 ∨ runWeight k s w = 1 := by
  induction k generalizing s with
  | zero => unfold runWeight terminal; split <;> simp_all
  | succ k ih =>
    simp only [runWeight]
    split
    · simpa using ih (append s (w 0)) (fun i => w i.succ)
    · simp

/-- The exact sum over appended masks, proved by the first-mask decomposition. -/
theorem sum_runWeight (k : ℕ) (s : State) :
    (∑ w : Fin k → Fin 8, runWeight k s w) = fullOrbit k s := by
  induction k generalizing s with
  | zero => simp [runWeight, fullOrbit]
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 8)).sum_comp
      (fun w => runWeight (k + 1) s w), Fintype.sum_prod_type]
    change (∑ a : Fin 8, ∑ w : Fin k → Fin 8,
      runWeight (k + 1) s (Fin.cons a w)) = _
    change (∑ a : Fin 8, ∑ w : Fin k → Fin 8,
      (if accepts (window s ⟨a.val, by omega⟩) then (1 : ℤ) else 0) *
        runWeight k (append s a) w) = _
    simp_rw [← Finset.mul_sum]
    simp_rw [ih]
    change _ = ∑ m : Fin 8, if accepts (window s ⟨m.val, by omega⟩)
      then fullOrbit k (append s m) else 0
    apply Finset.sum_congr rfl
    intro m _
    split <;> simp_all

/-- Four history symbols, followed by the real suffix and then open-end absence.
The history coordinates are -2,-1,0,1. -/
def expanded {k : ℕ} (s : State) (w : Fin k → Fin 8) (j : ℤ) : Symbol :=
  if h : -2 ≤ j ∧ j < 2 then columns s ⟨(j + 2).toNat, by omega⟩
  else if h : 2 ≤ j ∧ j < k + 2 then ⟨(w ⟨(j - 2).toNat, by omega⟩).val, by omega⟩
  else 8

/-- The window with nonnegative centre c in the history-and-suffix stream. -/
def expandedWindow {k : ℕ} (s : State) (w : Fin k → Fin 8) (c : ℕ) : Window :=
  fun i => expanded s w ((c : ℤ) + i.val - 2)

private theorem expanded_shift {k : ℕ} (s : State) (w : Fin (k + 1) → Fin 8)
    (j : ℤ) (hj : -2 ≤ j) :
    expanded (append s (w 0)) (fun i => w i.succ) j = expanded s w (j + 1) := by
  by_cases hlow : j < 1
  · have hleft : -2 ≤ j ∧ j < 2 := by omega
    have hright : -2 ≤ j + 1 ∧ j + 1 < 2 := by omega
    rw [expanded, dite_eq_left hleft, expanded, dite_eq_left hright, columns_append]
    have hi : (j + 2).toNat < 3 := by omega
    rw [dite_eq_left hi]
    congr 1
    apply Fin.ext
    dsimp
    omega
  · by_cases hone : j = 1
    · subst j
      simp [expanded, columns_append]
    · have htwo : 2 ≤ j := by omega
      by_cases htop : j < k + 2
      · have hl : ¬ (-2 ≤ j ∧ j < 2) := by omega
        have hr : ¬ (-2 ≤ j + 1 ∧ j + 1 < 2) := by omega
        have hfuture : 2 ≤ j ∧ j < k + 2 := ⟨htwo, htop⟩
        have hfuture' : 2 ≤ j + 1 ∧ j + 1 < ↑(k + 1) + 2 := by omega
        rw [expanded, dite_eq_right hl, dite_eq_left hfuture,
          expanded, dite_eq_right hr, dite_eq_left hfuture']
        have hi : (⟨(j - 2).toNat, by omega⟩ : Fin k).succ =
            (⟨(j + 1 - 2).toNat, by omega⟩ : Fin (k + 1)) := by
          apply Fin.ext
          dsimp
          omega
        apply Fin.ext
        exact congrArg (fun x : Fin (k + 1) => (w x).val) hi
      · have hl : ¬ (-2 ≤ j ∧ j < 2) := by omega
        have hr : ¬ (-2 ≤ j + 1 ∧ j + 1 < 2) := by omega
        have hfuture : ¬ (2 ≤ j ∧ j < k + 2) := by omega
        have hfuture' : ¬ (2 ≤ j + 1 ∧ j + 1 < ↑(k + 1) + 2) := by omega
        simp only [expanded, dite_eq_right hl, dite_eq_right hr,
          dite_eq_right hfuture, dite_eq_right hfuture']

private theorem expandedWindow_shift {k : ℕ} (s : State) (w : Fin (k + 1) → Fin 8)
    (c : ℕ) :
    expandedWindow (append s (w 0)) (fun i => w i.succ) c = expandedWindow s w (c + 1) := by
  funext i
  rw [expandedWindow, expanded_shift s w _ (by omega), expandedWindow]
  congr 1
  omega

private theorem expandedWindow_first {k : ℕ} (s : State) (w : Fin (k + 1) → Fin 8) :
    expandedWindow s w 0 = window s ⟨(w 0).val, by omega⟩ := by
  funext i
  fin_cases i <;> simp [expandedWindow, expanded, window, Fin.snoc] <;> congr 1

private theorem expandedWindow_zero (s : State) (w : Fin 0 → Fin 8) :
    expandedWindow s w 0 = window s 8 ∧
      expandedWindow s w 1 = ![columns s 1, columns s 2, columns s 3, 8, 8] := by
  constructor <;> funext i <;> fin_cases i <;>
    simp [expandedWindow, expanded, window, Fin.snoc] <;> congr 1

/-- The recursive run checks exactly every remaining real centre, including both
terminal checks; the statement also covers a zero-length appended suffix. -/
theorem runWeight_iff_tests (k : ℕ) (s : State) (w : Fin k → Fin 8) :
    runWeight k s w = 1 ↔ ∀ c : Fin (k + 2), Local (expandedWindow s w c.val) := by
  induction k generalizing s with
  | zero =>
    have hz := expandedWindow_zero s w
    simp only [runWeight, terminal]
    rw [Fin.forall_fin_succ, Fin.forall_fin_succ]
    simp only [Fin.val_zero, Fin.val_succ, Fin.forall_fin_zero, and_true]
    rw [hz.1, hz.2]
    simp [accepts, Bool.and_eq_true]
  | succ k ih =>
    have hrun : runWeight (k + 1) s w = 1 ↔
        accepts (window s ⟨(w 0).val, by omega⟩) = true ∧
          runWeight k (append s (w 0)) (fun i => w i.succ) = 1 := by
      simp only [runWeight]
      split <;> simp_all
    rw [hrun, ih]
    conv_rhs => rw [Fin.forall_fin_succ]
    simp only [Fin.val_zero, Fin.val_succ, expandedWindow_shift, ← expandedWindow_first]
    simp only [accepts, decide_eq_true_eq]

/-- The state containing the two initial labelled masks. -/
def start (a b : Fin 8) : State := ⟨8 * a.val + b.val, by omega⟩

private theorem columns_start (a b : Fin 8) :
    columns (start a b) = ![8, 8, ⟨a.val, by omega⟩, ⟨b.val, by omega⟩] := by
  funext i
  have h : (start a b).val < 64 := by simp [start]; omega
  apply Fin.ext
  simp only [columns, dite_eq_left h]
  fin_cases i <;> simp [start] <;> omega

private theorem expanded_start {k : ℕ} (a b : Fin 8) (w : Fin k → Fin 8)
    (c : Fin (k + 2)) :
    expandedWindow (start a b) w c.val =
      paddedWindow (fun (d : Fin (k + 2)) => maskEquiv ((Fin.cons a (Fin.cons b w) : Fin (k + 2) → Fin 8) d)) c := by
  funext i
  change expanded (start a b) w ((c.val : ℤ) + i.val - 2) =
    symbol (padded _ ((c.val : ℤ) + i.val - 2))
  generalize hjdef : ((c.val : ℤ) + i.val - 2) = j
  have hj : -2 ≤ j := by omega
  by_cases hneg : j < 0
  · have hl : -2 ≤ j ∧ j < 2 := by omega
    have hr : ¬ (0 ≤ j ∧ j < ↑(k + 2)) := by omega
    rw [expanded, dite_eq_left hl, columns_start, padded, dite_eq_right hr, symbol]
    have hc : j = -2 ∨ j = -1 := by omega
    rcases hc with rfl | rfl <;> simp
  · have hj0 : 0 ≤ j := by omega
    by_cases hsmall : j < 2
    · have hl : -2 ≤ j ∧ j < 2 := by omega
      have hr : 0 ≤ j ∧ j < ↑(k + 2) := by omega
      rw [expanded, dite_eq_left hl, columns_start, padded, dite_eq_left hr, symbol]
      have hc : j = 0 ∨ j = 1 := by omega
      rcases hc with rfl | rfl <;> simp [Fin.cons]
      have he : (1 : Fin (k + 2)) = (0 : Fin (k + 1)).succ := by
        apply Fin.ext
        simp
      rw [he]
      rfl
    · have hl : ¬ (-2 ≤ j ∧ j < 2) := by omega
      by_cases htop : j < ↑(k + 2)
      · have hfuture : 2 ≤ j ∧ j < ↑k + 2 := by omega
        have hr : 0 ≤ j ∧ j < ↑(k + 2) := ⟨hj0, htop⟩
        rw [expanded, dite_eq_right hl, dite_eq_left hfuture,
          padded, dite_eq_left hr, symbol]
        simp only [Equiv.symm_apply_apply]
        congr 1
        have he : (⟨j.toNat, by omega⟩ : Fin (k + 2)) =
            (⟨(j - 2).toNat, by omega⟩ : Fin k).succ.succ := by
          apply Fin.ext
          dsimp
          omega
        rw [he]
        rfl
      · have hfuture : ¬ (2 ≤ j ∧ j < ↑k + 2) := by omega
        have hr : ¬ (0 ≤ j ∧ j < ↑(k + 2)) := by omega
        simp only [expanded, dite_eq_right hl, dite_eq_right hfuture,
          padded, dite_eq_right hr, symbol]

/-- A numeric word is accepted precisely by its unique start and suffix run. -/
theorem accepted_cons_iff {k : ℕ} (a b : Fin 8) (w : Fin k → Fin 8) :
    (Fin.cons a (Fin.cons b w)) ∈ acceptedWords (k + 2) ↔ runWeight k (start a b) w = 1 := by
  simp only [acceptedWords, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [runWeight_iff_tests]
  exact forall_congr' fun c => by rw [expanded_start]

/-- Exact all-length actual-subset counting by the full transfer orbit. -/
theorem actualCount_fullOrbit (k : ℕ) :
    (actualCount (k + 2) : ℤ) = ∑ s : Fin 64, fullOrbit k ⟨s.val, by omega⟩ := by
  rw [actualCount_eq_acceptedWords]
  have hc : ((acceptedWords (k + 2)).card : ℤ) =
      ∑ w : Fin (k + 2) → Fin 8, if w ∈ acceptedWords (k + 2) then 1 else 0 := by
    simp
  rw [hc]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => Fin 8)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ a : Fin 8, ∑ w : Fin (k + 1) → Fin 8,
    if Fin.cons a w ∈ acceptedWords (k + 2) then (1 : ℤ) else 0) = _
  have hinner (a : Fin 8) :
      (∑ w : Fin (k + 1) → Fin 8,
        if Fin.cons a w ∈ acceptedWords (k + 2) then (1 : ℤ) else 0) =
      ∑ b : Fin 8, fullOrbit k (start a b) := by
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 8)).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ b : Fin 8, ∑ w : Fin k → Fin 8,
      if Fin.cons a (Fin.cons b w) ∈ acceptedWords (k + 2) then (1 : ℤ) else 0) = _
    apply Finset.sum_congr rfl
    intro b _
    simp_rw [accepted_cons_iff]
    have hh (w : Fin k → Fin 8) :
        (if runWeight k (start a b) w = 1 then (1 : ℤ) else 0) = runWeight k (start a b) w := by
      rcases runWeight_zero_one k (start a b) w with h | h <;> simp [h]
    simp_rw [hh]
    exact sum_runWeight k (start a b)
  simp_rw [hinner]
  rw [← Fintype.sum_prod_type (fun p : Fin 8 × Fin 8 => fullOrbit k (start p.1 p.2))]
  rw [← (finProdFinEquiv (m := 8) (n := 8)).sum_comp
    (fun s : Fin 64 => fullOrbit k ⟨s.val, by omega⟩)]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Fin.ext
  simp [start, finProdFinEquiv]
  omega

end D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridPaths
