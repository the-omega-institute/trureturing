/- GID: D5/S0/Certificates/Games/PnimHeavyIntervalRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/PnimHeavyIntervalRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.claim; result=D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.result; claim=D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.claim
   digest: Refutes PNim heavy-interval Conjecture 2 of arXiv:2506.04991v1. -/

/- proof_shape: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #8467)
   Direct frozen dependencies: none. -/

import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S0.Certificates.Games.PnimHeavyIntervalRefutation

/-!
Single-partition PNim deletes any nonempty subset of diagram rows or columns,
merging the remaining rows or columns. The cell-count filter extends the
recursion to arbitrary natural lists; it removes no legal move of a positive
nonincreasing partition. Heavy means that the Grundy value is the longest-play
length, given by Proposition 2 as the first row plus the number of rows minus
one. The empty partition is not heavy.

Conjecture 2 of Gottlieb, Krnc and Mursic, arXiv:2506.04991v1 (page 14),
is represented by claim. Natural parameters with b <= a are precisely the
integer parameters for which both displayed endpoints are partitions. The
counterexample is [9,9,8,8,8,5,5,5] at a = 8, b = 7. Only this printed
conjecture is refuted; no priority or corrected formula is asserted.
-/

/-- A partition is represented by its nonincreasing positive row lengths. -/
abbrev Position := List Nat

/-- Delete the indicated zero-based diagram columns and merge what remains. -/
def deleteColumns (p deleted : Position) : Position :=
  (p.map fun n => n - (deleted.filter fun j => j < n).length).filter (· != 0)

/-- Delete a nonempty subset of rows. -/
def rowMoves (p : Position) : List Position :=
  p.sublists.filter (fun q => q.length < p.length)

/-- Delete a nonempty subset of the columns present in the first row. -/
def columnMoves (p : Position) : List Position :=
  ((List.range (p.headD 0)).sublists.filter (· != [])).map (deleteColumns p)

/-- All 1-PNim followers. The sum filter is redundant on positive partitions. -/
def moves (p : Position) : List Position :=
  (rowMoves p ++ columnMoves p).filter (fun q => q.sum < p.sum)

/-- Least natural number absent from a finite set. -/
def mex (s : Finset Nat) : Nat :=
  (Finset.range (s.card + 1) \ s).min' (by
    apply Finset.sdiff_nonempty.mpr
    intro h
    have hc := Finset.card_le_card h
    simp only [Finset.card_range] at hc
    omega)

/-- The 1-PNim Grundy function, recursively evaluated by cell count. -/
def grundy : Position → Nat :=
  (measure List.sum).wf.fix fun p rec =>
    mex ((moves p).attach.map (fun q => rec q.val (by
      have hq := q.property
      simp only [moves, List.mem_filter] at hq
      have hdecreases : q.val.sum < p.sum := of_decide_eq_true hq.2
      exact hdecreases))).toFinset

private inductive Certificate where
  | empty
  | branch (position : Position) (candidate : Nat) (left right : Certificate)

private def domain : Certificate → List Position
  | .empty => []
  | .branch p _ left right => domain left ++ p :: domain right

private def lookup (p : Position) : Certificate → Option Nat
  | .empty => none
  | .branch q n left right =>
      if p = q then some n else
      if compare p q = .lt then lookup p left else lookup p right

private def lookup_mem (c : Certificate) (p : Position)
    (h : (lookup p c).isSome = true) : p ∈ domain c := by
  induction c with
  | empty => simp [lookup] at h
  | branch q n left right ihl ihr =>
    simp only [lookup] at h
    split_ifs at h with hp hlt
    · simp [domain, hp]
    · simp [domain, ihl h]
    · simp [domain, ihr h]

private def value (c : Certificate) (p : Position) := (lookup p c).getD 0

private def check (c : Certificate) (p : Position) : Bool :=
  let options := moves p
  let used := options.map (value c)
  options.all (fun q => (lookup q c).isSome) &&
    !used.contains (value c p) &&
    (List.range (value c p)).all (fun n => used.contains n)

private def certificate_correct (c : Certificate)
    (hc : (domain c).all (check c) = true) (p : Position) (hp : p ∈ domain c) :
    grundy p = value c p := by
  induction p using (measure List.sum).wf.induction with
  | h p ih =>
    have hcheck := List.all_eq_true.mp hc p hp
    simp only [check, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
      Bool.not_eq_true', Bool.eq_false_iff, List.mem_range] at hcheck
    obtain ⟨⟨hclosed, hmissing⟩, hbelow⟩ := hcheck
    calc
      grundy p = mex ((moves p).map grundy).toFinset := by
        rw [grundy, WellFounded.fix_eq]
        simp
      _ = mex ((moves p).map (value c)).toFinset := by
        have he : (moves p).map grundy = (moves p).map (value c) := by
          apply List.map_congr_left
          intro q hq
          have hdecreases : q.sum < p.sum := by
            have hq' := hq
            simp only [moves, List.mem_filter] at hq'
            exact of_decide_eq_true hq'.2
          exact ih q hdecreases (lookup_mem c q (hclosed q hq))
        rw [he]
      _ = value c p := by
        let s : Finset Nat := ((moves p).map (value c)).toFinset
        change mex s = value c p
        have hspec : mex s ∉ s ∧ ∀ n < mex s, n ∈ s := by
          have hnonempty : (Finset.range (s.card + 1) \ s).Nonempty := by
            apply Finset.sdiff_nonempty.mpr
            intro h
            have hc := Finset.card_le_card h
            simp only [Finset.card_range] at hc
            omega
          have hm := Finset.min'_mem _ hnonempty
          change mex s ∈ Finset.range (s.card + 1) \ s at hm
          rcases Finset.mem_sdiff.mp hm with ⟨hr, hs⟩
          refine ⟨hs, fun n hn => ?_⟩
          by_contra hns
          have hmem : n ∈ Finset.range (s.card + 1) \ s := by
            simp only [Finset.mem_sdiff, Finset.mem_range] at *
            exact ⟨by omega, hns⟩
          have hle := Finset.min'_le _ n hmem
          change mex s ≤ n at hle
          omega
        obtain ⟨hmissingMex, hsmallMex⟩ := hspec
        have hbelowFin : ∀ n < value c p, n ∈ s := by
          intro n hn
          exact List.mem_toFinset.mpr (hbelow n hn)
        have hnot : value c p ∉ s := by
          simpa [s, List.contains_iff_mem] using hmissing
        rcases lt_trichotomy (mex s) (value c p) with h | h | h
        · exact False.elim (hmissingMex (hbelowFin _ h))
        · exact h
        · exact False.elim (hnot (hsmallMex _ h))

/-- Nonincreasing positive lists, including the empty partition. -/
def IsPartition (p : Position) : Prop :=
  p.Pairwise (· ≥ ·) ∧ p.all (· > 0) = true

private instance (p : Position) : Decidable (IsPartition p) := by
  unfold IsPartition
  infer_instance

/-- Young's-lattice order, expressed by length and aligned row comparisons. -/
def youngLE (p q : Position) : Prop :=
  p.length ≤ q.length ∧ (p.zip q).all (fun pair => pair.1 ≤ pair.2) = true

private instance (p q : Position) : Decidable (youngLE p q) := by
  unfold youngLE
  infer_instance

def rectangle (a b : Nat) : Position := List.replicate (b + 1) (a + 1)

def staircase (a b : Nat) : Position :=
  (List.range (b + 1)).map (fun i => a + 1 - i)

/-- A nonempty partition is heavy when Grundy value equals longest-play length. -/
def heavy (p : Position) : Prop :=
  p ≠ [] ∧ grundy p = p.headD 0 + p.length - 1

/-- Gottlieb-Krnc-Mursic Conjecture 2, with every partition quantifier explicit. -/
def claim : Prop :=
  ∀ a b : Nat, b ≤ a → heavy (rectangle a b) →
    ∀ p : Position, IsPartition p →
      youngLE (staircase a b) p → youngLE p (rectangle a b) → heavy p

private def witnessCertificate : Certificate :=
  .branch [6, 2] 7 (.branch [4, 4, 3, 3, 3, 2, 2] 10 (.branch [3, 3, 3, 1, 1] 7 (.branch [3, 1] 4 (.branch
  [2, 2, 1, 1, 1] 6 (.branch [2] 2 (.branch [1, 1, 1, 1] 4 (.branch [1, 1] 2 (.branch [1] 1 (.branch [] 0
  (.empty) (.empty)) (.empty)) (.branch [1, 1, 1] 3 (.empty) (.empty))) (.branch [1, 1, 1, 1, 1, 1, 1] 7
  (.branch [1, 1, 1, 1, 1, 1] 6 (.branch [1, 1, 1, 1, 1] 5 (.empty) (.empty)) (.empty)) (.branch [1, 1, 1, 1,
  1, 1, 1, 1] 8 (.empty) (.empty)))) (.branch [2, 1, 1, 1, 1, 1] 7 (.branch [2, 1, 1, 1] 5 (.branch [2, 1, 1]
  4 (.branch [2, 1] 3 (.empty) (.empty)) (.empty)) (.branch [2, 1, 1, 1, 1] 6 (.empty) (.empty))) (.branch
  [2, 2, 1] 4 (.branch [2, 2] 1 (.branch [2, 1, 1, 1, 1, 1, 1] 8 (.empty) (.empty)) (.empty)) (.branch [2, 2,
  1, 1] 5 (.empty) (.empty))))) (.branch [2, 2, 2, 2, 1, 1] 7 (.branch [2, 2, 2, 1] 5 (.branch [2, 2, 1, 1,
  1, 1, 1, 1] 9 (.branch [2, 2, 1, 1, 1, 1, 1] 8 (.branch [2, 2, 1, 1, 1, 1] 7 (.empty) (.empty)) (.empty))
  (.branch [2, 2, 2] 4 (.empty) (.empty))) (.branch [2, 2, 2, 2] 3 (.branch [2, 2, 2, 1, 1, 1] 7 (.branch [2,
  2, 2, 1, 1] 6 (.empty) (.empty)) (.empty)) (.branch [2, 2, 2, 2, 1] 6 (.empty) (.empty)))) (.branch [2, 2,
  2, 2, 2, 1, 1, 1] 9 (.branch [2, 2, 2, 2, 2, 1] 7 (.branch [2, 2, 2, 2, 2] 6 (.branch [2, 2, 2, 2, 1, 1, 1]
  8 (.empty) (.empty)) (.empty)) (.branch [2, 2, 2, 2, 2, 1, 1] 8 (.empty) (.empty))) (.branch [2, 2, 2, 2,
  2, 2, 2, 2] 7 (.branch [2, 2, 2, 2, 2, 2, 2] 8 (.branch [2, 2, 2, 2, 2, 2] 5 (.empty) (.empty)) (.empty))
  (.branch [3] 3 (.empty) (.empty)))))) (.branch [3, 3, 1, 1] 6 (.branch [3, 2, 2, 1, 1, 1] 8 (.branch [3, 2,
  1, 1] 6 (.branch [3, 2] 4 (.branch [3, 1, 1, 1] 6 (.branch [3, 1, 1] 5 (.empty) (.empty)) (.empty))
  (.branch [3, 2, 1] 5 (.empty) (.empty))) (.branch [3, 2, 2, 1] 6 (.branch [3, 2, 2] 5 (.branch [3, 2, 1, 1,
  1] 7 (.empty) (.empty)) (.empty)) (.branch [3, 2, 2, 1, 1] 7 (.empty) (.empty)))) (.branch [3, 2, 2, 2, 2]
  7 (.branch [3, 2, 2, 2, 1, 1] 8 (.branch [3, 2, 2, 2, 1] 7 (.branch [3, 2, 2, 2] 6 (.empty) (.empty))
  (.empty)) (.branch [3, 2, 2, 2, 1, 1, 1] 9 (.empty) (.empty))) (.branch [3, 3] 4 (.branch [3, 2, 2, 2, 2,
  2, 2] 9 (.branch [3, 2, 2, 2, 2, 2] 8 (.empty) (.empty)) (.empty)) (.branch [3, 3, 1] 5 (.empty)
  (.empty))))) (.branch [3, 3, 2, 2, 2] 7 (.branch [3, 3, 2, 1, 1, 1] 8 (.branch [3, 3, 2, 1] 6 (.branch [3,
  3, 2] 1 (.branch [3, 3, 1, 1, 1] 7 (.empty) (.empty)) (.empty)) (.branch [3, 3, 2, 1, 1] 7 (.empty)
  (.empty))) (.branch [3, 3, 2, 2, 1, 1] 8 (.branch [3, 3, 2, 2, 1] 7 (.branch [3, 3, 2, 2] 6 (.empty)
  (.empty)) (.empty)) (.branch [3, 3, 2, 2, 1, 1, 1] 9 (.empty) (.empty)))) (.branch [3, 3, 2, 2, 2, 2, 2] 9
  (.branch [3, 3, 2, 2, 2, 1, 1, 1] 10 (.branch [3, 3, 2, 2, 2, 1, 1] 9 (.branch [3, 3, 2, 2, 2, 1] 8
  (.empty) (.empty)) (.empty)) (.branch [3, 3, 2, 2, 2, 2] 8 (.empty) (.empty))) (.branch [3, 3, 3] 1
  (.branch [3, 3, 2, 2, 2, 2, 2, 2] 10 (.empty) (.empty)) (.branch [3, 3, 3, 1] 2 (.empty) (.empty)))))))
  (.branch [4, 3, 3, 2] 7 (.branch [3, 3, 3, 3, 3, 3, 3] 5 (.branch [3, 3, 3, 3, 2, 2] 8 (.branch [3, 3, 3,
  3] 2 (.branch [3, 3, 3, 2, 2] 7 (.branch [3, 3, 3, 2] 6 (.branch [3, 3, 3, 1, 1, 1] 8 (.empty) (.empty))
  (.empty)) (.branch [3, 3, 3, 2, 2, 2] 8 (.empty) (.empty))) (.branch [3, 3, 3, 3, 1, 1, 1] 9 (.branch [3,
  3, 3, 3, 1, 1] 8 (.branch [3, 3, 3, 3, 1] 7 (.empty) (.empty)) (.empty)) (.branch [3, 3, 3, 3, 2] 7
  (.empty) (.empty)))) (.branch [3, 3, 3, 3, 3, 1, 1, 1] 10 (.branch [3, 3, 3, 3, 3, 1] 8 (.branch [3, 3, 3,
  3, 3] 7 (.branch [3, 3, 3, 3, 2, 2, 2] 9 (.empty) (.empty)) (.empty)) (.branch [3, 3, 3, 3, 3, 1, 1] 9
  (.empty) (.empty))) (.branch [3, 3, 3, 3, 3, 2, 2, 2] 10 (.branch [3, 3, 3, 3, 3, 2, 2] 9 (.branch [3, 3,
  3, 3, 3, 2] 8 (.empty) (.empty)) (.empty)) (.branch [3, 3, 3, 3, 3, 3] 8 (.empty) (.empty))))) (.branch [4,
  3, 1] 6 (.branch [4, 1, 1, 1] 7 (.branch [4, 1] 5 (.branch [4] 4 (.branch [3, 3, 3, 3, 3, 3, 3, 3] 6
  (.empty) (.empty)) (.empty)) (.branch [4, 1, 1] 6 (.empty) (.empty))) (.branch [4, 2, 2, 2] 7 (.branch [4,
  2, 2] 6 (.branch [4, 2] 5 (.empty) (.empty)) (.empty)) (.branch [4, 3] 5 (.empty) (.empty)))) (.branch [4,
  3, 2, 2, 2] 8 (.branch [4, 3, 2] 6 (.branch [4, 3, 1, 1, 1] 8 (.branch [4, 3, 1, 1] 7 (.empty) (.empty))
  (.empty)) (.branch [4, 3, 2, 2] 7 (.empty) (.empty))) (.branch [4, 3, 3, 1, 1] 8 (.branch [4, 3, 3, 1] 7
  (.branch [4, 3, 3] 2 (.empty) (.empty)) (.empty)) (.branch [4, 3, 3, 1, 1, 1] 9 (.empty) (.empty))))))
  (.branch [4, 4, 3] 6 (.branch [4, 3, 3, 3, 3] 8 (.branch [4, 3, 3, 3, 1, 1] 9 (.branch [4, 3, 3, 3] 7
  (.branch [4, 3, 3, 2, 2, 2] 9 (.branch [4, 3, 3, 2, 2] 8 (.empty) (.empty)) (.empty)) (.branch [4, 3, 3, 3,
  1] 8 (.empty) (.empty))) (.branch [4, 3, 3, 3, 2, 2] 9 (.branch [4, 3, 3, 3, 2] 8 (.branch [4, 3, 3, 3, 1,
  1, 1] 10 (.empty) (.empty)) (.empty)) (.branch [4, 3, 3, 3, 2, 2, 2] 10 (.empty) (.empty)))) (.branch [4,
  4, 1, 1] 7 (.branch [4, 4] 3 (.branch [4, 3, 3, 3, 3, 3, 3] 6 (.branch [4, 3, 3, 3, 3, 3] 9 (.empty)
  (.empty)) (.empty)) (.branch [4, 4, 1] 6 (.empty) (.empty))) (.branch [4, 4, 2, 2] 7 (.branch [4, 4, 2] 6
  (.branch [4, 4, 1, 1, 1] 8 (.empty) (.empty)) (.empty)) (.branch [4, 4, 2, 2, 2] 8 (.empty) (.empty)))))
  (.branch [4, 4, 3, 3, 1, 1, 1] 10 (.branch [4, 4, 3, 2, 2] 8 (.branch [4, 4, 3, 1, 1, 1] 9 (.branch [4, 4,
  3, 1, 1] 8 (.branch [4, 4, 3, 1] 7 (.empty) (.empty)) (.empty)) (.branch [4, 4, 3, 2] 1 (.empty) (.empty)))
  (.branch [4, 4, 3, 3, 1] 8 (.branch [4, 4, 3, 3] 1 (.branch [4, 4, 3, 2, 2, 2] 9 (.empty) (.empty))
  (.empty)) (.branch [4, 4, 3, 3, 1, 1] 9 (.empty) (.empty)))) (.branch [4, 4, 3, 3, 3, 1] 9 (.branch [4, 4,
  3, 3, 2, 2, 2] 10 (.branch [4, 4, 3, 3, 2, 2] 9 (.branch [4, 4, 3, 3, 2] 8 (.empty) (.empty)) (.empty))
  (.branch [4, 4, 3, 3, 3] 8 (.empty) (.empty))) (.branch [4, 4, 3, 3, 3, 1, 1, 1] 11 (.branch [4, 4, 3, 3,
  3, 1, 1] 10 (.empty) (.empty)) (.branch [4, 4, 3, 3, 3, 2] 9 (.empty) (.empty)))))))) (.branch [5, 4, 4, 4,
  4, 4] 10 (.branch [5, 1, 1] 7 (.branch [4, 4, 4, 4, 2, 2] 9 (.branch [4, 4, 4, 2, 2] 8 (.branch [4, 4, 4] 2
  (.branch [4, 4, 3, 3, 3, 3, 3] 10 (.branch [4, 4, 3, 3, 3, 3] 9 (.branch [4, 4, 3, 3, 3, 2, 2, 2] 11
  (.empty) (.empty)) (.empty)) (.branch [4, 4, 3, 3, 3, 3, 3, 3] 11 (.empty) (.empty))) (.branch [4, 4, 4, 1,
  1, 1] 9 (.branch [4, 4, 4, 1, 1] 8 (.branch [4, 4, 4, 1] 7 (.empty) (.empty)) (.empty)) (.branch [4, 4, 4,
  2] 1 (.empty) (.empty)))) (.branch [4, 4, 4, 4] 1 (.branch [4, 4, 4, 3, 3] 8 (.branch [4, 4, 4, 3] 1
  (.branch [4, 4, 4, 2, 2, 2] 9 (.empty) (.empty)) (.empty)) (.branch [4, 4, 4, 3, 3, 3] 9 (.empty)
  (.empty))) (.branch [4, 4, 4, 4, 1, 1, 1] 10 (.branch [4, 4, 4, 4, 1, 1] 9 (.branch [4, 4, 4, 4, 1] 8
  (.empty) (.empty)) (.empty)) (.branch [4, 4, 4, 4, 2] 8 (.empty) (.empty))))) (.branch [4, 4, 4, 4, 4, 2,
  2] 10 (.branch [4, 4, 4, 4, 4] 8 (.branch [4, 4, 4, 4, 3, 3] 9 (.branch [4, 4, 4, 4, 3] 8 (.branch [4, 4,
  4, 4, 2, 2, 2] 10 (.empty) (.empty)) (.empty)) (.branch [4, 4, 4, 4, 3, 3, 3] 10 (.empty) (.empty)))
  (.branch [4, 4, 4, 4, 4, 1, 1, 1] 11 (.branch [4, 4, 4, 4, 4, 1, 1] 10 (.branch [4, 4, 4, 4, 4, 1] 9
  (.empty) (.empty)) (.empty)) (.branch [4, 4, 4, 4, 4, 2] 9 (.empty) (.empty)))) (.branch [4, 4, 4, 4, 4, 4]
  7 (.branch [4, 4, 4, 4, 4, 3, 3] 10 (.branch [4, 4, 4, 4, 4, 3] 9 (.branch [4, 4, 4, 4, 4, 2, 2, 2] 11
  (.empty) (.empty)) (.empty)) (.branch [4, 4, 4, 4, 4, 3, 3, 3] 11 (.empty) (.empty))) (.branch [5] 5
  (.branch [4, 4, 4, 4, 4, 4, 4, 4] 5 (.branch [4, 4, 4, 4, 4, 4, 4] 6 (.empty) (.empty)) (.empty)) (.branch
  [5, 1] 6 (.empty) (.empty)))))) (.branch [5, 4, 4, 1, 1] 9 (.branch [5, 4, 1, 1] 8 (.branch [5, 3] 6
  (.branch [5, 2, 2] 7 (.branch [5, 2] 6 (.branch [5, 1, 1, 1] 8 (.empty) (.empty)) (.empty)) (.branch [5, 2,
  2, 2] 8 (.empty) (.empty))) (.branch [5, 4] 6 (.branch [5, 3, 3, 3] 8 (.branch [5, 3, 3] 7 (.empty)
  (.empty)) (.empty)) (.branch [5, 4, 1] 7 (.empty) (.empty)))) (.branch [5, 4, 3] 7 (.branch [5, 4, 2, 2] 8
  (.branch [5, 4, 2] 7 (.branch [5, 4, 1, 1, 1] 9 (.empty) (.empty)) (.empty)) (.branch [5, 4, 2, 2, 2] 9
  (.empty) (.empty))) (.branch [5, 4, 4] 7 (.branch [5, 4, 3, 3, 3] 9 (.branch [5, 4, 3, 3] 8 (.empty)
  (.empty)) (.empty)) (.branch [5, 4, 4, 1] 8 (.empty) (.empty))))) (.branch [5, 4, 4, 4, 1, 1] 10 (.branch
  [5, 4, 4, 3] 8 (.branch [5, 4, 4, 2, 2] 9 (.branch [5, 4, 4, 2] 8 (.branch [5, 4, 4, 1, 1, 1] 10 (.empty)
  (.empty)) (.empty)) (.branch [5, 4, 4, 2, 2, 2] 10 (.empty) (.empty))) (.branch [5, 4, 4, 4] 8 (.branch [5,
  4, 4, 3, 3, 3] 10 (.branch [5, 4, 4, 3, 3] 9 (.empty) (.empty)) (.empty)) (.branch [5, 4, 4, 4, 1] 9
  (.empty) (.empty)))) (.branch [5, 4, 4, 4, 3] 9 (.branch [5, 4, 4, 4, 2, 2] 10 (.branch [5, 4, 4, 4, 2] 9
  (.branch [5, 4, 4, 4, 1, 1, 1] 11 (.empty) (.empty)) (.empty)) (.branch [5, 4, 4, 4, 2, 2, 2] 11 (.empty)
  (.empty))) (.branch [5, 4, 4, 4, 3, 3, 3] 11 (.branch [5, 4, 4, 4, 3, 3] 10 (.empty) (.empty)) (.branch [5,
  4, 4, 4, 4] 9 (.empty) (.empty))))))) (.branch [5, 5, 4, 4, 4, 3, 3] 11 (.branch [5, 5, 4, 3, 3] 1 (.branch
  [5, 5, 3, 3] 8 (.branch [5, 5, 1, 1, 1] 9 (.branch [5, 5, 1] 7 (.branch [5, 5] 6 (.branch [5, 4, 4, 4, 4,
  4, 4] 11 (.empty) (.empty)) (.empty)) (.branch [5, 5, 1, 1] 8 (.empty) (.empty))) (.branch [5, 5, 2, 2, 2]
  3 (.branch [5, 5, 2, 2] 8 (.branch [5, 5, 2] 7 (.empty) (.empty)) (.empty)) (.branch [5, 5, 3] 7 (.empty)
  (.empty)))) (.branch [5, 5, 4, 1, 1, 1] 10 (.branch [5, 5, 4, 1] 8 (.branch [5, 5, 4] 7 (.branch [5, 5, 3,
  3, 3] 9 (.empty) (.empty)) (.empty)) (.branch [5, 5, 4, 1, 1] 9 (.empty) (.empty))) (.branch [5, 5, 4, 2,
  2, 2] 10 (.branch [5, 5, 4, 2, 2] 9 (.branch [5, 5, 4, 2] 8 (.empty) (.empty)) (.empty)) (.branch [5, 5, 4,
  3] 8 (.empty) (.empty))))) (.branch [5, 5, 4, 4, 3, 3] 10 (.branch [5, 5, 4, 4, 1, 1, 1] 11 (.branch [5, 5,
  4, 4, 1] 9 (.branch [5, 5, 4, 4] 8 (.branch [5, 5, 4, 3, 3, 3] 10 (.empty) (.empty)) (.empty)) (.branch [5,
  5, 4, 4, 1, 1] 10 (.empty) (.empty))) (.branch [5, 5, 4, 4, 2, 2, 2] 11 (.branch [5, 5, 4, 4, 2, 2] 10
  (.branch [5, 5, 4, 4, 2] 1 (.empty) (.empty)) (.empty)) (.branch [5, 5, 4, 4, 3] 1 (.empty) (.empty))))
  (.branch [5, 5, 4, 4, 4, 1, 1, 1] 12 (.branch [5, 5, 4, 4, 4, 1] 10 (.branch [5, 5, 4, 4, 4] 1 (.branch [5,
  5, 4, 4, 3, 3, 3] 11 (.empty) (.empty)) (.empty)) (.branch [5, 5, 4, 4, 4, 1, 1] 11 (.empty) (.empty)))
  (.branch [5, 5, 4, 4, 4, 2, 2, 2] 12 (.branch [5, 5, 4, 4, 4, 2, 2] 11 (.branch [5, 5, 4, 4, 4, 2] 10
  (.empty) (.empty)) (.empty)) (.branch [5, 5, 4, 4, 4, 3] 10 (.empty) (.empty)))))) (.branch [5, 5, 5, 5, 3,
  3] 2 (.branch [5, 5, 5, 3, 3] 1 (.branch [5, 5, 5] 7 (.branch [5, 5, 4, 4, 4, 4, 4] 11 (.branch [5, 5, 4,
  4, 4, 4] 10 (.branch [5, 5, 4, 4, 4, 3, 3, 3] 12 (.empty) (.empty)) (.empty)) (.branch [5, 5, 4, 4, 4, 4,
  4, 4] 12 (.empty) (.empty))) (.branch [5, 5, 5, 2, 2, 2] 10 (.branch [5, 5, 5, 2, 2] 9 (.branch [5, 5, 5,
  2] 8 (.empty) (.empty)) (.empty)) (.branch [5, 5, 5, 3] 8 (.empty) (.empty)))) (.branch [5, 5, 5, 5] 8
  (.branch [5, 5, 5, 4, 4] 1 (.branch [5, 5, 5, 4] 8 (.branch [5, 5, 5, 3, 3, 3] 2 (.empty) (.empty))
  (.empty)) (.branch [5, 5, 5, 4, 4, 4] 10 (.empty) (.empty))) (.branch [5, 5, 5, 5, 2, 2, 2] 11 (.branch [5,
  5, 5, 5, 2, 2] 10 (.branch [5, 5, 5, 5, 2] 1 (.empty) (.empty)) (.empty)) (.branch [5, 5, 5, 5, 3] 1
  (.empty) (.empty))))) (.branch [5, 5, 5, 5, 5, 3, 3] 11 (.branch [5, 5, 5, 5, 5] 1 (.branch [5, 5, 5, 5, 4,
  4] 2 (.branch [5, 5, 5, 5, 4] 1 (.branch [5, 5, 5, 5, 3, 3, 3] 11 (.empty) (.empty)) (.empty)) (.branch [5,
  5, 5, 5, 4, 4, 4] 11 (.empty) (.empty))) (.branch [5, 5, 5, 5, 5, 2, 2, 2] 12 (.branch [5, 5, 5, 5, 5, 2,
  2] 4 (.branch [5, 5, 5, 5, 5, 2] 3 (.empty) (.empty)) (.empty)) (.branch [5, 5, 5, 5, 5, 3] 2 (.empty)
  (.empty)))) (.branch [5, 5, 5, 5, 5, 5] 2 (.branch [5, 5, 5, 5, 5, 4, 4] 11 (.branch [5, 5, 5, 5, 5, 4] 2
  (.branch [5, 5, 5, 5, 5, 3, 3, 3] 12 (.empty) (.empty)) (.empty)) (.branch [5, 5, 5, 5, 5, 4, 4, 4] 12
  (.empty) (.empty))) (.branch [5, 5, 5, 5, 5, 5, 5, 5] 4 (.branch [5, 5, 5, 5, 5, 5, 5] 3 (.empty) (.empty))
  (.branch [6] 6 (.empty) (.empty))))))))) (.branch [7, 7, 3, 3, 3] 11 (.branch [6, 6, 5, 5, 5, 4] 1 (.branch
  [6, 5, 5, 5, 5, 5] 3 (.branch [6, 5, 5, 2] 9 (.branch [6, 5, 2] 8 (.branch [6, 3, 3, 3] 9 (.branch [6, 3] 7
  (.branch [6, 2, 2, 2] 9 (.branch [6, 2, 2] 8 (.empty) (.empty)) (.empty)) (.branch [6, 3, 3] 8 (.empty)
  (.empty))) (.branch [6, 4, 4, 4] 9 (.branch [6, 4, 4] 8 (.branch [6, 4] 7 (.empty) (.empty)) (.empty))
  (.branch [6, 5] 7 (.empty) (.empty)))) (.branch [6, 5, 3, 3, 3] 10 (.branch [6, 5, 3] 8 (.branch [6, 5, 2,
  2, 2] 10 (.branch [6, 5, 2, 2] 9 (.empty) (.empty)) (.empty)) (.branch [6, 5, 3, 3] 9 (.empty) (.empty)))
  (.branch [6, 5, 4, 4, 4] 10 (.branch [6, 5, 4, 4] 9 (.branch [6, 5, 4] 8 (.empty) (.empty)) (.empty))
  (.branch [6, 5, 5] 8 (.empty) (.empty))))) (.branch [6, 5, 5, 5, 2] 10 (.branch [6, 5, 5, 3, 3, 3] 11
  (.branch [6, 5, 5, 3] 9 (.branch [6, 5, 5, 2, 2, 2] 11 (.branch [6, 5, 5, 2, 2] 10 (.empty) (.empty))
  (.empty)) (.branch [6, 5, 5, 3, 3] 2 (.empty) (.empty))) (.branch [6, 5, 5, 4, 4, 4] 11 (.branch [6, 5, 5,
  4, 4] 2 (.branch [6, 5, 5, 4] 9 (.empty) (.empty)) (.empty)) (.branch [6, 5, 5, 5] 9 (.empty) (.empty))))
  (.branch [6, 5, 5, 5, 3, 3, 3] 12 (.branch [6, 5, 5, 5, 3] 2 (.branch [6, 5, 5, 5, 2, 2, 2] 12 (.branch [6,
  5, 5, 5, 2, 2] 11 (.empty) (.empty)) (.empty)) (.branch [6, 5, 5, 5, 3, 3] 11 (.empty) (.empty))) (.branch
  [6, 5, 5, 5, 4, 4, 4] 12 (.branch [6, 5, 5, 5, 4, 4] 11 (.branch [6, 5, 5, 5, 4] 2 (.empty) (.empty))
  (.empty)) (.branch [6, 5, 5, 5, 5] 2 (.empty) (.empty)))))) (.branch [6, 6, 5, 4, 4] 10 (.branch [6, 6, 4,
  4] 9 (.branch [6, 6, 2, 2, 2] 10 (.branch [6, 6, 2] 8 (.branch [6, 6] 5 (.branch [6, 5, 5, 5, 5, 5, 5] 4
  (.empty) (.empty)) (.empty)) (.branch [6, 6, 2, 2] 9 (.empty) (.empty))) (.branch [6, 6, 3, 3, 3] 10
  (.branch [6, 6, 3, 3] 9 (.branch [6, 6, 3] 8 (.empty) (.empty)) (.empty)) (.branch [6, 6, 4] 8 (.empty)
  (.empty)))) (.branch [6, 6, 5, 2, 2, 2] 11 (.branch [6, 6, 5, 2] 9 (.branch [6, 6, 5] 8 (.branch [6, 6, 4,
  4, 4] 10 (.empty) (.empty)) (.empty)) (.branch [6, 6, 5, 2, 2] 10 (.empty) (.empty))) (.branch [6, 6, 5, 3,
  3, 3] 11 (.branch [6, 6, 5, 3, 3] 10 (.branch [6, 6, 5, 3] 9 (.empty) (.empty)) (.empty)) (.branch [6, 6,
  5, 4] 9 (.empty) (.empty))))) (.branch [6, 6, 5, 5, 4, 4] 1 (.branch [6, 6, 5, 5, 2, 2, 2] 12 (.branch [6,
  6, 5, 5, 2] 10 (.branch [6, 6, 5, 5] 9 (.branch [6, 6, 5, 4, 4, 4] 1 (.empty) (.empty)) (.empty)) (.branch
  [6, 6, 5, 5, 2, 2] 11 (.empty) (.empty))) (.branch [6, 6, 5, 5, 3, 3, 3] 12 (.branch [6, 6, 5, 5, 3, 3] 1
  (.branch [6, 6, 5, 5, 3] 10 (.empty) (.empty)) (.empty)) (.branch [6, 6, 5, 5, 4] 3 (.empty) (.empty))))
  (.branch [6, 6, 5, 5, 5, 2, 2, 2] 13 (.branch [6, 6, 5, 5, 5, 2] 1 (.branch [6, 6, 5, 5, 5] 3 (.branch [6,
  6, 5, 5, 4, 4, 4] 12 (.empty) (.empty)) (.empty)) (.branch [6, 6, 5, 5, 5, 2, 2] 12 (.empty) (.empty)))
  (.branch [6, 6, 5, 5, 5, 3, 3] 12 (.branch [6, 6, 5, 5, 5, 3] 1 (.empty) (.empty)) (.branch [6, 6, 5, 5, 5,
  3, 3, 3] 13 (.empty) (.empty))))))) (.branch [7, 4] 8 (.branch [6, 6, 6, 6, 4] 2 (.branch [6, 6, 6, 4] 9
  (.branch [6, 6, 5, 5, 5, 5, 5, 5] 13 (.branch [6, 6, 5, 5, 5, 5] 1 (.branch [6, 6, 5, 5, 5, 4, 4, 4] 13
  (.branch [6, 6, 5, 5, 5, 4, 4] 12 (.empty) (.empty)) (.empty)) (.branch [6, 6, 5, 5, 5, 5, 5] 4 (.empty)
  (.empty))) (.branch [6, 6, 6, 3, 3] 2 (.branch [6, 6, 6, 3] 9 (.branch [6, 6, 6] 8 (.empty) (.empty))
  (.empty)) (.branch [6, 6, 6, 3, 3, 3] 11 (.empty) (.empty)))) (.branch [6, 6, 6, 5, 5, 5] 1 (.branch [6, 6,
  6, 5] 9 (.branch [6, 6, 6, 4, 4, 4] 1 (.branch [6, 6, 6, 4, 4] 2 (.empty) (.empty)) (.empty)) (.branch [6,
  6, 6, 5, 5] 2 (.empty) (.empty))) (.branch [6, 6, 6, 6, 3, 3] 1 (.branch [6, 6, 6, 6, 3] 10 (.branch [6, 6,
  6, 6] 7 (.empty) (.empty)) (.empty)) (.branch [6, 6, 6, 6, 3, 3, 3] 12 (.empty) (.empty))))) (.branch [6,
  6, 6, 6, 6, 4] 1 (.branch [6, 6, 6, 6, 5, 5, 5] 12 (.branch [6, 6, 6, 6, 5] 2 (.branch [6, 6, 6, 6, 4, 4,
  4] 12 (.branch [6, 6, 6, 6, 4, 4] 1 (.empty) (.empty)) (.empty)) (.branch [6, 6, 6, 6, 5, 5] 1 (.empty)
  (.empty))) (.branch [6, 6, 6, 6, 6, 3, 3] 12 (.branch [6, 6, 6, 6, 6, 3] 1 (.branch [6, 6, 6, 6, 6] 2
  (.empty) (.empty)) (.empty)) (.branch [6, 6, 6, 6, 6, 3, 3, 3] 13 (.empty) (.empty)))) (.branch [6, 6, 6,
  6, 6, 5, 5, 5] 13 (.branch [6, 6, 6, 6, 6, 5] 1 (.branch [6, 6, 6, 6, 6, 4, 4, 4] 13 (.branch [6, 6, 6, 6,
  6, 4, 4] 12 (.empty) (.empty)) (.empty)) (.branch [6, 6, 6, 6, 6, 5, 5] 4 (.empty) (.empty))) (.branch [7,
  3, 3] 9 (.branch [7, 3] 8 (.branch [7] 7 (.empty) (.empty)) (.empty)) (.branch [7, 3, 3, 3] 10 (.empty)
  (.empty)))))) (.branch [7, 6, 6, 4] 10 (.branch [7, 6, 4] 9 (.branch [7, 5, 5, 5] 10 (.branch [7, 5] 8
  (.branch [7, 4, 4, 4] 10 (.branch [7, 4, 4] 9 (.empty) (.empty)) (.empty)) (.branch [7, 5, 5] 9 (.empty)
  (.empty))) (.branch [7, 6, 3, 3] 10 (.branch [7, 6, 3] 9 (.branch [7, 6] 8 (.empty) (.empty)) (.empty))
  (.branch [7, 6, 3, 3, 3] 11 (.empty) (.empty)))) (.branch [7, 6, 5, 5, 5] 4 (.branch [7, 6, 5] 9 (.branch
  [7, 6, 4, 4, 4] 11 (.branch [7, 6, 4, 4] 10 (.empty) (.empty)) (.empty)) (.branch [7, 6, 5, 5] 10 (.empty)
  (.empty))) (.branch [7, 6, 6, 3, 3] 11 (.branch [7, 6, 6, 3] 10 (.branch [7, 6, 6] 9 (.empty) (.empty))
  (.empty)) (.branch [7, 6, 6, 3, 3, 3] 12 (.empty) (.empty))))) (.branch [7, 6, 6, 6, 4] 11 (.branch [7, 6,
  6, 5, 5, 5] 12 (.branch [7, 6, 6, 5] 10 (.branch [7, 6, 6, 4, 4, 4] 12 (.branch [7, 6, 6, 4, 4] 11 (.empty)
  (.empty)) (.empty)) (.branch [7, 6, 6, 5, 5] 11 (.empty) (.empty))) (.branch [7, 6, 6, 6, 3, 3] 12 (.branch
  [7, 6, 6, 6, 3] 11 (.branch [7, 6, 6, 6] 10 (.empty) (.empty)) (.empty)) (.branch [7, 6, 6, 6, 3, 3, 3] 13
  (.empty) (.empty)))) (.branch [7, 6, 6, 6, 5, 5, 5] 13 (.branch [7, 6, 6, 6, 5] 3 (.branch [7, 6, 6, 6, 4,
  4, 4] 13 (.branch [7, 6, 6, 6, 4, 4] 12 (.empty) (.empty)) (.empty)) (.branch [7, 6, 6, 6, 5, 5] 12
  (.empty) (.empty))) (.branch [7, 7, 3] 9 (.branch [7, 7] 8 (.empty) (.empty)) (.branch [7, 7, 3, 3] 10
  (.empty) (.empty)))))))) (.branch [8, 7, 7, 7] 11 (.branch [7, 7, 7, 4, 4, 4] 12 (.branch [7, 7, 6, 6, 3,
  3, 3] 13 (.branch [7, 7, 6, 3, 3, 3] 12 (.branch [7, 7, 5, 5] 10 (.branch [7, 7, 4, 4, 4] 11 (.branch [7,
  7, 4, 4] 10 (.branch [7, 7, 4] 9 (.empty) (.empty)) (.empty)) (.branch [7, 7, 5] 9 (.empty) (.empty)))
  (.branch [7, 7, 6, 3] 10 (.branch [7, 7, 6] 5 (.branch [7, 7, 5, 5, 5] 4 (.empty) (.empty)) (.empty))
  (.branch [7, 7, 6, 3, 3] 11 (.empty) (.empty)))) (.branch [7, 7, 6, 5, 5] 11 (.branch [7, 7, 6, 4, 4, 4] 12
  (.branch [7, 7, 6, 4, 4] 11 (.branch [7, 7, 6, 4] 10 (.empty) (.empty)) (.empty)) (.branch [7, 7, 6, 5] 10
  (.empty) (.empty))) (.branch [7, 7, 6, 6, 3] 11 (.branch [7, 7, 6, 6] 10 (.branch [7, 7, 6, 5, 5, 5] 12
  (.empty) (.empty)) (.empty)) (.branch [7, 7, 6, 6, 3, 3] 12 (.empty) (.empty))))) (.branch [7, 7, 6, 6, 6,
  3, 3, 3] 14 (.branch [7, 7, 6, 6, 5, 5] 3 (.branch [7, 7, 6, 6, 4, 4, 4] 1 (.branch [7, 7, 6, 6, 4, 4] 12
  (.branch [7, 7, 6, 6, 4] 11 (.empty) (.empty)) (.empty)) (.branch [7, 7, 6, 6, 5] 11 (.empty) (.empty)))
  (.branch [7, 7, 6, 6, 6, 3] 12 (.branch [7, 7, 6, 6, 6] 4 (.branch [7, 7, 6, 6, 5, 5, 5] 1 (.empty)
  (.empty)) (.empty)) (.branch [7, 7, 6, 6, 6, 3, 3] 1 (.empty) (.empty)))) (.branch [7, 7, 6, 6, 6, 5, 5] 1
  (.branch [7, 7, 6, 6, 6, 4, 4, 4] 14 (.branch [7, 7, 6, 6, 6, 4, 4] 1 (.branch [7, 7, 6, 6, 6, 4] 3
  (.empty) (.empty)) (.empty)) (.branch [7, 7, 6, 6, 6, 5] 12 (.empty) (.empty))) (.branch [7, 7, 7, 4] 10
  (.branch [7, 7, 7] 5 (.branch [7, 7, 6, 6, 6, 5, 5, 5] 14 (.empty) (.empty)) (.empty)) (.branch [7, 7, 7,
  4, 4] 11 (.empty) (.empty)))))) (.branch [8, 4, 4] 10 (.branch [7, 7, 7, 7, 5, 5, 5] 1 (.branch [7, 7, 7,
  7, 4] 11 (.branch [7, 7, 7, 5, 5, 5] 12 (.branch [7, 7, 7, 5, 5] 11 (.branch [7, 7, 7, 5] 10 (.empty)
  (.empty)) (.empty)) (.branch [7, 7, 7, 7] 6 (.empty) (.empty))) (.branch [7, 7, 7, 7, 5] 11 (.branch [7, 7,
  7, 7, 4, 4, 4] 1 (.branch [7, 7, 7, 7, 4, 4] 12 (.empty) (.empty)) (.empty)) (.branch [7, 7, 7, 7, 5, 5] 12
  (.empty) (.empty)))) (.branch [7, 7, 7, 7, 7, 5] 4 (.branch [7, 7, 7, 7, 7, 4, 4] 1 (.branch [7, 7, 7, 7,
  7, 4] 12 (.branch [7, 7, 7, 7, 7] 3 (.empty) (.empty)) (.empty)) (.branch [7, 7, 7, 7, 7, 4, 4, 4] 14
  (.empty) (.empty))) (.branch [8] 8 (.branch [7, 7, 7, 7, 7, 5, 5, 5] 2 (.branch [7, 7, 7, 7, 7, 5, 5] 1
  (.empty) (.empty)) (.empty)) (.branch [8, 4] 9 (.empty) (.empty))))) (.branch [8, 7, 5, 5] 11 (.branch [8,
  7] 9 (.branch [8, 5, 5] 10 (.branch [8, 5] 9 (.branch [8, 4, 4, 4] 11 (.empty) (.empty)) (.empty)) (.branch
  [8, 5, 5, 5] 11 (.empty) (.empty))) (.branch [8, 7, 4, 4, 4] 12 (.branch [8, 7, 4, 4] 11 (.branch [8, 7, 4]
  10 (.empty) (.empty)) (.empty)) (.branch [8, 7, 5] 10 (.empty) (.empty)))) (.branch [8, 7, 7, 4, 4, 4] 13
  (.branch [8, 7, 7, 4] 11 (.branch [8, 7, 7] 6 (.branch [8, 7, 5, 5, 5] 12 (.empty) (.empty)) (.empty))
  (.branch [8, 7, 7, 4, 4] 12 (.empty) (.empty))) (.branch [8, 7, 7, 5, 5] 12 (.branch [8, 7, 7, 5] 11
  (.empty) (.empty)) (.branch [8, 7, 7, 5, 5, 5] 13 (.empty) (.empty))))))) (.branch [8, 8, 8, 8, 5] 12
  (.branch [8, 8, 7, 5, 5, 5] 13 (.branch [8, 8, 4, 4, 4] 12 (.branch [8, 7, 7, 7, 5, 5] 13 (.branch [8, 7,
  7, 7, 4, 4, 4] 14 (.branch [8, 7, 7, 7, 4, 4] 13 (.branch [8, 7, 7, 7, 4] 12 (.empty) (.empty)) (.empty))
  (.branch [8, 7, 7, 7, 5] 12 (.empty) (.empty))) (.branch [8, 8, 4] 10 (.branch [8, 8] 7 (.branch [8, 7, 7,
  7, 5, 5, 5] 2 (.empty) (.empty)) (.empty)) (.branch [8, 8, 4, 4] 11 (.empty) (.empty)))) (.branch [8, 8, 7,
  4] 11 (.branch [8, 8, 5, 5, 5] 12 (.branch [8, 8, 5, 5] 11 (.branch [8, 8, 5] 10 (.empty) (.empty))
  (.empty)) (.branch [8, 8, 7] 10 (.empty) (.empty))) (.branch [8, 8, 7, 5] 11 (.branch [8, 8, 7, 4, 4, 4] 13
  (.branch [8, 8, 7, 4, 4] 12 (.empty) (.empty)) (.empty)) (.branch [8, 8, 7, 5, 5] 12 (.empty) (.empty)))))
  (.branch [8, 8, 7, 7, 7, 4, 4] 14 (.branch [8, 8, 7, 7, 5] 12 (.branch [8, 8, 7, 7, 4, 4] 13 (.branch [8,
  8, 7, 7, 4] 12 (.branch [8, 8, 7, 7] 11 (.empty) (.empty)) (.empty)) (.branch [8, 8, 7, 7, 4, 4, 4] 14
  (.empty) (.empty))) (.branch [8, 8, 7, 7, 7] 12 (.branch [8, 8, 7, 7, 5, 5, 5] 14 (.branch [8, 8, 7, 7, 5,
  5] 13 (.empty) (.empty)) (.empty)) (.branch [8, 8, 7, 7, 7, 4] 13 (.empty) (.empty)))) (.branch [8, 8, 8] 6
  (.branch [8, 8, 7, 7, 7, 5, 5] 14 (.branch [8, 8, 7, 7, 7, 5] 13 (.branch [8, 8, 7, 7, 7, 4, 4, 4] 1
  (.empty) (.empty)) (.empty)) (.branch [8, 8, 7, 7, 7, 5, 5, 5] 1 (.empty) (.empty))) (.branch [8, 8, 8, 5,
  5, 5] 13 (.branch [8, 8, 8, 5, 5] 12 (.branch [8, 8, 8, 5] 11 (.empty) (.empty)) (.empty)) (.branch [8, 8,
  8, 8] 5 (.empty) (.empty)))))) (.branch [9, 8, 8, 8, 5] 13 (.branch [9, 5, 5, 5] 12 (.branch [8, 8, 8, 8,
  8, 5, 5] 2 (.branch [8, 8, 8, 8, 8] 4 (.branch [8, 8, 8, 8, 5, 5, 5] 14 (.branch [8, 8, 8, 8, 5, 5] 13
  (.empty) (.empty)) (.empty)) (.branch [8, 8, 8, 8, 8, 5] 13 (.empty) (.empty))) (.branch [9, 5] 10 (.branch
  [9] 9 (.branch [8, 8, 8, 8, 8, 5, 5, 5] 1 (.empty) (.empty)) (.empty)) (.branch [9, 5, 5] 11 (.empty)
  (.empty)))) (.branch [9, 8, 8] 11 (.branch [9, 8, 5, 5] 12 (.branch [9, 8, 5] 11 (.branch [9, 8] 10
  (.empty) (.empty)) (.empty)) (.branch [9, 8, 5, 5, 5] 13 (.empty) (.empty))) (.branch [9, 8, 8, 5, 5, 5] 14
  (.branch [9, 8, 8, 5, 5] 13 (.branch [9, 8, 8, 5] 12 (.empty) (.empty)) (.empty)) (.branch [9, 8, 8, 8] 12
  (.empty) (.empty))))) (.branch [9, 9, 8, 5, 5, 5] 14 (.branch [9, 9, 5, 5] 12 (.branch [9, 9] 10 (.branch
  [9, 8, 8, 8, 5, 5, 5] 15 (.branch [9, 8, 8, 8, 5, 5] 14 (.empty) (.empty)) (.empty)) (.branch [9, 9, 5] 11
  (.empty) (.empty))) (.branch [9, 9, 8, 5] 12 (.branch [9, 9, 8] 11 (.branch [9, 9, 5, 5, 5] 13 (.empty)
  (.empty)) (.empty)) (.branch [9, 9, 8, 5, 5] 13 (.empty) (.empty)))) (.branch [9, 9, 8, 8, 8] 13 (.branch
  [9, 9, 8, 8, 5, 5] 14 (.branch [9, 9, 8, 8, 5] 13 (.branch [9, 9, 8, 8] 12 (.empty) (.empty)) (.empty))
  (.branch [9, 9, 8, 8, 5, 5, 5] 15 (.empty) (.empty))) (.branch [9, 9, 8, 8, 8, 5, 5] 15 (.branch [9, 9, 8,
  8, 8, 5] 14 (.empty) (.empty)) (.branch [9, 9, 8, 8, 8, 5, 5, 5] 3 (.empty) (.empty)))))))))

private def rectangleCertificate : Certificate :=
  .branch [5, 5, 5, 5] 8 (.branch [3, 3] 4 (.branch [2] 2 (.branch [1, 1, 1, 1] 4 (.branch [1, 1] 2 (.branch
  [1] 1 (.branch [] 0 (.empty) (.empty)) (.empty)) (.branch [1, 1, 1] 3 (.empty) (.empty))) (.branch [1, 1,
  1, 1, 1, 1, 1] 7 (.branch [1, 1, 1, 1, 1, 1] 6 (.branch [1, 1, 1, 1, 1] 5 (.empty) (.empty)) (.empty))
  (.branch [1, 1, 1, 1, 1, 1, 1, 1] 8 (.empty) (.empty)))) (.branch [2, 2, 2, 2, 2, 2] 5 (.branch [2, 2, 2,
  2] 3 (.branch [2, 2, 2] 4 (.branch [2, 2] 1 (.empty) (.empty)) (.empty)) (.branch [2, 2, 2, 2, 2] 6
  (.empty) (.empty))) (.branch [2, 2, 2, 2, 2, 2, 2, 2] 7 (.branch [2, 2, 2, 2, 2, 2, 2] 8 (.empty) (.empty))
  (.branch [3] 3 (.empty) (.empty))))) (.branch [4, 4, 4] 2 (.branch [3, 3, 3, 3, 3, 3, 3] 5 (.branch [3, 3,
  3, 3, 3] 7 (.branch [3, 3, 3, 3] 2 (.branch [3, 3, 3] 1 (.empty) (.empty)) (.empty)) (.branch [3, 3, 3, 3,
  3, 3] 8 (.empty) (.empty))) (.branch [4] 4 (.branch [3, 3, 3, 3, 3, 3, 3, 3] 6 (.empty) (.empty)) (.branch
  [4, 4] 3 (.empty) (.empty)))) (.branch [4, 4, 4, 4, 4, 4, 4, 4] 5 (.branch [4, 4, 4, 4, 4, 4] 7 (.branch
  [4, 4, 4, 4, 4] 8 (.branch [4, 4, 4, 4] 1 (.empty) (.empty)) (.empty)) (.branch [4, 4, 4, 4, 4, 4, 4] 6
  (.empty) (.empty))) (.branch [5, 5] 6 (.branch [5] 5 (.empty) (.empty)) (.branch [5, 5, 5] 7 (.empty)
  (.empty)))))) (.branch [7, 7, 7, 7, 7, 7, 7] 1 (.branch [6, 6, 6, 6, 6, 6] 1 (.branch [6] 6 (.branch [5, 5,
  5, 5, 5, 5, 5] 3 (.branch [5, 5, 5, 5, 5, 5] 2 (.branch [5, 5, 5, 5, 5] 1 (.empty) (.empty)) (.empty))
  (.branch [5, 5, 5, 5, 5, 5, 5, 5] 4 (.empty) (.empty))) (.branch [6, 6, 6, 6] 7 (.branch [6, 6, 6] 8
  (.branch [6, 6] 5 (.empty) (.empty)) (.empty)) (.branch [6, 6, 6, 6, 6] 2 (.empty) (.empty)))) (.branch [7,
  7, 7] 5 (.branch [7] 7 (.branch [6, 6, 6, 6, 6, 6, 6, 6] 3 (.branch [6, 6, 6, 6, 6, 6, 6] 4 (.empty)
  (.empty)) (.empty)) (.branch [7, 7] 8 (.empty) (.empty))) (.branch [7, 7, 7, 7, 7] 3 (.branch [7, 7, 7, 7]
  6 (.empty) (.empty)) (.branch [7, 7, 7, 7, 7, 7] 4 (.empty) (.empty))))) (.branch [8, 8, 8, 8, 8, 8, 8, 8]
  1 (.branch [8, 8, 8, 8] 5 (.branch [8, 8] 7 (.branch [8] 8 (.branch [7, 7, 7, 7, 7, 7, 7, 7] 2 (.empty)
  (.empty)) (.empty)) (.branch [8, 8, 8] 6 (.empty) (.empty))) (.branch [8, 8, 8, 8, 8, 8] 3 (.branch [8, 8,
  8, 8, 8] 4 (.empty) (.empty)) (.branch [8, 8, 8, 8, 8, 8, 8] 2 (.empty) (.empty)))) (.branch [9, 9, 9, 9,
  9] 13 (.branch [9, 9, 9] 11 (.branch [9, 9] 10 (.branch [9] 9 (.empty) (.empty)) (.empty)) (.branch [9, 9,
  9, 9] 12 (.empty) (.empty))) (.branch [9, 9, 9, 9, 9, 9, 9] 15 (.branch [9, 9, 9, 9, 9, 9] 14 (.empty)
  (.empty)) (.branch [9, 9, 9, 9, 9, 9, 9, 9] 16 (.empty) (.empty))))))

set_option maxHeartbeats 20000000 in
/-- A finite a=8, b=7 counterexample refutes the fully quantified conjecture. -/
theorem result : ¬ claim := by
  have witnessChecked :
      (domain witnessCertificate).all (check witnessCertificate) = true := by
    conv => lhs; arg 1; reduce
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have rectangleChecked :
      (domain rectangleCertificate).all (check rectangleCertificate) = true := by
    conv => lhs; arg 1; reduce
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
    repeat' apply And.intro
    all_goals decide +kernel
  have witnessValue : grundy [9, 9, 8, 8, 8, 5, 5, 5] = 3 := by
    calc
      _ = value witnessCertificate [9, 9, 8, 8, 8, 5, 5, 5] :=
        certificate_correct witnessCertificate witnessChecked _ (by decide +kernel)
      _ = 3 := by decide +kernel
  have rectangleValue : grundy [9, 9, 9, 9, 9, 9, 9, 9] = 16 := by
    calc
      _ = value rectangleCertificate [9, 9, 9, 9, 9, 9, 9, 9] :=
        certificate_correct rectangleCertificate rectangleChecked _ (by decide +kernel)
      _ = 16 := by decide +kernel
  intro h
  have rectangleHeavy : heavy (rectangle 8 7) := by
    constructor
    · decide
    · change grundy [9, 9, 9, 9, 9, 9, 9, 9] = 16
      exact rectangleValue
  have witnessHeavy : heavy [9, 9, 8, 8, 8, 5, 5, 5] :=
    h 8 7 (by decide) rectangleHeavy _ (by decide) (by decide) (by decide)
  have predicted : grundy [9, 9, 8, 8, 8, 5, 5, 5] = 16 := witnessHeavy.2
  omega

#print axioms claim
#print axioms result

end D5.S0.Certificates.Games.PnimHeavyIntervalRefutation
