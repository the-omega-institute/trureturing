/- GID: D5/S3/Combinatorics/Transportation/SupportedCycleSupplier
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/SupportedCycleSupplier
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Pigeonhole]
   utility: none
   digest: Fixed Boolean margins supply a simple cycle of target disagreements. -/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! Unequal Boolean tables in one labeled margin fiber contain a simple
alternating cycle of positive and negative target disagreements. -/

/-
Source: https://github.com/guanyangwang/ktv-swap-lean/tree/15b5f47c9ac833bfdf99b8b29374af7a678ef4bc
Original modules: KTV.Johnson.BinaryMatrix.Basic, KTV.Johnson.BinaryMatrix.Proposals,
KTV.Johnson.Connectivity. The consumed cycle-extraction closure is retained;
module layout, visibility and imports are adapted to this repository.
Retirement: replace this port by direct imports when this repository's pinned
mathlib contains equivalent fixed-margin simple disagreement-cycle extraction.

MIT License

Copyright (c) 2026 Guanyang Wang

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/

namespace D5.S3.Combinatorics.Transportation.SupportedCycleSupplier
variable {Row Col : Type*} [Fintype Row] [DecidableEq Row]
  [Fintype Col] [DecidableEq Col]

abbrev BinaryMatrix (Row Col : Type*) := Row → Col → Bool

def rowSum (X : BinaryMatrix Row Col) (r : Row) : Nat :=
  (Finset.univ.filter fun c : Col => X r c = true).card

def colSum (X : BinaryMatrix Row Col) (c : Col) : Nat :=
  (Finset.univ.filter fun r : Row => X r c = true).card

structure FixedMarginModel (Row Col : Type*) [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col] where
  rowTarget : Row → Nat
  colTarget : Col → Nat

def FixedMarginModel.IsState (M : FixedMarginModel Row Col)
    (X : BinaryMatrix Row Col) : Prop :=
  (∀ r, rowSum X r = M.rowTarget r) ∧
    ∀ c, colSum X c = M.colTarget c

abbrev FixedMarginState (M : FixedMarginModel Row Col) :=
  {X : BinaryMatrix Row Col // M.IsState X}


abbrev OrderedDistinctPair (α : Type*) := {p : α × α // p.1 ≠ p.2}

omit [Fintype Col] [DecidableEq Col] in
private theorem exists_mem_left_not_right_of_fixedCard_ne
    {A : Finset Col} {k : Nat}
    {S T : {S : Finset Col // S ⊆ A ∧ S.card = k}}
    (hST : S ≠ T) :
    ∃ a : Col, a ∈ S.1 ∧ a ∉ T.1 := by
  classical
  by_contra h
  have hSub : S.1 ⊆ T.1 := by
    intro a haS
    by_contra haT
    exact h ⟨a, haS, haT⟩
  have hCard : S.1.card = T.1.card := by
    rw [S.2.2, T.2.2]
  have hVal : S.1 = T.1 :=
    Finset.eq_of_subset_of_card_le hSub (by omega)
  exact hST (Subtype.ext hVal)

omit [Fintype Col] [DecidableEq Col] in
private theorem exists_mem_right_not_left_of_fixedCard_ne
    {A : Finset Col} {k : Nat}
    {S T : {S : Finset Col // S ⊆ A ∧ S.card = k}}
    (hST : S ≠ T) :
    ∃ b : Col, b ∈ T.1 ∧ b ∉ S.1 := by
  classical
  rcases exists_mem_left_not_right_of_fixedCard_ne
    (A := A) (k := k) (S := T) (T := S) (by
      intro hTS
      exact hST hTS.symm) with ⟨b, hbT, hbS⟩
  exact ⟨b, hbT, hbS⟩


private theorem exists_entry_ne_of_fixedMarginState_ne
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (hXY : X ≠ Y) :
    ∃ r : Row, ∃ c : Col, X.1 r c ≠ Y.1 r c := by
  classical
  by_contra h
  apply hXY
  apply Subtype.ext
  funext r c
  by_contra hne
  exact h ⟨r, c, hne⟩

private theorem exists_row_pos_neg_disagreement_of_entry_ne
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    {r : Row} {c : Col}
    (h : X.1 r c ≠ Y.1 r c) :
    ∃ cpos cneg : Col,
      X.1 r cpos = true ∧ Y.1 r cpos = false ∧
        X.1 r cneg = false ∧ Y.1 r cneg = true := by
  classical
  let SX : Finset Col :=
    (Finset.univ : Finset Col).filter fun d => X.1 r d = true
  let SY : Finset Col :=
    (Finset.univ : Finset Col).filter fun d => Y.1 r d = true
  have hCard : SX.card = SY.card := by
    change rowSum X.1 r = rowSum Y.1 r
    rw [X.2.1 r, Y.2.1 r]
  let S : {S : Finset Col // S ⊆ (Finset.univ : Finset Col) ∧ S.card = SX.card} :=
    ⟨SX, by
      constructor
      · intro d hd
        simp
      · rfl⟩
  let T : {S : Finset Col // S ⊆ (Finset.univ : Finset Col) ∧ S.card = SX.card} :=
    ⟨SY, by
      constructor
      · intro d hd
        simp
      · exact hCard.symm⟩
  cases hXc : X.1 r c <;> cases hYc : Y.1 r c
  · simp [hXc, hYc] at h
  · have hcS : c ∉ S.1 := by
      simp [S, SX, hXc]
    have hcT : c ∈ T.1 := by
      simp [T, SY, hYc]
    have hST : S ≠ T := by
      intro hEq
      exact hcS (by
        have hVal : S.1 = T.1 := congrArg Subtype.val hEq
        simpa [hVal] using hcT)
    rcases exists_mem_left_not_right_of_fixedCard_ne
        (A := (Finset.univ : Finset Col)) (k := SX.card)
        (S := S) (T := T) hST with
      ⟨cpos, hcposS, hcposT⟩
    refine ⟨cpos, c, ?_, ?_, ?_, ?_⟩
    · simpa [S, SX] using hcposS
    · by_cases hy : Y.1 r cpos
      · exact False.elim (hcposT (by simp [T, SY, hy]))
      · simp [hy]
    · exact hXc
    · exact hYc
  · have hcS : c ∈ S.1 := by
      simp [S, SX, hXc]
    have hcT : c ∉ T.1 := by
      simp [T, SY, hYc]
    have hST : S ≠ T := by
      intro hEq
      exact hcT (by
        have hVal : S.1 = T.1 := congrArg Subtype.val hEq
        simpa [← hVal] using hcS)
    rcases exists_mem_right_not_left_of_fixedCard_ne
        (A := (Finset.univ : Finset Col)) (k := SX.card)
        (S := S) (T := T) hST with
      ⟨cneg, hcnegT, hcnegS⟩
    refine ⟨c, cneg, ?_, ?_, ?_, ?_⟩
    · exact hXc
    · exact hYc
    · by_cases hx : X.1 r cneg
      · exact False.elim (hcnegS (by simp [S, SX, hx]))
      · simp [hx]
    · simpa [T, SY] using hcnegT
  · simp [hXc, hYc] at h

private theorem exists_col_pos_neg_disagreement_of_entry_ne
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    {r : Row} {c : Col}
    (h : X.1 r c ≠ Y.1 r c) :
    ∃ rpos rneg : Row,
      X.1 rpos c = true ∧ Y.1 rpos c = false ∧
        X.1 rneg c = false ∧ Y.1 rneg c = true := by
  classical
  let SX : Finset Row :=
    (Finset.univ : Finset Row).filter fun s => X.1 s c = true
  let SY : Finset Row :=
    (Finset.univ : Finset Row).filter fun s => Y.1 s c = true
  have hCard : SX.card = SY.card := by
    change colSum X.1 c = colSum Y.1 c
    rw [X.2.2 c, Y.2.2 c]
  let S : {S : Finset Row // S ⊆ (Finset.univ : Finset Row) ∧ S.card = SX.card} :=
    ⟨SX, by
      constructor
      · intro s hs
        simp
      · rfl⟩
  let T : {S : Finset Row // S ⊆ (Finset.univ : Finset Row) ∧ S.card = SX.card} :=
    ⟨SY, by
      constructor
      · intro s hs
        simp
      · exact hCard.symm⟩
  cases hXr : X.1 r c <;> cases hYr : Y.1 r c
  · simp [hXr, hYr] at h
  · have hrS : r ∉ S.1 := by
      simp [S, SX, hXr]
    have hrT : r ∈ T.1 := by
      simp [T, SY, hYr]
    have hST : S ≠ T := by
      intro hEq
      exact hrS (by
        have hVal : S.1 = T.1 := congrArg Subtype.val hEq
        simpa [hVal] using hrT)
    rcases exists_mem_left_not_right_of_fixedCard_ne
        (A := (Finset.univ : Finset Row)) (k := SX.card)
        (S := S) (T := T) hST with
      ⟨rpos, hrposS, hrposT⟩
    refine ⟨rpos, r, ?_, ?_, ?_, ?_⟩
    · simpa [S, SX] using hrposS
    · by_cases hy : Y.1 rpos c
      · exact False.elim (hrposT (by simp [T, SY, hy]))
      · simp [hy]
    · exact hXr
    · exact hYr
  · have hrS : r ∈ S.1 := by
      simp [S, SX, hXr]
    have hrT : r ∉ T.1 := by
      simp [T, SY, hYr]
    have hST : S ≠ T := by
      intro hEq
      exact hrT (by
        have hVal : S.1 = T.1 := congrArg Subtype.val hEq
        simpa [← hVal] using hrS)
    rcases exists_mem_right_not_left_of_fixedCard_ne
        (A := (Finset.univ : Finset Row)) (k := SX.card)
        (S := S) (T := T) hST with
      ⟨rneg, hrnegT, hrnegS⟩
    refine ⟨r, rneg, ?_, ?_, ?_, ?_⟩
    · exact hXr
    · exact hYr
    · by_cases hx : X.1 rneg c
      · exact False.elim (hrnegS (by simp [S, SX, hx]))
      · simp [hx]
    · simpa [T, SY] using hrnegT
  · simp [hXr, hYr] at h

private theorem exists_row_neg_disagreement_of_pos
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    {r : Row} {cpos : Col}
    (hXpos : X.1 r cpos = true) (hYpos : Y.1 r cpos = false) :
    ∃ cneg : Col, X.1 r cneg = false ∧ Y.1 r cneg = true := by
  have hne : X.1 r cpos ≠ Y.1 r cpos := by
    simp [hXpos, hYpos]
  rcases exists_row_pos_neg_disagreement_of_entry_ne
      (M := M) (X := X) (Y := Y) (r := r) (c := cpos) hne with
    ⟨_cpos', cneg, _hXpos', _hYpos', hXneg, hYneg⟩
  exact ⟨cneg, hXneg, hYneg⟩

private theorem exists_col_pos_disagreement_of_neg
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    {rneg : Row} {c : Col}
    (hXneg : X.1 rneg c = false) (hYneg : Y.1 rneg c = true) :
    ∃ rpos : Row, X.1 rpos c = true ∧ Y.1 rpos c = false := by
  have hne : X.1 rneg c ≠ Y.1 rneg c := by
    simp [hXneg, hYneg]
  rcases exists_col_pos_neg_disagreement_of_entry_ne
      (M := M) (X := X) (Y := Y) (r := rneg) (c := c) hne with
    ⟨rpos, _rneg', hXpos, hYpos, _hXneg', _hYneg'⟩
  exact ⟨rpos, hXpos, hYpos⟩

private theorem exists_alternating_two_step_of_fixedMarginState_ne
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (hXY : X ≠ Y) :
    ∃ p : OrderedDistinctPair Row, ∃ cpos cneg : Col,
      cpos ≠ cneg ∧
        X.1 p.1.1 cpos = true ∧ Y.1 p.1.1 cpos = false ∧
        X.1 p.1.1 cneg = false ∧ Y.1 p.1.1 cneg = true ∧
        X.1 p.1.2 cneg = true ∧ Y.1 p.1.2 cneg = false := by
  classical
  rcases exists_entry_ne_of_fixedMarginState_ne (M := M) hXY with
    ⟨r, c, hrc⟩
  rcases exists_row_pos_neg_disagreement_of_entry_ne
      (M := M) (X := X) (Y := Y) (r := r) (c := c) hrc with
    ⟨cpos, cneg, hXpos, hYpos, hXneg, hYneg⟩
  have hcol : X.1 r cneg ≠ Y.1 r cneg := by
    simp [hXneg, hYneg]
  rcases exists_col_pos_neg_disagreement_of_entry_ne
      (M := M) (X := X) (Y := Y) (r := r) (c := cneg) hcol with
    ⟨rpos, _rneg, hXrpos, hYrpos, _hXrneg, _hYrneg⟩
  have hr_ne : r ≠ rpos := by
    intro hEq
    subst rpos
    simp [hXneg] at hXrpos
  have hc_ne : cpos ≠ cneg := by
    intro hEq
    subst cneg
    simp [hXpos] at hXneg
  refine ⟨⟨(r, rpos), hr_ne⟩, cpos, cneg, hc_ne, ?_⟩
  exact ⟨hXpos, hYpos, hXneg, hYneg, hXrpos, hYrpos⟩

def fixedMarginPositiveDisagreement
    {M : FixedMarginModel Row Col}
    (X Y : FixedMarginState M) : Type _ :=
  {rc : Row × Col // X.1 rc.1 rc.2 = true ∧ Y.1 rc.1 rc.2 = false}

noncomputable instance fixedMarginPositiveDisagreement_fintype
    {M : FixedMarginModel Row Col}
    (X Y : FixedMarginState M) :
    Fintype (fixedMarginPositiveDisagreement (M := M) X Y) := by
  classical
  unfold fixedMarginPositiveDisagreement
  infer_instance

noncomputable def fixedMarginPositiveDisagreement_nextNegCol
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (a : fixedMarginPositiveDisagreement (M := M) X Y) : Col :=
  Classical.choose
    (exists_row_neg_disagreement_of_pos
      (M := M) (X := X) (Y := Y) (r := a.1.1) (cpos := a.1.2)
      a.2.1 a.2.2)

private theorem fixedMarginPositiveDisagreement_nextNegCol_spec
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (a : fixedMarginPositiveDisagreement (M := M) X Y) :
    X.1 a.1.1 (fixedMarginPositiveDisagreement_nextNegCol (M := M) a) = false ∧
      Y.1 a.1.1 (fixedMarginPositiveDisagreement_nextNegCol (M := M) a) = true :=
  Classical.choose_spec
    (exists_row_neg_disagreement_of_pos
      (M := M) (X := X) (Y := Y) (r := a.1.1) (cpos := a.1.2)
      a.2.1 a.2.2)

noncomputable def fixedMarginPositiveDisagreement_nextRow
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (a : fixedMarginPositiveDisagreement (M := M) X Y) : Row :=
  Classical.choose
    (exists_col_pos_disagreement_of_neg
      (M := M) (X := X) (Y := Y) (rneg := a.1.1)
      (c := fixedMarginPositiveDisagreement_nextNegCol (M := M) a)
      (fixedMarginPositiveDisagreement_nextNegCol_spec (M := M) a).1
      (fixedMarginPositiveDisagreement_nextNegCol_spec (M := M) a).2)

private theorem fixedMarginPositiveDisagreement_nextRow_spec
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (a : fixedMarginPositiveDisagreement (M := M) X Y) :
    X.1 (fixedMarginPositiveDisagreement_nextRow (M := M) a)
        (fixedMarginPositiveDisagreement_nextNegCol (M := M) a) = true ∧
      Y.1 (fixedMarginPositiveDisagreement_nextRow (M := M) a)
        (fixedMarginPositiveDisagreement_nextNegCol (M := M) a) = false :=
  Classical.choose_spec
    (exists_col_pos_disagreement_of_neg
      (M := M) (X := X) (Y := Y) (rneg := a.1.1)
      (c := fixedMarginPositiveDisagreement_nextNegCol (M := M) a)
      (fixedMarginPositiveDisagreement_nextNegCol_spec (M := M) a).1
      (fixedMarginPositiveDisagreement_nextNegCol_spec (M := M) a).2)

noncomputable def fixedMarginPositiveDisagreement_next
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (a : fixedMarginPositiveDisagreement (M := M) X Y) :
    fixedMarginPositiveDisagreement (M := M) X Y :=
  ⟨(fixedMarginPositiveDisagreement_nextRow (M := M) a,
      fixedMarginPositiveDisagreement_nextNegCol (M := M) a),
    fixedMarginPositiveDisagreement_nextRow_spec (M := M) a⟩

private theorem fixedMarginPositiveDisagreement_next_edge
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (a : fixedMarginPositiveDisagreement (M := M) X Y) :
    X.1 a.1.1 (fixedMarginPositiveDisagreement_next (M := M) a).1.2 = false ∧
      Y.1 a.1.1 (fixedMarginPositiveDisagreement_next (M := M) a).1.2 = true ∧
      X.1 (fixedMarginPositiveDisagreement_next (M := M) a).1.1
          (fixedMarginPositiveDisagreement_next (M := M) a).1.2 = true ∧
      Y.1 (fixedMarginPositiveDisagreement_next (M := M) a).1.1
          (fixedMarginPositiveDisagreement_next (M := M) a).1.2 = false := by
  exact
    ⟨(fixedMarginPositiveDisagreement_nextNegCol_spec (M := M) a).1,
      (fixedMarginPositiveDisagreement_nextNegCol_spec (M := M) a).2,
      (fixedMarginPositiveDisagreement_nextRow_spec (M := M) a).1,
      (fixedMarginPositiveDisagreement_nextRow_spec (M := M) a).2⟩

private theorem fixedMarginPositiveDisagreement_next_ne
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (a : fixedMarginPositiveDisagreement (M := M) X Y) :
    fixedMarginPositiveDisagreement_next (M := M) a ≠ a := by
  intro h
  have hXneg : X.1 a.1.1 (fixedMarginPositiveDisagreement_next (M := M) a).1.2 = false :=
    (fixedMarginPositiveDisagreement_next_edge (M := M) a).1
  have hXpos : X.1 a.1.1 (fixedMarginPositiveDisagreement_next (M := M) a).1.2 = true := by
    rw [h]
    exact a.2.1
  simp [hXpos] at hXneg

private theorem fixedMarginPositiveDisagreement_iterate_edge
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (a : fixedMarginPositiveDisagreement (M := M) X Y) (n : Nat) :
    X.1 ((fixedMarginPositiveDisagreement_next (M := M))^[n] a).1.1
        ((fixedMarginPositiveDisagreement_next (M := M))^[n + 1] a).1.2 = false ∧
      Y.1 ((fixedMarginPositiveDisagreement_next (M := M))^[n] a).1.1
        ((fixedMarginPositiveDisagreement_next (M := M))^[n + 1] a).1.2 = true ∧
      X.1 ((fixedMarginPositiveDisagreement_next (M := M))^[n + 1] a).1.1
          ((fixedMarginPositiveDisagreement_next (M := M))^[n + 1] a).1.2 = true ∧
      Y.1 ((fixedMarginPositiveDisagreement_next (M := M))^[n + 1] a).1.1
          ((fixedMarginPositiveDisagreement_next (M := M))^[n + 1] a).1.2 = false := by
  simpa [Nat.add_comm, Function.iterate_succ_apply']
    using
      fixedMarginPositiveDisagreement_next_edge
        (M := M) ((fixedMarginPositiveDisagreement_next (M := M))^[n] a)

private theorem exists_fixedMarginPositiveDisagreement_iterate_repeat
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (hXY : X ≠ Y) :
    ∃ start : fixedMarginPositiveDisagreement (M := M) X Y,
      ∃ i j : Fin (Fintype.card (fixedMarginPositiveDisagreement (M := M) X Y) + 1),
        i ≠ j ∧
          (fixedMarginPositiveDisagreement_next (M := M))^[i.1] start =
            (fixedMarginPositiveDisagreement_next (M := M))^[j.1] start := by
  classical
  rcases exists_alternating_two_step_of_fixedMarginState_ne
      (M := M) (X := X) (Y := Y) hXY with
    ⟨p, cpos, _cneg, _hc_ne, hXpos, hYpos, _hXneg, _hYneg,
      _hXrpos, _hYrpos⟩
  let start : fixedMarginPositiveDisagreement (M := M) X Y :=
    ⟨(p.1.1, cpos), hXpos, hYpos⟩
  let f :
      Fin (Fintype.card (fixedMarginPositiveDisagreement (M := M) X Y) + 1) →
        fixedMarginPositiveDisagreement (M := M) X Y :=
    fun i => (fixedMarginPositiveDisagreement_next (M := M))^[i.1] start
  have hcard :
      Fintype.card (fixedMarginPositiveDisagreement (M := M) X Y) <
        Fintype.card
          (Fin (Fintype.card (fixedMarginPositiveDisagreement (M := M) X Y) + 1)) := by
    simp
  rcases Fintype.exists_ne_map_eq_of_card_lt f hcard with
    ⟨i, j, hij, heq⟩
  exact ⟨start, i, j, hij, heq⟩

private theorem exists_fixedMarginPositiveDisagreement_iterate_repeat_nat
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (hXY : X ≠ Y) :
    ∃ start : fixedMarginPositiveDisagreement (M := M) X Y,
      ∃ m n : Nat,
        m < n ∧
          n ≤ Fintype.card (fixedMarginPositiveDisagreement (M := M) X Y) ∧
          (fixedMarginPositiveDisagreement_next (M := M))^[m] start =
            (fixedMarginPositiveDisagreement_next (M := M))^[n] start := by
  classical
  rcases exists_fixedMarginPositiveDisagreement_iterate_repeat
      (M := M) (X := X) (Y := Y) hXY with
    ⟨start, i, j, hij, heq⟩
  have hne_val : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne_val with hlt | hgt
  · refine ⟨start, i.1, j.1, hlt, ?_, heq⟩
    omega
  · refine ⟨start, j.1, i.1, hgt, ?_, heq.symm⟩
    omega


def FixedMarginAlternatingClosedWalkLength
    (M : FixedMarginModel Row Col) (X Y : FixedMarginState M) (L : Nat) : Prop :=
  ∃ r : Nat → Row, ∃ c : Nat → Col,
    2 ≤ L ∧
      (∀ i : Nat, i < L →
        X.1 (r i) (c i) = true ∧ Y.1 (r i) (c i) = false) ∧
      (∀ i : Nat, i + 1 < L →
        X.1 (r i) (c (i + 1)) = false ∧
          Y.1 (r i) (c (i + 1)) = true) ∧
      X.1 (r (L - 1)) (c 0) = false ∧
        Y.1 (r (L - 1)) (c 0) = true

private theorem fixedMarginAlternatingClosedWalkLength_of_col_repeat'
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    {L a b : Nat}
    {r : Nat → Row} {c : Nat → Col}
    (hRed : ∀ i : Nat, i < L →
      X.1 (r i) (c i) = true ∧ Y.1 (r i) (c i) = false)
    (hBlue : ∀ i : Nat, i + 1 < L →
      X.1 (r i) (c (i + 1)) = false ∧
        Y.1 (r i) (c (i + 1)) = true)
    (hab : a < b) (hbL : b < L) (hcol : c a = c b) :
    FixedMarginAlternatingClosedWalkLength M X Y (b - a) := by
  classical
  let L' := b - a
  let r' : Nat → Row := fun i => r (a + i)
  let c' : Nat → Col := fun i => c (a + i)
  have hnot_adj : b ≠ a + 1 := by
    intro hb
    have hred := (hRed a (by omega)).1
    have hblue := (hBlue a (by omega)).1
    have hc : c (a + 1) = c a := by
      calc
        c (a + 1) = c b := by rw [hb]
        _ = c a := hcol.symm
    rw [hc, hred] at hblue
    contradiction
  have hlen' : 2 ≤ L' := by
    change 2 ≤ b - a
    omega
  refine ⟨r', c', hlen', ?_, ?_, ?_⟩
  · intro i hi
    have hidx : a + i < L := by
      change i < b - a at hi
      omega
    simpa [r', c'] using hRed (a + i) hidx
  · intro i hi
    have hidx : a + i + 1 < L := by
      change i + 1 < b - a at hi
      omega
    have hnext : a + (i + 1) = a + i + 1 := by omega
    simpa [r', c', hnext] using hBlue (a + i) hidx
  · have hbpos : 0 < b := by omega
    have hidx : b - 1 + 1 < L := by omega
    have hpred : b - 1 + 1 = b := by omega
    have hlast : a + (L' - 1) = b - 1 := by
      dsimp [L']
      omega
    have hblue := hBlue (b - 1) hidx
    constructor
    · simpa [r', c', L', hlast, hpred, hcol] using hblue.1
    · simpa [r', c', L', hlast, hpred, hcol] using hblue.2

private theorem fixedMarginAlternatingClosedWalkLength_of_row_repeat'
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    {L a b : Nat}
    {r : Nat → Row} {c : Nat → Col}
    (hRed : ∀ i : Nat, i < L →
      X.1 (r i) (c i) = true ∧ Y.1 (r i) (c i) = false)
    (hBlue : ∀ i : Nat, i + 1 < L →
      X.1 (r i) (c (i + 1)) = false ∧
        Y.1 (r i) (c (i + 1)) = true)
    (hab : a < b) (hbL : b < L) (hrow : r a = r b) :
    FixedMarginAlternatingClosedWalkLength M X Y (b - a) := by
  classical
  let L' := b - a
  let r' : Nat → Row := fun i => r (a + 1 + i)
  let c' : Nat → Col := fun i => c (a + 1 + i)
  have hnot_adj : b ≠ a + 1 := by
    intro hb
    have hred := (hRed b hbL).1
    have hblue := (hBlue a (by omega)).1
    have hr : r b = r a := hrow.symm
    have hc : c b = c (a + 1) := by rw [hb]
    have hred' : X.1 (r a) (c (a + 1)) = true := by
      simpa [hr, hc] using hred
    rw [hred'] at hblue
    contradiction
  have hlen' : 2 ≤ L' := by
    change 2 ≤ b - a
    omega
  refine ⟨r', c', hlen', ?_, ?_, ?_⟩
  · intro i hi
    have hidx : a + 1 + i < L := by
      change i < b - a at hi
      omega
    simpa [r', c'] using hRed (a + 1 + i) hidx
  · intro i hi
    have hidx : a + 1 + i + 1 < L := by
      change i + 1 < b - a at hi
      omega
    have hnext : a + 1 + (i + 1) = a + 1 + i + 1 := by omega
    simpa [r', c', hnext] using hBlue (a + 1 + i) hidx
  · have hidx : a + 1 < L := by omega
    have hlast : a + 1 + (L' - 1) = b := by
      dsimp [L']
      omega
    have hblue := hBlue a hidx
    constructor
    · simpa [r', c', L', hlast, hrow] using hblue.1
    · simpa [r', c', L', hlast, hrow] using hblue.2

private theorem exists_simple_fixedMarginAlternatingClosedWalk
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (hExists : ∃ L : Nat, FixedMarginAlternatingClosedWalkLength M X Y L) :
    ∃ L : Nat, ∃ r : Nat → Row, ∃ c : Nat → Col,
      2 ≤ L ∧
        (∀ i : Nat, i < L →
          X.1 (r i) (c i) = true ∧ Y.1 (r i) (c i) = false) ∧
        (∀ i : Nat, i + 1 < L →
          X.1 (r i) (c (i + 1)) = false ∧
            Y.1 (r i) (c (i + 1)) = true) ∧
        (X.1 (r (L - 1)) (c 0) = false ∧
          Y.1 (r (L - 1)) (c 0) = true) ∧
        (∀ a b : Nat, a < b → b < L → r a ≠ r b) ∧
        (∀ a b : Nat, a < b → b < L → c a ≠ c b) := by
  classical
  let L : Nat := Nat.find hExists
  have hWalk : FixedMarginAlternatingClosedWalkLength M X Y L :=
    Nat.find_spec hExists
  rcases hWalk with ⟨r, c, hlen, hRed, hBlue, hClosing⟩
  have hRowDistinct : ∀ a b : Nat, a < b → b < L → r a ≠ r b := by
    intro a b hab hbL hrow
    have hShort :
        FixedMarginAlternatingClosedWalkLength M X Y (b - a) :=
      fixedMarginAlternatingClosedWalkLength_of_row_repeat'
        (M := M) (X := X) (Y := Y)
        hRed hBlue hab hbL hrow
    have hlt : b - a < L := by
      omega
    exact Nat.find_min hExists hlt hShort
  have hColDistinct : ∀ a b : Nat, a < b → b < L → c a ≠ c b := by
    intro a b hab hbL hcol
    have hShort :
        FixedMarginAlternatingClosedWalkLength M X Y (b - a) :=
      fixedMarginAlternatingClosedWalkLength_of_col_repeat'
        (M := M) (X := X) (Y := Y)
        hRed hBlue hab hbL hcol
    have hlt : b - a < L := by
      omega
    exact Nat.find_min hExists hlt hShort
  exact ⟨L, r, c, hlen, hRed, hBlue, hClosing, hRowDistinct, hColDistinct⟩


private theorem fixedMarginAlternatingClosedWalkLength_of_positiveDisagreement_cycle
    {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (start : fixedMarginPositiveDisagreement (M := M) X Y)
    {m n : Nat}
    (hmn : m < n)
    (hlen : 2 ≤ n - m)
    (hcycle :
      (fixedMarginPositiveDisagreement_next (M := M))^[m] start =
        (fixedMarginPositiveDisagreement_next (M := M))^[n] start) :
    FixedMarginAlternatingClosedWalkLength M X Y (n - m) := by
  classical
  let f := fixedMarginPositiveDisagreement_next (M := M) (X := X) (Y := Y)
  let r : Nat → Row := fun i => (f^[m + i] start).1.1
  let c : Nat → Col := fun i => (f^[m + i] start).1.2
  refine ⟨r, c, hlen, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨(f^[m + i] start).2.1, (f^[m + i] start).2.2⟩
  · intro i hi
    have hEdge :=
      fixedMarginPositiveDisagreement_iterate_edge
        (M := M) (X := X) (Y := Y) start (m + i)
    have hidx : m + i + 1 = m + (i + 1) := by omega
    constructor
    · simpa [r, c, f, hidx] using hEdge.1
    · simpa [r, c, f, hidx] using hEdge.2.1
  · have hClosing :=
      fixedMarginPositiveDisagreement_iterate_edge
        (M := M) (X := X) (Y := Y) start (n - 1)
    have hn_pred : n - 1 + 1 = n := by omega
    have hlast : m + (n - m - 1) = n - 1 := by omega
    constructor
    · simpa [r, c, f, hlast, hn_pred, hcycle.symm] using hClosing.1
    · simpa [r, c, f, hlast, hn_pred, hcycle.symm] using hClosing.2.1


/-- Unequal Boolean tables with the same labeled margins have a separately simple
cycle consisting entirely of positive and negative target disagreements. -/
theorem simple_cycle {M : FixedMarginModel Row Col} {X Y : FixedMarginState M}
    (hne : X ≠ Y) :
    ∃ L : ℕ, ∃ r : ℕ → Row, ∃ c : ℕ → Col,
      2 ≤ L ∧
      (∀ i, i < L → X.1 (r i) (c i) = true ∧ Y.1 (r i) (c i) = false) ∧
      (∀ i, i + 1 < L → X.1 (r i) (c (i + 1)) = false ∧
        Y.1 (r i) (c (i + 1)) = true) ∧
      (X.1 (r (L - 1)) (c 0) = false ∧ Y.1 (r (L - 1)) (c 0) = true) ∧
      (∀ a b, a < b → b < L → r a ≠ r b) ∧
      (∀ a b, a < b → b < L → c a ≠ c b) := by
  obtain ⟨start, m, n, hmn, _, heq⟩ :=
    exists_fixedMarginPositiveDisagreement_iterate_repeat_nat hne
  have hnot : n ≠ m + 1 := by
    intro h
    rw [h, Function.iterate_succ_apply'] at heq
    exact fixedMarginPositiveDisagreement_next_ne _ heq.symm
  have hlen : 2 ≤ n - m := by omega
  exact exists_simple_fixedMarginAlternatingClosedWalk
    ⟨n - m, fixedMarginAlternatingClosedWalkLength_of_positiveDisagreement_cycle
      start hmn hlen heq⟩

#check simple_cycle
#print axioms simple_cycle
end D5.S3.Combinatorics.Transportation.SupportedCycleSupplier
