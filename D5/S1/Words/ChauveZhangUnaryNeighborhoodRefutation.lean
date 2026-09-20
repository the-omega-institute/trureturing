/- GID: D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation
   generality: I
   mirror-B: D5/B/S1/Words/ChauveZhangUnaryNeighborhoodRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Set.Card, mathlib/module/Mathlib.Order.Lattice.Nat]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimCondensed; result=D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed; claim=D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimCondensed
   digest: Chauve-Zhang unary CN/SCN minimality fails at (3,2) and (4,1). -/

import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false

namespace D5.S1.Words.ChauveZhangUnaryNeighborhoodRefutation

/-
proof_shape: levenshtein_eq_dlev: content; resultCondensed: content; resultSuperCondensed: content
escape_witness: levenshtein_eq_dlev: form (2), universal alignment lower bound and an attaining alignment;
  form (1), levenshtein_le_cost and exists_alignment_levenshtein;
  resultCondensed and resultSuperCondensed: levenshtein_eq_dlev on the live path
admission_basis: levenshtein_eq_dlev: escape-witness;
  resultCondensed and resultSuperCondensed: open-problem-resolution (issue #8618)
Direct frozen dependencies: none (pinned Mathlib only)
-/

variable {α : Type} [DecidableEq α]

/-- A column of an alignment (printed page 2): a letter over a letter, a letter over a gap,
or a gap over a letter. There is no gap-over-gap constructor. -/
inductive Column (α : Type)
  | both (x y : α)
  | top (x : α)
  | bottom (y : α)

/-- An alignment is a two-row array, read column by column from left to right. -/
abbrev Alignment (α : Type) := List (Column α)

/-- The first row after deleting all gaps. -/
def topRow : Alignment α → List α
  | [] => []
  | Column.both x _ :: A => x :: topRow A
  | Column.top x :: A => x :: topRow A
  | Column.bottom _ :: A => topRow A

/-- The second row after deleting all gaps. -/
def bottomRow : Alignment α → List α
  | [] => []
  | Column.both _ y :: A => y :: bottomRow A
  | Column.top _ :: A => bottomRow A
  | Column.bottom y :: A => y :: bottomRow A

/-- The number of columns containing two different characters, counting each gap once. -/
def cost : Alignment α → ℕ
  | [] => 0
  | Column.both x y :: A => (if x = y then 0 else 1) + cost A
  | Column.top _ :: A => 1 + cost A
  | Column.bottom _ :: A => 1 + cost A

/-- The alignment containing only letters in its top row. -/
private def topAlignment (xs : List α) : Alignment α := xs.map Column.top

/-- The alignment containing only letters in its bottom row. -/
private def bottomAlignment (ys : List α) : Alignment α := ys.map Column.bottom


/-- `d_lev(u,v)`: the paper first defines the minimum number of insertion, deletion and
substitution edits, then states that it equals the minimum cost of an alignment. This
formalization takes the stated alignment characterization as its definition. -/
noncomputable def dlev (u v : List α) : ℕ :=
  sInf {c | ∃ A : Alignment α,
    topRow A = u ∧ bottomRow A = v ∧ cost A = c}

private def levenshteinAux : ℕ → List α → List α → ℕ
  | _, [], ys => ys.length
  | _, xs, [] => xs.length
  | 0, _ :: _, _ :: _ => 0
  | fuel + 1, x :: xs, y :: ys =>
      min (levenshteinAux fuel xs (y :: ys) + 1)
        (min (levenshteinAux fuel (x :: xs) ys + 1)
          (levenshteinAux fuel xs ys + if x = y then 0 else 1))

/-- The fuelled Wagner--Fischer recurrence used to compute `d_lev`. -/
def levenshtein (xs ys : List α) : ℕ :=
  levenshteinAux (xs.length + ys.length) xs ys


private theorem levenshtein_le_cost (A : Alignment α) :
    levenshtein (topRow A) (bottomRow A) ≤ cost A := by
  have levenshtein_cons (x y : α) (xs ys : List α) :
      levenshtein (x :: xs) (y :: ys) =
        min (levenshtein xs (y :: ys) + 1)
          (min (levenshtein (x :: xs) ys + 1)
            (levenshtein xs ys + if x = y then 0 else 1)) := by
    have aux_succ_eq_of_length_add_le :
        ∀ (fuel : ℕ) (as bs : List α), as.length + bs.length ≤ fuel →
          levenshteinAux (fuel + 1) as bs = levenshteinAux fuel as bs := by
      intro fuel
      induction fuel with
      | zero =>
          intro as bs hfuel
          cases as <;> cases bs <;> simp [levenshteinAux] at hfuel ⊢
      | succ fuel ih =>
          intro as bs hfuel
          cases as with
          | nil => simp [levenshteinAux]
          | cons a as =>
              cases bs with
              | nil => simp [levenshteinAux]
              | cons b bs =>
                  have hDelete : as.length + (b :: bs).length ≤ fuel := by
                    simp only [List.length_cons] at hfuel ⊢
                    omega
                  have hInsert : (a :: as).length + bs.length ≤ fuel := by
                    simp only [List.length_cons] at hfuel ⊢
                    omega
                  have hAlign : as.length + bs.length ≤ fuel := by
                    simp only [List.length_cons] at hfuel ⊢
                    omega
                  simp only [levenshteinAux]
                  rw [ih as (b :: bs) hDelete, ih (a :: as) bs hInsert,
                    ih as bs hAlign]
    simp only [levenshtein, List.length_cons, levenshteinAux]
    have hDelete :
        levenshteinAux ((xs.length + 1).add ys.length) xs (y :: ys) =
          levenshteinAux (xs.length + (ys.length + 1)) xs (y :: ys) := by
      congr 1
      simp [Nat.add_comm, Nat.add_left_comm]
    have hInsert :
        levenshteinAux ((xs.length + 1).add ys.length) (x :: xs) ys =
          levenshteinAux (xs.length + 1 + ys.length) (x :: xs) ys := by
      congr 1
    have hAlign :
        levenshteinAux ((xs.length + 1).add ys.length) xs ys =
          levenshteinAux (xs.length + ys.length) xs ys := by
      rw [show (xs.length + 1).add ys.length = xs.length + ys.length + 1 by
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]]
      exact aux_succ_eq_of_length_add_le (xs.length + ys.length) xs ys (Nat.le_refl _)
    rw [hDelete, hInsert, hAlign]
  induction A with
  | nil => simp [topRow, bottomRow, cost, levenshtein, levenshteinAux]
  | cons col A ih =>
      cases col with
      | both x y =>
          simp only [topRow, bottomRow, cost, levenshtein_cons]
          exact (min_le_right _ _).trans <|
            (min_le_right _ _).trans (by
              simpa [Nat.add_comm] using
                Nat.add_le_add_right ih (if x = y then 0 else 1))
      | top x =>
          cases h : bottomRow A with
          | nil =>
              rw [h] at ih
              simp only [topRow, bottomRow, cost, h, levenshtein, levenshteinAux]
              have hright : levenshtein (topRow A) [] = (topRow A).length := by
                cases topRow A <;> simp [levenshtein, levenshteinAux]
              rw [hright] at ih
              simp only [List.length_cons]
              omega
          | cons y ys =>
              rw [h] at ih
              simp only [topRow, bottomRow, cost, h, levenshtein_cons]
              exact (min_le_left _ _).trans (by
                simpa [Nat.add_comm] using Nat.add_le_add_right ih 1)
      | bottom y =>
          cases h : topRow A with
          | nil =>
              rw [h] at ih
              simp only [topRow, bottomRow, cost, h, levenshtein, levenshteinAux]
              simp [levenshtein, levenshteinAux] at ih
              simp only [List.length_cons]
              omega
          | cons x xs =>
              rw [h] at ih
              simp only [topRow, bottomRow, cost, h, levenshtein_cons]
              exact (min_le_right _ _).trans <|
                (min_le_left _ _).trans (by
                  simpa [Nat.add_comm] using Nat.add_le_add_right ih 1)

private theorem exists_alignment_levenshtein (u v : List α) :
    ∃ A : Alignment α,
      topRow A = u ∧ bottomRow A = v ∧ cost A = levenshtein u v := by
  have rows_cost_topAlignment (xs : List α) :
      topRow (topAlignment xs) = xs ∧
        bottomRow (topAlignment xs) = [] ∧ cost (topAlignment xs) = xs.length := by
    induction xs with
    | nil => simp [topAlignment, topRow, bottomRow, cost]
    | cons x xs ih =>
        change (x :: topRow (topAlignment xs) = x :: xs) ∧
          bottomRow (topAlignment xs) = [] ∧
            1 + cost (topAlignment xs) = (x :: xs).length
        refine ⟨by simpa using congrArg (List.cons x) ih.1, ih.2.1, ?_⟩
        rw [ih.2.2]
        simp only [List.length_cons]
        omega

  have rows_cost_bottomAlignment (ys : List α) :
      topRow (bottomAlignment ys) = [] ∧
        bottomRow (bottomAlignment ys) = ys ∧ cost (bottomAlignment ys) = ys.length := by
    induction ys with
    | nil => simp [bottomAlignment, topRow, bottomRow, cost]
    | cons y ys ih =>
        change topRow (bottomAlignment ys) = [] ∧
          (y :: bottomRow (bottomAlignment ys) = y :: ys) ∧
            1 + cost (bottomAlignment ys) = (y :: ys).length
        refine ⟨ih.1, by simpa using congrArg (List.cons y) ih.2.1, ?_⟩
        rw [ih.2.2]
        simp only [List.length_cons]
        omega
  have aux : ∀ (fuel : ℕ) (as bs : List α), as.length + bs.length ≤ fuel →
      ∃ A : Alignment α,
        topRow A = as ∧ bottomRow A = bs ∧ cost A = levenshteinAux fuel as bs := by
    intro fuel
    induction fuel with
    | zero =>
        intro as bs hfuel
        cases as with
        | nil =>
            refine ⟨bottomAlignment bs, (rows_cost_bottomAlignment bs).1,
              (rows_cost_bottomAlignment bs).2.1, ?_⟩
            simpa [levenshteinAux] using (rows_cost_bottomAlignment bs).2.2
        | cons a as =>
            cases bs <;> simp at hfuel
    | succ fuel ih =>
        intro as bs hfuel
        cases as with
        | nil =>
            refine ⟨bottomAlignment bs, (rows_cost_bottomAlignment bs).1,
              (rows_cost_bottomAlignment bs).2.1, ?_⟩
            simpa [levenshteinAux] using (rows_cost_bottomAlignment bs).2.2
        | cons x xs =>
            cases bs with
            | nil =>
                refine ⟨topAlignment (x :: xs), (rows_cost_topAlignment (x :: xs)).1,
                  (rows_cost_topAlignment (x :: xs)).2.1, ?_⟩
                simpa [levenshteinAux] using (rows_cost_topAlignment (x :: xs)).2.2
            | cons y ys =>
                have hDelete : xs.length + (y :: ys).length ≤ fuel := by
                  simp only [List.length_cons] at hfuel ⊢
                  omega
                have hInsert : (x :: xs).length + ys.length ≤ fuel := by
                  simp only [List.length_cons] at hfuel ⊢
                  omega
                have hAlign : xs.length + ys.length ≤ fuel := by
                  simp only [List.length_cons] at hfuel ⊢
                  omega
                obtain ⟨Ad, htd, hbd, hcd⟩ := ih xs (y :: ys) hDelete
                obtain ⟨Ai, hti, hbi, hci⟩ := ih (x :: xs) ys hInsert
                obtain ⟨Aa, hta, hba, hca⟩ := ih xs ys hAlign
                let del := levenshteinAux fuel xs (y :: ys) + 1
                let ins := levenshteinAux fuel (x :: xs) ys + 1
                let sub := levenshteinAux fuel xs ys + if x = y then 0 else 1
                by_cases hd : del ≤ min ins sub
                · refine ⟨Column.top x :: Ad, ?_, ?_, ?_⟩
                  · simp [topRow, htd]
                  · simp [bottomRow, hbd]
                  · simp only [cost, levenshteinAux]
                    rw [Nat.min_eq_left hd]
                    simp [del, hcd, Nat.add_comm]
                · have hright : min ins sub ≤ del := (Nat.lt_of_not_ge hd).le
                  rw [show levenshteinAux (fuel + 1) (x :: xs) (y :: ys) = min ins sub by
                    simp only [levenshteinAux]
                    rw [Nat.min_eq_right hright]]
                  by_cases hi : ins ≤ sub
                  · refine ⟨Column.bottom y :: Ai, ?_, ?_, ?_⟩
                    · simp [topRow, hti]
                    · simp [bottomRow, hbi]
                    · rw [Nat.min_eq_left hi]
                      simp [cost, ins, hci, Nat.add_comm]
                  · have hs : sub ≤ ins := (Nat.lt_of_not_ge hi).le
                    refine ⟨Column.both x y :: Aa, ?_, ?_, ?_⟩
                    · simp [topRow, hta]
                    · simp [bottomRow, hba]
                    · rw [Nat.min_eq_right hs]
                      simp [cost, sub, hca, Nat.add_comm]
  exact aux (u.length + v.length) u v (Nat.le_refl _)

/-- The dynamic program computes the paper's stated minimum alignment cost. -/
theorem levenshtein_eq_dlev (u v : List α) : levenshtein u v = dlev u v := by
  change levenshtein u v = sInf {c | ∃ A : Alignment α,
    topRow A = u ∧ bottomRow A = v ∧ cost A = c}
  obtain ⟨A, htop, hbottom, hcost⟩ := exists_alignment_levenshtein u v
  have hmem : levenshtein u v ∈ {c | ∃ A : Alignment α,
      topRow A = u ∧ bottomRow A = v ∧ cost A = c} :=
    ⟨A, htop, hbottom, hcost⟩
  apply Nat.le_antisymm
  · have hs := Nat.sInf_mem (Set.nonempty_of_mem hmem)
    obtain ⟨B, htopB, hbottomB, hcostB⟩ := hs
    rw [← hcostB, ← htopB, ← hbottomB]
    exact levenshtein_le_cost B
  · exact Nat.sInf_le hmem

/-- (2.1) `N(w,d) = {x in Sigma* | d_lev(x,w) <= d}`. -/
def neighborhood (w : List α) (d : ℕ) : Set (List α) :=
  {x | dlev x w ≤ d}

/-- (2.2) The words of `N(w,d)` having no proper prefix in `N(w,d)`. -/
def condensed (w : List α) (d : ℕ) : Set (List α) :=
  {x ∈ neighborhood w d | ∀ y, y <+: x → y ≠ x → y ∉ neighborhood w d}

/-- (2.3) The words of `N(w,d)` having no proper subword in `N(w,d)`. -/
def superCondensed (w : List α) (d : ℕ) : Set (List α) :=
  {x ∈ neighborhood w d | ∀ y, y <:+: x → y ≠ x → y ∉ neighborhood w d}

private def wordsUpTo {β : Type} [Fintype β] [DecidableEq β] : ℕ → Finset (List β)
  | 0 => {[]}
  | n + 1 => insert [] ((Finset.univ ×ˢ wordsUpTo n).image fun p => p.1 :: p.2)

/-- The first assertion of the closing question. -/
def claimCondensed : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (n d : ℕ) (a : α) (w : List α),
    w.length = n →
      (condensed (List.replicate n a) d).ncard ≤ (condensed w d).ncard

/-- The second assertion of the closing question. -/
def claimSuperCondensed : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (n d : ℕ) (a : α) (w : List α),
    w.length = n →
      (superCondensed (List.replicate n a) d).ncard ≤ (superCondensed w d).ncard

theorem resultCondensed : ¬ claimCondensed := by
  intro h
  have hbad := h Bool 3 2 false [false, false, true] (by decide)
  have mem_wordsUpTo_iff (x : List Bool) (n : ℕ) :
      x ∈ wordsUpTo n ↔ x.length ≤ n := by
    induction n generalizing x with
    | zero => simp [wordsUpTo]
    | succ n ih =>
        cases x with
        | nil => simp [wordsUpTo]
        | cons a x => simp [wordsUpTo, ih]
  have length_le_add_levenshtein (xs ys : List Bool) :
      xs.length ≤ ys.length + levenshtein xs ys := by
    have aux (fuel : ℕ) (as bs : List Bool)
        (hfuel : as.length + bs.length ≤ fuel) :
        as.length ≤ bs.length + levenshteinAux fuel as bs := by
      induction fuel generalizing as bs with
      | zero =>
          cases as <;> cases bs <;> simp [levenshteinAux] at hfuel ⊢
      | succ fuel ih =>
          cases as with
          | nil => simp [levenshteinAux]
          | cons a as =>
              cases bs with
              | nil => simp [levenshteinAux]
              | cons b bs =>
                  have ihDelete := ih as (b :: bs) (by
                    simp only [List.length_cons] at hfuel ⊢
                    omega)
                  have ihInsert := ih (a :: as) bs (by
                    simp only [List.length_cons] at hfuel ⊢
                    omega)
                  have ihAlign := ih as bs (by
                    simp only [List.length_cons] at hfuel ⊢
                    omega)
                  simp only [List.length_cons] at ihDelete ihInsert ⊢
                  simp only [levenshteinAux, Nat.min_def]
                  split <;> split <;> split <;> omega
    apply aux
    exact Nat.le_refl _
  let boundedCondensed (w : List Bool) (d : ℕ) : Finset (List Bool) :=
    (wordsUpTo (w.length + d)).filter fun x =>
      levenshtein x w ≤ d ∧
        (wordsUpTo x.length).filter (fun y =>
          y <+: x ∧ y ≠ x ∧ levenshtein y w ≤ d) = ∅
  have condensed_eq (w : List Bool) (d : ℕ) :
      condensed w d = ↑(boundedCondensed w d) := by
    ext x
    simp only [condensed, neighborhood, Set.mem_ofPred_eq, Finset.mem_coe,
      boundedCondensed, Finset.mem_filter]
    simp_rw [← levenshtein_eq_dlev]
    constructor
    · rintro ⟨hx, hprefix⟩
      refine ⟨mem_wordsUpTo_iff x _ |>.2 ?_, hx, Finset.filter_eq_empty_iff.mpr ?_⟩
      · exact (length_le_add_levenshtein x w).trans (Nat.add_le_add_left hx w.length)
      · intro y _ hy
        exact hprefix y hy.1 hy.2.1 hy.2.2
    · rintro ⟨_, hx, hfiltered⟩
      refine ⟨hx, fun y hy hne hyn => ?_⟩
      have hall := Finset.filter_eq_empty_iff.mp hfiltered
      exact (hall (mem_wordsUpTo_iff y _ |>.2 hy.length_le)) ⟨hy, hne, hyn⟩
  have hunary : (condensed (List.replicate 3 false) 2).ncard = 3 := by
    rw [condensed_eq, Set.ncard_coe_finset]
    rfl
  have hwitness : (condensed [false, false, true] 2).ncard = 2 := by
    rw [condensed_eq, Set.ncard_coe_finset]
    rfl
  omega

theorem resultSuperCondensed : ¬ claimSuperCondensed := by
  intro h
  have hbad := h Bool 4 1 false [false, false, true, true] (by decide)
  have mem_wordsUpTo_iff (x : List Bool) (n : ℕ) :
      x ∈ wordsUpTo n ↔ x.length ≤ n := by
    induction n generalizing x with
    | zero => simp [wordsUpTo]
    | succ n ih =>
        cases x with
        | nil => simp [wordsUpTo]
        | cons a x => simp [wordsUpTo, ih]
  have length_le_add_levenshtein (xs ys : List Bool) :
      xs.length ≤ ys.length + levenshtein xs ys := by
    have aux (fuel : ℕ) (as bs : List Bool)
        (hfuel : as.length + bs.length ≤ fuel) :
        as.length ≤ bs.length + levenshteinAux fuel as bs := by
      induction fuel generalizing as bs with
      | zero =>
          cases as <;> cases bs <;> simp [levenshteinAux] at hfuel ⊢
      | succ fuel ih =>
          cases as with
          | nil => simp [levenshteinAux]
          | cons a as =>
              cases bs with
              | nil => simp [levenshteinAux]
              | cons b bs =>
                  have ihDelete := ih as (b :: bs) (by
                    simp only [List.length_cons] at hfuel ⊢
                    omega)
                  have ihInsert := ih (a :: as) bs (by
                    simp only [List.length_cons] at hfuel ⊢
                    omega)
                  have ihAlign := ih as bs (by
                    simp only [List.length_cons] at hfuel ⊢
                    omega)
                  simp only [List.length_cons] at ihDelete ihInsert ⊢
                  simp only [levenshteinAux, Nat.min_def]
                  split <;> split <;> split <;> omega
    apply aux
    exact Nat.le_refl _
  let boundedSuperCondensed (w : List Bool) (d : ℕ) : Finset (List Bool) :=
    (wordsUpTo (w.length + d)).filter fun x =>
      levenshtein x w ≤ d ∧
        (wordsUpTo x.length).filter (fun y =>
          y <:+: x ∧ y ≠ x ∧ levenshtein y w ≤ d) = ∅
  have superCondensed_eq (w : List Bool) (d : ℕ) :
      superCondensed w d = ↑(boundedSuperCondensed w d) := by
    ext x
    simp only [superCondensed, neighborhood, Set.mem_ofPred_eq, Finset.mem_coe,
      boundedSuperCondensed, Finset.mem_filter]
    simp_rw [← levenshtein_eq_dlev]
    constructor
    · rintro ⟨hx, hinfix⟩
      refine ⟨mem_wordsUpTo_iff x _ |>.2 ?_, hx, Finset.filter_eq_empty_iff.mpr ?_⟩
      · exact (length_le_add_levenshtein x w).trans (Nat.add_le_add_left hx w.length)
      · intro y _ hy
        exact hinfix y hy.1 hy.2.1 hy.2.2
    · rintro ⟨_, hx, hfiltered⟩
      refine ⟨hx, fun y hy hne hyn => ?_⟩
      have hall := Finset.filter_eq_empty_iff.mp hfiltered
      exact (hall (mem_wordsUpTo_iff y _ |>.2 hy.length_le)) ⟨hy, hne, hyn⟩
  have hunary : (superCondensed (List.replicate 4 false) 1).ncard = 3 := by
    rw [superCondensed_eq, Set.ncard_coe_finset]
    rfl
  have hwitness : (superCondensed [false, false, true, true] 1).ncard = 2 := by
    rw [superCondensed_eq, Set.ncard_coe_finset]
    rfl
  omega

example (ys : List α) : levenshtein [] ys = ys.length := by
  simp [levenshtein, levenshteinAux]

example (xs : List α) : levenshtein xs [] = xs.length := by
  cases xs <;> rfl

example (x y : α) (xs ys : List α) :
    levenshtein (x :: xs) (y :: ys) =
      min (levenshtein xs (y :: ys) + 1)
        (min (levenshtein (x :: xs) ys + 1)
          (levenshtein xs ys + if x = y then 0 else 1)) := by
  have aux_succ_eq_of_length_add_le :
      ∀ (fuel : ℕ) (as bs : List α), as.length + bs.length ≤ fuel →
        levenshteinAux (fuel + 1) as bs = levenshteinAux fuel as bs := by
    intro fuel
    induction fuel with
    | zero =>
        intro as bs hfuel
        cases as <;> cases bs <;> simp [levenshteinAux] at hfuel ⊢
    | succ fuel ih =>
        intro as bs hfuel
        cases as with
        | nil => simp [levenshteinAux]
        | cons a as =>
            cases bs with
            | nil => simp [levenshteinAux]
            | cons b bs =>
                have hDelete : as.length + (b :: bs).length ≤ fuel := by
                  simp only [List.length_cons] at hfuel ⊢
                  omega
                have hInsert : (a :: as).length + bs.length ≤ fuel := by
                  simp only [List.length_cons] at hfuel ⊢
                  omega
                have hAlign : as.length + bs.length ≤ fuel := by
                  simp only [List.length_cons] at hfuel ⊢
                  omega
                simp only [levenshteinAux]
                rw [ih as (b :: bs) hDelete, ih (a :: as) bs hInsert,
                  ih as bs hAlign]
  simp only [levenshtein, List.length_cons, levenshteinAux]
  have hDelete :
      levenshteinAux ((xs.length + 1).add ys.length) xs (y :: ys) =
        levenshteinAux (xs.length + (ys.length + 1)) xs (y :: ys) := by
    congr 1
    simp [Nat.add_comm, Nat.add_left_comm]
  have hInsert :
      levenshteinAux ((xs.length + 1).add ys.length) (x :: xs) ys =
        levenshteinAux (xs.length + 1 + ys.length) (x :: xs) ys := by
    congr 1
  have hAlign :
      levenshteinAux ((xs.length + 1).add ys.length) xs ys =
        levenshteinAux (xs.length + ys.length) xs ys := by
    rw [show (xs.length + 1).add ys.length = xs.length + ys.length + 1 by
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]]
    exact aux_succ_eq_of_length_add_le (xs.length + ys.length) xs ys (Nat.le_refl _)
  rw [hDelete, hInsert, hAlign]

example : ∃ A : Alignment Char,
    topRow A = "align".toList ∧ bottomRow A = "assign".toList ∧ cost A = 2 := by
  refine ⟨[Column.both 'a' 'a', Column.both 'l' 's', Column.bottom 's',
    Column.both 'i' 'i', Column.both 'g' 'g', Column.both 'n' 'n'], ?_⟩
  decide

example : dlev "align".toList "assign".toList = 2 := by
  rw [← levenshtein_eq_dlev]
  rfl

#print axioms levenshtein_eq_dlev
#print axioms resultCondensed
#print axioms resultSuperCondensed

end D5.S1.Words.ChauveZhangUnaryNeighborhoodRefutation
