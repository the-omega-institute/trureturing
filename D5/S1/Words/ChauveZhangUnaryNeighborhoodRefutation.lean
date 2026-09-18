/- GID: D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation
   generality: I
   mirror-B: D5/B/S1/Words/ChauveZhangUnaryNeighborhoodRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimCondensed; result=D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed; claim=D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimCondensed
   digest: Chauve-Zhang unary CN/SCN minimality fails: 000 vs 001; 0000 vs 0011. -/

import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace D5.S1.Words.ChauveZhangUnaryNeighborhoodRefutation

/-
proof_shape: resultCondensed: content; resultSuperCondensed: content
escape_witness: length_le_add_levenshtein (form (1): the local `have ∀ xs ys : List Bool, xs.length ≤ ys.length + levenshtein xs ys` on the live path of both results, proved by induction on the private fuel recursion)
admission_basis: open-problem-resolution (issue #8618)
Direct frozen dependencies: none (pinned Mathlib only)
-/

variable {α : Type} [DecidableEq α]

private def levenshteinAux : ℕ → List α → List α → ℕ
  | _, [], ys => ys.length
  | _, xs, [] => xs.length
  | 0, _ :: _, _ :: _ => 0
  | fuel + 1, x :: xs, y :: ys =>
      min (levenshteinAux fuel xs (y :: ys) + 1)
        (min (levenshteinAux fuel (x :: xs) ys + 1)
          (levenshteinAux fuel xs ys + if x = y then 0 else 1))

/-- Levenshtein distance: the minimum number of insertions, deletions and substitutions transforming one word
into the other, computed by the Wagner--Fischer recurrence (`[] ys -> |ys|`, `xs [] -> |xs|`,
`(x::xs) (y::ys) -> min (d xs (y::ys) + 1) (min (d (x::xs) ys + 1) (d xs ys + if x = y then 0 else 1))`).
Pinned Mathlib `db584cd6` has no `levenshtein`. -/
def levenshtein (xs ys : List α) : ℕ :=
  levenshteinAux (xs.length + ys.length) xs ys

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

/-- (2.1) `N(w,d) = {x ∈ Σ* | d_lev(x,w) ≤ d}`. -/
def neighborhood (w : List α) (d : ℕ) : Set (List α) :=
  {x | levenshtein x w ≤ d}

/-- (2.2) `CN(w,d) = N(w,d) \ N(w,d)Σ+`: the words of `N` with no proper prefix in `N`. -/
def condensed (w : List α) (d : ℕ) : Set (List α) :=
  {x ∈ neighborhood w d | ∀ y, y <+: x → y ≠ x → y ∉ neighborhood w d}

/-- (2.3) `SCN(w,d) = N(w,d) \ (Σ*N(w,d)Σ+ ∪ Σ+N(w,d)Σ*)`: the words of `N` with no proper subword in `N`. -/
def superCondensed (w : List α) (d : ℕ) : Set (List α) :=
  {x ∈ neighborhood w d | ∀ y, y <:+: x → y ≠ x → y ∉ neighborhood w d}

private def wordsUpTo {β : Type} [Fintype β] [DecidableEq β] : ℕ → Finset (List β)
  | 0 => {[]}
  | n + 1 => insert [] ((Finset.univ ×ˢ wordsUpTo n).image fun p => p.1 :: p.2)

/-- The first assertion of the closing question: unary words have the smallest condensed neighborhoods. -/
def claimCondensed : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (n d : ℕ) (a : α) (w : List α),
    w.length = n →
      (condensed (List.replicate n a) d).ncard ≤ (condensed w d).ncard

/-- The second assertion: unary words have the smallest super condensed neighborhoods. -/
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

example : levenshtein "align".toList "assign".toList = 2 := by
  rfl

example : Nonempty (List Bool) := ⟨[]⟩

example : (List.replicate 3 false).length = 3 := by
  decide

#print axioms resultCondensed
#print axioms resultSuperCondensed

end D5.S1.Words.ChauveZhangUnaryNeighborhoodRefutation
