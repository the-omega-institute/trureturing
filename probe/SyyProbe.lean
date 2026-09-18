import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.Range
import Mathlib.Logic.Function.Iterate

/-! An isolated probe of arXiv:2411.11914v2, Conjecture 6.2.
The dotted-pattern map is modeled by the proved right-hand side of Proposition 3.5.
No formal equivalence to the paper's original dotted-pattern stack is asserted. -/

namespace SyyProbe

/-- A valley is strictly smaller than every preceding entry. -/
def IsValley (earlier : List ℕ) (entry : ℕ) : Prop :=
  ∀ a ∈ earlier, entry < a

/-- The current valley starts a run, which ends just before the next smaller entry. -/
def valleyRuns : List ℕ → List (List ℕ)
  | [] => []
  | v :: tail =>
      (v :: tail.takeWhile (fun x => decide (v ≤ x))) ::
        valleyRuns (tail.dropWhile (fun x => decide (v ≤ x)))
termination_by w => w.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_dropWhile_le _ _)

/-- The Proposition 3.5 expression, used as the model's dotted-pattern map. -/
def r (w : List ℕ) : List ℕ := (valleyRuns w).map List.reverse |>.flatten

/-- Stack head is the top. Pop while top < current; push otherwise; flush at EOF. -/
private def westRun (stack input : List ℕ) : List ℕ :=
  match input, stack with
  | [], stack => stack
  | x :: xs, [] => westRun [x] xs
  | x :: xs, a :: rest =>
      if a < x then a :: westRun rest (x :: xs)
      else westRun (x :: a :: rest) xs
termination_by (input.length, stack.length)
decreasing_by all_goals simp_wf; omega

/-- West's deterministic stack-sorting map, defined by its stack algorithm. -/
def s (w : List ℕ) : List ℕ := westRun [] w

/-- The 21-dot machine, in the order specified by the source. -/
def M (w : List ℕ) : List ℕ := s (r w)

/-- The proposed potential, compared with the ordinary lexicographic order. -/
def Phi (w : List ℕ) : List ℕ := w.reverse

private theorem westRun_perm (stack input : List ℕ) :
    (westRun stack input).Perm (stack ++ input) := by
  fun_induction westRun stack input with
  | case1 stack => simp [westRun]
  | case2 x xs ih => simpa [westRun] using ih
  | case3 x xs a rest h ih => simpa [westRun, h] using ih.cons a
  | case4 x xs a rest h ih =>
      simpa [westRun, h] using ih.trans List.perm_middle.symm

private theorem westRun_sentinel (stack input : List ℕ) (m : ℕ)
    (bound : ∀ x ∈ input, x ≤ m) :
    westRun (stack ++ [m]) input = westRun stack input ++ [m] := by
  fun_induction westRun stack input with
  | case1 stack => simp [westRun]
  | case2 x xs ih =>
      have hx : ¬m < x := Nat.not_lt.mpr (bound x (by simp))
      have ht : ∀ y ∈ xs, y ≤ m := fun y hy => bound y (by simp [hy])
      simpa only [List.cons_append, List.nil_append, westRun, if_neg hx] using ih ht
  | case3 x xs a rest h ih =>
      simpa only [List.cons_append, westRun, if_pos h] using congrArg (a :: ·) (ih bound)
  | case4 x xs a rest h ih =>
      have ht : ∀ y ∈ xs, y ≤ m := fun y hy => bound y (by simp [hy])
      simpa only [List.cons_append, westRun, if_neg h] using ih ht

private theorem westRun_split (stack X Y : List ℕ) (m : ℕ)
    (hstack : ∀ x ∈ stack, x < m) (hX : ∀ x ∈ X, x < m) :
    westRun stack (X ++ m :: Y) = westRun stack X ++ westRun [m] Y := by
  fun_induction westRun stack X with
  | case1 stack =>
      simp only [List.nil_append, westRun]
      have drain : ∀ st : List ℕ, (∀ x ∈ st, x < m) →
          westRun st (m :: Y) = st ++ westRun [m] Y := by
        intro st
        induction st with
        | nil => intro _; simp only [westRun, List.nil_append]
        | cons a rest ih =>
            intro hs
            have ha := hs a (by simp)
            have hr : ∀ x ∈ rest, x < m := fun x hx => hs x (by simp [hx])
            simpa only [westRun, if_pos ha, List.cons_append] using
              congrArg (a :: ·) (ih hr)
      exact drain stack hstack
  | case2 x xs ih =>
      have hx := hX x (by simp)
      have ht : ∀ y ∈ xs, y < m := fun y hy => hX y (by simp [hy])
      simpa only [List.cons_append, westRun] using ih (by simpa using hx) ht
  | case3 x xs a rest h ih =>
      have hr : ∀ y ∈ rest, y < m := fun y hy => hstack y (by simp [hy])
      simpa only [List.cons_append, westRun, if_pos h] using
        congrArg (a :: ·) (ih hr hX)
  | case4 x xs a rest h ih =>
      have hx := hX x (by simp)
      have ht : ∀ y ∈ xs, y < m := fun y hy => hX y (by simp [hy])
      have hs : ∀ y ∈ x :: a :: rest, y < m := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx
        · exact hstack y hy
      simpa only [List.cons_append, westRun, if_neg h] using ih hs ht

private theorem s_split_max (X Y : List ℕ) (m : ℕ)
    (hX : ∀ x ∈ X, x < m) (hY : ∀ y ∈ Y, y ≤ m) :
    s (X ++ m :: Y) = s X ++ s Y ++ [m] := by
  rw [s, westRun_split [] X Y m (by simp) hX]
  have hs := westRun_sentinel [] Y m hY
  simpa only [List.nil_append, s, List.append_assoc] using
    congrArg (westRun [] X ++ ·) hs

private theorem r_perm (w : List ℕ) : (r w).Perm w := by
  fun_induction valleyRuns w with
  | case1 => simp [r, valleyRuns]
  | case2 v tail ih =>
      let p := fun x => decide (v ≤ x)
      have h := (List.reverse_perm (v :: tail.takeWhile p)).append ih
      simpa only [p, r, valleyRuns, List.map_cons, List.flatten_cons,
        List.cons_append, List.takeWhile_append_dropWhile] using h

private theorem s_ends_max (w : List ℕ) (ne : w ≠ []) :
    ∃ b m, s w = b ++ [m] ∧ m ∈ w ∧ ∀ x ∈ w, x ≤ m := by
  classical
  have hn : w.toFinset.Nonempty := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil w ne
    exact ⟨a, by simpa using ha⟩
  obtain ⟨m, hm, hmax⟩ := w.toFinset.exists_max_image id hn
  have hm' : m ∈ w := by simpa using hm
  have bound : ∀ x ∈ w, x ≤ m := by simpa using hmax
  obtain ⟨X, Y, hw, hnX⟩ := List.eq_append_cons_of_mem hm'
  subst w
  have hx : ∀ x ∈ X, x < m := by
    intro x hmem
    have le := bound x (by simp [hmem])
    exact lt_of_le_of_ne le (fun e => hnX (e ▸ hmem))
  have hy : ∀ y ∈ Y, y ≤ m := fun y hmem => bound y (by simp [hmem])
  exact ⟨s X ++ s Y, m, s_split_max X Y m hx hy, hm', bound⟩

private theorem input_le_reverse_s (w : List ℕ) : w ≤ (s w).reverse := by
  induction w with
  | nil => simp [s, westRun]
  | cons a tail ih =>
      obtain ⟨b, m, hs, _, hmax⟩ := s_ends_max (a :: tail) (by simp)
      have ha := hmax a (by simp)
      rcases lt_or_eq_of_le ha with ha | rfl
      · rw [hs, List.reverse_append]
        exact le_of_lt (List.Lex.rel ha)
      · have hb : ∀ x ∈ tail, x ≤ a := fun x hx => hmax x (by simp [hx])
        have heq : s (a :: tail) = s tail ++ [a] := by
          simpa only [s, westRun, List.nil_append] using westRun_sentinel [] tail a hb
        rw [heq, List.reverse_append]
        exact List.cons_le_cons a ih

private theorem valleyRuns_append_valley (X Y : List ℕ) (v : ℕ)
    (bound : ∀ x ∈ X, v < x) :
    valleyRuns (X ++ v :: Y) = valleyRuns X ++ valleyRuns (v :: Y) := by
  fun_induction valleyRuns X with
  | case1 => simp [valleyRuns]
  | case2 a tail ih =>
      let p := fun x => decide (a ≤ x)
      have hv : p v = false := by simp [p, Nat.not_le.mpr (bound a (by simp))]
      have cut : ∀ t : List ℕ,
          (t ++ v :: Y).takeWhile p = t.takeWhile p ∧
          (t ++ v :: Y).dropWhile p = t.dropWhile p ++ v :: Y := by
        intro t
        induction t with
        | nil => simp [hv]
        | cons x xs ht =>
            cases hx : p x <;> simp [List.takeWhile_cons, List.dropWhile_cons, hx, ht]
      have hb : ∀ x ∈ tail.dropWhile p, v < x := by
        intro x hx
        have ht : x ∈ tail := List.dropWhile_subset p hx
        exact bound x (by simp [ht])
      simp only [valleyRuns, List.cons_append]
      rw [(cut tail).1, (cut tail).2, ih hb]
      rw [valleyRuns]

private theorem r_split_min (X Y : List ℕ) (v : ℕ)
    (hX : ∀ x ∈ X, v < x) (hY : ∀ y ∈ Y, v ≤ y) :
    r (X ++ v :: Y) = r X ++ Y.reverse ++ [v] := by
  have ht : Y.takeWhile (fun y => decide (v ≤ y)) = Y :=
    List.takeWhile_eq_self_iff.mpr (by simpa using hY)
  have hd : Y.dropWhile (fun y => decide (v ≤ y)) = [] :=
    List.dropWhile_eq_nil_iff.mpr (by simpa using hY)
  simp only [r, valleyRuns_append_valley X Y v hX, List.map_append,
    List.flatten_append, valleyRuns, ht, hd, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.reverse_cons,
    List.append_assoc]

private theorem append_le_of_length_eq {A B C D : List ℕ}
    (hlen : A.length = B.length) (hab : A ≤ B) (hcd : C ≤ D) :
    A ++ C ≤ B ++ D := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · have strict_extend {U V : List ℕ} (h : List.Lex (· < ·) U V) :
        ∀ C D : List ℕ, U.length = V.length →
          List.Lex (· < ·) (U ++ C) (V ++ D) := by
      induction h with
      | nil => intro C D hlen; simp at hlen
      | rel h => intro C D _; exact .rel h
      | cons h ih => intro C D hlen; exact .cons (ih C D (Nat.succ.inj hlen))
    exact le_of_lt (strict_extend hab C D hlen)
  · rcases lt_or_eq_of_le hcd with hcd | rfl
    · exact le_of_lt (List.Lex.append_left (· < ·) hcd A)
    · exact le_rfl

end SyyProbe
