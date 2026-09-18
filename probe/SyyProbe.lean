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

end SyyProbe
