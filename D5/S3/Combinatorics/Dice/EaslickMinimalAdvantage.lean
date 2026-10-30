/- GID: D5/S3/Combinatorics/Dice/EaslickMinimalAdvantage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Dice/EaslickMinimalAdvantage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exact independent dice probabilities and their attainable least strict advantage. -/

import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage

/-- A die is its unique nondecreasing list of faces, with repetitions permitted. -/
def IsDie (n : ℕ) (d : List ℕ) : Prop :=
  d.length = n ∧ d.Pairwise (· ≤ ·) ∧ ∀ x ∈ d, 1 ≤ x ∧ x ≤ n

/-- Each occurrence of each face contributes separately to the strict-win count. -/
def winCount (d e : List ℕ) : ℕ :=
  (d.map fun x => (e.map fun y => if y < x then 1 else 0).sum).sum

/-- The actual uniform product sample space consists of the two face indices. -/
def indexWinCount (d e : List ℕ) : ℕ :=
  ∑ i : Fin d.length, ∑ j : Fin e.length, if e[j.val] < d[i.val] then 1 else 0

/-- Fair independent rolls give weight one over the product of the face counts. -/
def winProbability (d e : List ℕ) : ℚ :=
  (indexWinCount d e : ℚ) / (d.length * e.length : ℕ)

/-- The first integer strictly above half the number of ordered outcomes. -/
def threshold (n : ℕ) : ℕ := n * n / 2 + 1

/-- Minimum among the actual probabilities of all valid ordered pairs of dice. -/
def IsMinimum (n : ℕ) (p : ℚ) : Prop :=
  (∃ d e, IsDie n d ∧ IsDie n e ∧ winProbability d e = p) ∧
  1 / 2 < p ∧ ∀ d e, IsDie n d → IsDie n e →
    1 / 2 < winProbability d e → p ≤ winProbability d e

/-- Edges use the true attained minimum, without substituting a parity formula. -/
def Edge (n : ℕ) (d e : List ℕ) : Prop :=
  IsDie n d ∧ IsDie n e ∧ IsMinimum n (winProbability d e)

/-- A cycle uses k distinct dice and includes the last-to-first edge. -/
def HasCycle (n k : ℕ) : Prop :=
  ∃ c : List (List ℕ), c.length = k ∧ c.Nodup ∧ c ≠ [] ∧
    (c ++ [c.head!]).IsChain (Edge n)

/-- The global maximum simple-cycle length is exactly n. -/
def S (n : ℕ) : Prop := HasCycle n n ∧ ∀ k, n < k → ¬ HasCycle n k

/-- Easlick's complete Conjecture 1, with no assertion required below six. -/
def ConjectureOne : Prop := S 6 ∧ ∀ n : ℕ, 7 ≤ n → ¬ S n

/-- Counting face occurrences is exactly counting the uniform index product. -/
theorem winCount_eq_indexWinCount (d e : List ℕ) : winCount d e = indexWinCount d e := by
  have row (x : ℕ) : (e.map fun y => if y < x then 1 else 0).sum =
      ∑ j : Fin e.length, if e[j.val] < x then 1 else 0 := by
    rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  simp_rw [winCount, row]
  rw [indexWinCount, ← List.sum_ofFn, List.ofFn_getElem_eq_map]

@[simp] private theorem wins_nil_left (e : List ℕ) : winCount [] e = 0 := by simp [winCount]
@[simp] private theorem wins_nil_right (d : List ℕ) : winCount d [] = 0 := by simp [winCount]

private theorem wins_append_left (a b e : List ℕ) :
    winCount (a ++ b) e = winCount a e + winCount b e := by simp [winCount]

private theorem wins_append_right (d a b : List ℕ) :
    winCount d (a ++ b) = winCount d a + winCount d b := by
  induction d with
  | nil => simp
  | cons x d ih =>
    simp only [winCount, List.map_cons, List.sum_cons, List.map_append, List.sum_append] at *
    omega

private theorem wins_replicate (a b m k : ℕ) :
    winCount (List.replicate m a) (List.replicate k b) =
      if b < a then m * k else 0 := by
  by_cases h : b < a <;> simp [winCount, h]

private theorem wins_single_left (a : ℕ) (e : List ℕ) :
    winCount [a] e = (e.map fun b => if b < a then 1 else 0).sum := by simp [winCount]

private theorem wins_shift (d e : List ℕ) (s : ℕ) :
    winCount (d.map (· + s)) (e.map (· + s)) = winCount d e := by
  simp [winCount, List.map_map, Function.comp_def]

private theorem wins_all (d e : List ℕ) (h : ∀ x ∈ d, ∀ y ∈ e, y < x) :
    winCount d e = d.length * e.length := by
  have row (x : ℕ) (hx : x ∈ d) :
      (e.map fun y => if y < x then 1 else 0).sum = e.length := by
    have : (e.map fun y => if y < x then 1 else 0) = List.replicate e.length 1 := by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        simp [h x hx e[i] (List.getElem_mem _)]
    rw [this]
    simp
  unfold winCount
  rw [List.map_congr_left row]
  simp

private theorem wins_none (d e : List ℕ) (h : ∀ x ∈ d, ∀ y ∈ e, x ≤ y) :
    winCount d e = 0 := by
  have row (x : ℕ) (hx : x ∈ d) :
      (e.map fun y => if y < x then 1 else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    simp [Nat.not_lt.mpr (h x hx y hy)]
  unfold winCount
  rw [List.map_congr_left row]
  simp

private def evenX (k : ℕ) := List.replicate (k - 1) 1 ++ [2] ++ List.replicate k 3
private def evenY (k : ℕ) := [1] ++ List.replicate (2 * k - 1) 2
private def oddX (k : ℕ) := List.replicate k 1 ++ [2] ++ List.replicate k 3
private def oddY (k : ℕ) := List.replicate (k + 1) 1 ++ List.replicate k 2

private theorem even_valid (k : ℕ) (hk : 2 ≤ k) :
    IsDie (2*k) (evenX k) ∧ IsDie (2*k) (evenY k) := by
  constructor <;> simp [IsDie, evenX, evenY, List.pairwise_append,
    List.pairwise_replicate, List.mem_replicate] <;> omega

private theorem odd_valid (k : ℕ) (hk : 1 ≤ k) :
    IsDie (2*k+1) (oddX k) ∧ IsDie (2*k+1) (oddY k) := by
  constructor <;> simp [IsDie, oddX, oddY, List.pairwise_append,
    List.pairwise_replicate, List.mem_replicate] <;> omega

private theorem even_wins (k : ℕ) (hk : 2 ≤ k) :
    winCount (evenX k) (evenY k) = threshold (2*k) := by
  have hsq : 2*k*(2*k) = (2*k*k)*2 := by ring
  simp [evenX, evenY, wins_append_left, wins_append_right, winCount, threshold, hsq]
  omega

private theorem odd_wins (k : ℕ) (hk : 1 ≤ k) :
    winCount (oddX k) (oddY k) = threshold (2*k+1) := by
  have hsq : (2*k+1)*(2*k+1) = (2*k*k+2*k)*2+1 := by ring
  simp [oddX, oddY, wins_append_left, wins_append_right, winCount, threshold, hsq]
  omega

/-- The integer-grid lower bound is attained for every number of faces at least three. -/
theorem threshold_attained (n : ℕ) (hn : 3 ≤ n) :
    ∃ d e, IsDie n d ∧ IsDie n e ∧ winCount d e = threshold n := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hn' : n = 2*k := by omega
    subst n
    exact ⟨evenX k, evenY k, (even_valid k (by omega)).1,
      (even_valid k (by omega)).2, even_wins k (by omega)⟩
  · obtain ⟨k, hk⟩ := ho
    have hn' : n = 2*k+1 := by omega
    subst n
    exact ⟨oddX k, oddY k, (odd_valid k (by omega)).1,
      (odd_valid k (by omega)).2, odd_wins k (by omega)⟩

end D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage
