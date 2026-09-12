/- GID: D5/S0/Certificates/JacoExponentialDominationRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/JacoExponentialDominationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Floor.Semiring, mathlib/module/Mathlib.Analysis.Complex.ExponentialBounds, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/JacoExponentialDominationRefutation.claim; result=D5/S0/Certificates/JacoExponentialDominationRefutation.result; claim=D5/S0/Certificates/JacoExponentialDominationRefutation.claim
   digest: Kok's arXiv:2507.16500v1 Conjecture 2.12 is false: the proposed exponential vertex set does not dominate vertex 88 of the infinite linear Jaco graph. -/

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.JacoExponentialDominationRefutation

/-!
Kok, *Integer sequences with conjectured relation with certain graph parameters
of the family of linear Jaco graphs*, arXiv:2507.16500v1, Conjecture 2.12 on
printed page 9, proposes the vertices indexed by A000149 as a dominating set of
the infinite linear Jaco graph. The sequence is indexed here from zero, so its
members are the natural floors of `(Real.exp 1) ^ t` for natural `t`.

Vertices have positive natural indices. If `i < j`, they are adjacent exactly
when `j` is at most the right endpoint `2 * i - d_i`, where `d_i` counts earlier
right endpoints reaching `i`. The table construction below evaluates this
recurrence from left to right. Index zero is retained only as a convenient
unused table entry.

The result concerns only Conjecture 2.12 as printed. It does not assert a value
of the domination number or a replacement dominating set.
-/

private def extendEndpoints (table : Array ℕ) (n : ℕ) : Array ℕ :=
  let indegree := ((Finset.range n).filter fun i => 1 ≤ i ∧ n ≤ table[i]!).card
  table.push (2 * n - indegree)

private def endpointTable : ℕ → Array ℕ
  | 0 => #[0]
  | n + 1 => extendEndpoints (endpointTable n) (n + 1)

private theorem endpointTable_size (n : ℕ) : (endpointTable n).size = n + 1 := by
  induction n with
  | zero => decide
  | succ n ih => simp [endpointTable, extendEndpoints, ih]

/-- The right endpoint `r_n = 2n - d_n` of vertex `n`. -/
def jacoRight (n : ℕ) : ℕ :=
  (endpointTable n)[n]!

private theorem jacoRight_le_twice (n : ℕ) : jacoRight n ≤ 2 * n := by
  cases n with
  | zero => decide
  | succ n =>
      rw [jacoRight, endpointTable, extendEndpoints]
      rw [show n + 1 = (endpointTable n).size by
        simpa using (endpointTable_size n).symm]
      simp

/-- Undirected adjacency in the infinite linear Jaco graph. -/
def Adj (i j : ℕ) : Prop :=
  (i < j ∧ j ≤ jacoRight i) ∨ (j < i ∧ i ≤ jacoRight j)

/-- The vertex indices in OEIS A000149, with the sequence indexed from zero. -/
def exponentialVertices : Set ℕ :=
  {n | ∃ t : ℕ, n = ⌊(Real.exp 1) ^ t⌋₊}

/-- A set dominates the positive vertices when every such vertex is in it or adjacent to it. -/
def Dominates (C : Set ℕ) : Prop :=
  ∀ v : ℕ, 1 ≤ v → ∃ c ∈ C, v = c ∨ Adj v c

/-- Kok's Conjecture 2.12: A000149 dominates the infinite linear Jaco graph. -/
def claim : Prop :=
  Dominates exponentialVertices

private theorem endpoint_eighty_eight : jacoRight 88 = 143 := by
  decide +kernel

private theorem endpoints_before_fifty_five (i : ℕ) (hi : i ≤ 54) :
    jacoRight i < 88 := by
  by_cases hsmall : i ≤ 43
  · exact (jacoRight_le_twice i).trans_lt (by omega)
  · interval_cases i <;> decide +kernel

private theorem exponential_floor_avoids_closed_neighborhood (t : ℕ) :
    ⌊(Real.exp 1) ^ t⌋₊ ∉ Set.Icc 55 143 := by
  have exp_lt_upper : Real.exp 1 < (68 : ℝ) / 25 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have lower_lt_exp : (271 : ℝ) / 100 < Real.exp 1 :=
    (show (271 : ℝ) / 100 < 2.7182818283 by norm_num).trans Real.exp_one_gt_d9
  have exp_pow_four_lt : (Real.exp 1) ^ 4 < (55 : ℝ) := calc
    (Real.exp 1) ^ 4 < ((68 : ℝ) / 25) ^ 4 :=
      pow_lt_pow_left₀ exp_lt_upper (Real.exp_pos 1).le (by decide)
    _ < (55 : ℝ) := by norm_num
  have one_le_exp : (1 : ℝ) ≤ Real.exp 1 :=
    (show (1 : ℝ) ≤ 2 by norm_num).trans Real.exp_one_gt_two.le
  have lower_pow_five : (144 : ℝ) < (Real.exp 1) ^ 5 := calc
    (144 : ℝ) < ((271 : ℝ) / 100) ^ 5 := by norm_num
    _ < (Real.exp 1) ^ 5 :=
      pow_lt_pow_left₀ lower_lt_exp (by norm_num) (by decide)
  intro hwindow
  rcases hwindow with ⟨window_lower, window_upper⟩
  by_cases ht : t ≤ 4
  · have power_lt : (Real.exp 1) ^ t < (55 : ℝ) :=
      (pow_le_pow_right₀ one_le_exp ht).trans_lt exp_pow_four_lt
    have floor_lt : ⌊(Real.exp 1) ^ t⌋₊ < 55 :=
      (Nat.floor_lt (by positivity)).2 power_lt
    omega
  · have ht5 : 5 ≤ t := by omega
    have lower_power : (144 : ℝ) ≤ (Real.exp 1) ^ t :=
      lower_pow_five.le.trans (pow_le_pow_right₀ one_le_exp ht5)
    have floor_ge : 144 ≤ ⌊(Real.exp 1) ^ t⌋₊ :=
      (Nat.le_floor_iff' (by decide)).2 lower_power
    omega

/-- Vertex 88 is neither selected nor adjacent to a selected vertex. -/
theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨c, ⟨t, rfl⟩, dominated⟩ := hclaim 88 (by decide)
  have avoids := exponential_floor_avoids_closed_neighborhood t
  rcases dominated with equal | adjacent
  · apply avoids
    simp only [Set.mem_Icc]
    omega
  · rcases adjacent with above | below
    · rw [endpoint_eighty_eight] at above
      apply avoids
      exact ⟨by omega, above.2⟩
    · have index_le : ⌊(Real.exp 1) ^ t⌋₊ ≤ 54 := by
        by_contra h
        apply avoids
        exact ⟨by omega, by omega⟩
      exact (not_le_of_gt (endpoints_before_fifty_five _ index_le)) below.2

#print axioms claim
#print axioms result

end D5.S0.Certificates.JacoExponentialDominationRefutation
