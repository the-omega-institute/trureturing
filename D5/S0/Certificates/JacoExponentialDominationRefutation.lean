/- GID: D5/S0/Certificates/JacoExponentialDominationRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/JacoExponentialDominationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.ExponentialBounds]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/JacoExponentialDominationRefutation.dominationClause; result=D5/S0/Certificates/JacoExponentialDominationRefutation.result; claim=D5/S0/Certificates/JacoExponentialDominationRefutation.dominationClause
   digest: Kok's Conjecture 2.12 domination clause is false: A000149 misses vertex 88 in J_infinity(x). -/

import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.JacoExponentialDominationRefutation

/-!
Kok, *Integer sequences with conjectured relation with certain graph parameters
of the family of linear Jaco graphs*, arXiv:2507.16500v1, Conjecture 2.12 on
printed page 9, proposes that the vertices indexed by A000149 form a gamma-set
of the infinite linear Jaco graph. A gamma-set is a minimum dominating set, so
its vertices must in particular dominate the graph. The sequence is indexed
here from zero, with members the natural floors of `(Real.exp 1) ^ t`.

Vertices have positive natural indices. If `i < j`, they are adjacent exactly
when `j` is at most the right endpoint `2 * i - d_i`, where `d_i` counts earlier
right endpoints reaching `i`. The table construction below evaluates this
recurrence from left to right. Index zero is retained only as a convenient
unused table entry.

The formal target is only the domination clause. The minimum-cardinality part
of the gamma-set assertion and the p-graphical clause are source boundaries and
are not encoded.
-/

private def extendEndpoints (table : Array ℕ) (n : ℕ) : Array ℕ :=
  let indegree := ((Finset.range n).filter fun i => 1 ≤ i ∧ n ≤ table[i]!).card
  table.push (2 * n - indegree)

private def endpointTable : ℕ → Array ℕ
  | 0 => #[0]
  | n + 1 => extendEndpoints (endpointTable n) (n + 1)

/-- The right endpoint `r_n = 2n - d_n` of vertex `n`. -/
def jacoRight (n : ℕ) : ℕ :=
  (endpointTable n).back!

/-- The right endpoints increase by at least one at every step. -/
theorem jacoRight_succ_ge : ∀ n : ℕ, jacoRight n + 1 ≤ jacoRight (n + 1) := by
  intro n
  have table_size : ∀ k : ℕ, (endpointTable k).size = k + 1 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih => simp [endpointTable, extendEndpoints, ih]
  cases n with
  | zero => decide +kernel
  | succ n =>
      let oldDegree := ((Finset.range (n + 1)).filter fun i =>
        1 ≤ i ∧ n + 1 ≤ (endpointTable n)[i]!)
      let newDegree := ((Finset.range (n + 1 + 1)).filter fun i =>
        1 ≤ i ∧ n + 1 < (endpointTable (n + 1))[i]!)
      have old_formula : jacoRight (n + 1) = 2 * (n + 1) - oldDegree.card := by
        simp [jacoRight, endpointTable, extendEndpoints, oldDegree]
      have new_formula : jacoRight (n + 1 + 1) =
          2 * (n + 1 + 1) - newDegree.card := by
        simp [jacoRight, endpointTable, extendEndpoints, newDegree]
      have prefix_agreement (i : ℕ) (hi : i < n + 1) :
          (endpointTable (n + 1))[i]! = (endpointTable n)[i]! := by
        have hiOld : i < (endpointTable n).size := by
          rw [table_size]
          exact hi
        have hiNew : i < (endpointTable (n + 1)).size := by
          rw [table_size]
          omega
        rw [getElem!_pos (endpointTable (n + 1)) i hiNew]
        rw [getElem!_pos (endpointTable n) i hiOld]
        simp only [endpointTable, extendEndpoints]
        exact Array.getElem_push_lt hiOld
      have degree_subset : newDegree ⊆ insert (n + 1) oldDegree := by
        intro i hi
        simp only [newDegree, Finset.mem_filter, Finset.mem_range] at hi
        by_cases htop : i = n + 1
        · simp [htop]
        · have hilow : i < n + 1 := by omega
          have endpoint_ge : n + 1 ≤ (endpointTable n)[i]! := by
            rw [← prefix_agreement i hilow]
            omega
          simp only [Finset.mem_insert, oldDegree, Finset.mem_filter, Finset.mem_range]
          exact Or.inr ⟨hilow, hi.2.1, endpoint_ge⟩
      have degree_growth : newDegree.card ≤ oldDegree.card + 1 :=
        (Finset.card_le_card degree_subset).trans (Finset.card_insert_le _ _)
      have old_degree_le : oldDegree.card ≤ n + 1 := by
        calc
          oldDegree.card ≤ (Finset.range (n + 1)).card := by
            exact Finset.card_le_card (by
              simpa only [oldDegree] using Finset.filter_subset
                (fun i => 1 ≤ i ∧ n + 1 ≤ (endpointTable n)[i]!)
                (Finset.range (n + 1)))
          _ = n + 1 := Finset.card_range (n + 1)
      omega

/-- Undirected adjacency in the infinite linear Jaco graph. -/
def Adj (i j : ℕ) : Prop :=
  (i < j ∧ j ≤ jacoRight i) ∨ (j < i ∧ i ≤ jacoRight j)

/-- The vertex indices in OEIS A000149, with the sequence indexed from zero. -/
def exponentialVertices : Set ℕ :=
  {n | ∃ t : ℕ, n = ⌊(Real.exp 1) ^ t⌋₊}

/-- A set dominates the positive vertices when every such vertex is in it or adjacent to it. -/
def Dominates (C : Set ℕ) : Prop :=
  ∀ v : ℕ, 1 ≤ v → ∃ c ∈ C, v = c ∨ Adj v c

/--
The domination clause of Kok's Conjecture 2.12: the A000149 vertices dominate J_∞(x).
A γ-set is by definition dominating, so refuting this clause refutes the γ-set assertion.
The minimality and p-graphical clauses of the conjecture are source boundaries and are not encoded.
-/
def dominationClause : Prop :=
  Dominates exponentialVertices

/-- Vertex 88 is neither selected nor adjacent to a selected vertex. -/
theorem result : ¬ dominationClause := by
  have right_iterated : ∀ a b : ℕ, a ≤ b →
      jacoRight a + (b - a) ≤ jacoRight b := by
    intro a b hab
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    simp only [Nat.add_sub_cancel_left]
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          jacoRight a + (k + 1) = (jacoRight a + k) + 1 := by omega
          _ ≤ jacoRight (a + k) + 1 := Nat.add_le_add_right ih 1
          _ ≤ jacoRight ((a + k) + 1) := jacoRight_succ_ge (a + k)
          _ = jacoRight (a + (k + 1)) := congrArg jacoRight (by omega)
  have endpoint_fifty_four : jacoRight 54 = 87 := by decide +kernel
  have endpoint_eighty_eight : jacoRight 88 = 143 := by decide +kernel
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
  intro hdomination
  obtain ⟨m, ⟨t, rfl⟩, dominated⟩ := hdomination 88 (by decide)
  by_cases ht : t ≤ 4
  · have power_lt : (Real.exp 1) ^ t < (55 : ℝ) :=
      (pow_le_pow_right₀ one_le_exp ht).trans_lt exp_pow_four_lt
    have floor_lt : ⌊(Real.exp 1) ^ t⌋₊ < 55 :=
      (Nat.floor_lt (by positivity)).2 power_lt
    have index_le : ⌊(Real.exp 1) ^ t⌋₊ ≤ 54 := by omega
    have endpoint_le : jacoRight ⌊(Real.exp 1) ^ t⌋₊ ≤ 87 := by
      have h := right_iterated ⌊(Real.exp 1) ^ t⌋₊ 54 index_le
      omega
    rcases dominated with equal | adjacent
    · omega
    · rcases adjacent with above | below
      · omega
      · omega
  · have ht5 : 5 ≤ t := by omega
    have lower_power : (144 : ℝ) ≤ (Real.exp 1) ^ t :=
      lower_pow_five.le.trans (pow_le_pow_right₀ one_le_exp ht5)
    have floor_ge : 144 ≤ ⌊(Real.exp 1) ^ t⌋₊ :=
      (Nat.le_floor_iff' (by decide)).2 lower_power
    rcases dominated with equal | adjacent
    · omega
    · rcases adjacent with above | below
      · rw [endpoint_eighty_eight] at above
        omega
      · omega

#print axioms jacoRight_succ_ge
#print axioms dominationClause
#print axioms result

end D5.S0.Certificates.JacoExponentialDominationRefutation
