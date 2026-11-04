/- GID: D5/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Polynomials/TutteCoefficientAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Binomial]
   utility: none
   digest: Fixed-rank cyclic state counts control the signed graph coefficient error. -/

import D5.S3.Combinatorics.Graph.Polynomials.CyclicRankEstimate
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.Polynomials.TutteCoefficientAsymptotics

open CyclicRankEstimate
open scoped BigOperators Polynomial Classical

private def comparisonTerm (a : ℤ) (k s : ℕ) : ℤ :=
  if s ≤ k then (-1 : ℤ) ^ s * Ring.choose (a - s) (k - s) else 0

private theorem comparisonTerm_succ (a : ℤ) (k s : ℕ) :
    comparisonTerm a (k + 1) (s + 1) = -comparisonTerm (a - 1) k s := by
  by_cases hs : s ≤ k
  · have harg : a - ((s + 1 : ℕ) : ℤ) = a - 1 - (s : ℤ) := by push_cast; ring
    simp only [comparisonTerm, Nat.add_le_add_iff_right, hs, ↓reduceIte,
      Nat.add_sub_add_right, harg, pow_succ]
    ring
  · simp [comparisonTerm, hs]

private theorem sum_comparisonTerm {E : Type*} [DecidableEq E]
    (T : Finset E) (a : ℤ) (k : ℕ) :
    ∑ S ∈ T.powerset, comparisonTerm a k S.card = Ring.choose (a - T.card) k := by
  induction T using Finset.induction_on generalizing a k with
  | empty => simp [comparisonTerm]
  | @insert x T hx ih =>
    rw [Finset.sum_powerset_insert hx]
    have hcard (S : Finset E) (hS : S ∈ T.powerset) : (insert x S).card = S.card + 1 :=
      Finset.card_insert_of_notMem (fun h => hx (Finset.mem_powerset.mp hS h))
    cases k with
    | zero =>
      have hz : ∑ S ∈ T.powerset, comparisonTerm a 0 (insert x S).card = 0 := by
        apply Finset.sum_eq_zero
        intro S hS
        simp only [hcard S hS, comparisonTerm, show ¬ S.card + 1 ≤ 0 by omega,
          ↓reduceIte]
      rw [hz, add_zero, ih]
      simp
    | succ k =>
      have hshift : ∑ S ∈ T.powerset, comparisonTerm a (k + 1) (insert x S).card =
          -∑ S ∈ T.powerset, comparisonTerm (a - 1) k S.card := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro S hS
        rw [hcard S hS, comparisonTerm_succ]
      rw [hshift, ih, ih]
      have hleft : a - (T.card : ℤ) = (a - (T.card : ℤ) - 1) + 1 := by ring
      have hmid : a - 1 - (T.card : ℤ) = a - (T.card : ℤ) - 1 := by ring
      have hright : a - ((insert x T).card : ℤ) = a - (T.card : ℤ) - 1 := by
        rw [Finset.card_insert_of_notMem hx, Nat.cast_add, Nat.cast_one]
        ring
      rw [hright, hmid]
      have hp : Ring.choose (a - (T.card : ℤ)) (k + 1) =
          Ring.choose (a - (T.card : ℤ) - 1) k +
          Ring.choose (a - (T.card : ℤ) - 1) (k + 1) := by
        nth_rw 1 [hleft]
        exact Ring.choose_succ_succ _ _
      omega

private theorem graph_edge_card {n : ℕ} (G : SimpleGraph (Fin n)) :
    Nat.card (graphEdge G) = Nat.card G.edgeSet := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro e
  induction e using Sym2.inductionOn with
  | hf a b => exact Iff.rfl

/-- A finite constant for the sum of the rank-specific cyclic errors. -/
noncomputable def cyclicErrorConstant (D k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), 2 ^ j * cyclicPatternConstant D j

private theorem cyclic_weighted_sum_bound {n D k A : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (hD : boundedForwardDegree D G)
    (f : Finset (graphEdge G) → ℤ)
    (hzero : ∀ S, k < graphRank G S → f S = 0)
    (hterm : ∀ S ∈ cyclicStates (graphRank G), graphRank G S ≤ k →
      (f S).natAbs ≤ A * (Nat.card G.edgeSet + 1) ^ (k - graphRank G S)) :
    (∑ S ∈ cyclicStates (graphRank G), f S).natAbs ≤
      A * cyclicErrorConstant D k * (Nat.card G.edgeSet + 1) ^ (k - 1) := by
  classical
  have hfiber (j : ℕ) :
      (cyclicStates (graphRank G)).filter (fun S => graphRank G S = j) =
        cyclicRankStates G j := by
    ext S
    simp only [cyclicStates, cyclicRankStates, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hsplit : ∑ S ∈ cyclicStates (graphRank G), f S =
      ∑ j ∈ Finset.range (k + 1), ∑ S ∈ cyclicRankStates G j, f S := by
    have h := Finset.sum_fiberwise_eq_sum_filter (cyclicStates (graphRank G))
      (Finset.range (k + 1)) (graphRank G) f
    simp_rw [hfiber] at h
    rw [h]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hnot
    apply hzero
    have hn : ¬ graphRank G S ∈ Finset.range (k + 1) := by
      simpa only [Finset.mem_filter, hS, true_and] using hnot
    simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hn
  rw [hsplit]
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        (∑ S ∈ cyclicRankStates G j, f S).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        A * (2 ^ j * cyclicPatternConstant D j) *
          (Nat.card G.edgeSet + 1) ^ (k - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      by_cases hjpos : 0 < j
      · have hpow : (j - 1) + (k - j) = k - 1 := by omega
        calc
          _ ≤ ∑ S ∈ cyclicRankStates G j, (f S).natAbs := Int.natAbs_sum_le _ _
          _ ≤ ∑ _S ∈ cyclicRankStates G j, A * (Nat.card G.edgeSet + 1) ^ (k - j) := by
            apply Finset.sum_le_sum
            intro S hS
            obtain ⟨hq, hc⟩ := (Finset.mem_filter.mp hS).2
            have hcy : S ∈ cyclicStates (graphRank G) := by
              simp only [cyclicStates, Finset.mem_filter, Finset.mem_univ, true_and]
              omega
            have h := hterm S hcy (by omega)
            simpa only [hq] using h
          _ = (cyclicRankStates G j).card *
              (A * (Nat.card G.edgeSet + 1) ^ (k - j)) := by simp
          _ ≤ ((2 ^ j * cyclicPatternConstant D j) *
              (Nat.card G.edgeSet + 1) ^ (j - 1)) *
              (A * (Nat.card G.edgeSet + 1) ^ (k - j)) :=
            Nat.mul_le_mul_right _ (cyclic_rank_state_count G hG hD)
          _ = A * (2 ^ j * cyclicPatternConstant D j) *
              ((Nat.card G.edgeSet + 1) ^ (j - 1) *
                (Nat.card G.edgeSet + 1) ^ (k - j)) := by ring
          _ = _ := by rw [← pow_add, hpow]
      · have hempty : cyclicRankStates G j = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro S hS
          obtain ⟨hq, hc⟩ := (Finset.mem_filter.mp hS).2
          have hp := cyclic_graph_rank_ge_two G S (by omega)
          omega
        simp only [hempty, Finset.sum_empty, Int.natAbs_zero, zero_le]
    _ = A * cyclicErrorConstant D k * (Nat.card G.edgeSet + 1) ^ (k - 1) := by
      simp only [cyclicErrorConstant, Finset.mul_sum, Finset.sum_mul]

/-- The actual cyclic contribution uses the proved rank count and term growth. -/
theorem graph_cyclic_coefficient_estimate {n D : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (hD : boundedForwardDegree D G)
    (k : ℕ) :
    (cyclicCoefficient n k (graphRank G)
      (fun S => (graph_rank_bounds hn G S).2.2)).natAbs ≤
      (2 ^ k * cyclicErrorConstant D k) * (Nat.card G.edgeSet + 1) ^ (k - 1) := by
  apply cyclic_weighted_sum_bound G hG hD
  · intro S hS
    simp only [termCoefficient, not_le.mpr hS, ↓reduceIte]
  · intro S hS hk
    exact graph_term_coefficient_bound hn G hG k S


private theorem integer_choose_bound (a : ℤ) (t : ℕ) :
    (Ring.choose a t).natAbs ≤ (a.natAbs + t + 1) ^ t := by
  cases a with
  | ofNat a =>
    change (Ring.choose (a : ℤ) t).natAbs ≤ (a + t + 1) ^ t
    rw [Ring.choose_natCast, Int.natAbs_natCast]
    exact (Nat.choose_le_pow a t).trans (Nat.pow_le_pow_left (by omega) _)
  | negSucc a =>
    have ha : Int.negSucc a = -((a + 1 : ℕ) : ℤ) := by omega
    rw [ha, ← idealCoefficient, idealCoefficient_formula]
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
      one_pow, Int.natAbs_natCast, one_mul]
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)

private theorem comparison_term_bound {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (k : ℕ)
    (S : Finset (graphEdge G)) :
    (comparisonTerm ((n : ℤ) - 1) k S.card).natAbs ≤
      (2 * k + 3) ^ k * (Nat.card G.edgeSet + 1) ^ (k - graphRank G S) := by
  classical
  by_cases hs : S.card ≤ k
  · have hv : n ≤ Nat.card G.edgeSet + 1 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
        hG.card_vert_le_card_edgeSet_add_one
    have hr := (graph_rank_bounds hn G S).1
    have ha : ((n : ℤ) - 1 - (S.card : ℤ)).natAbs ≤ n + S.card := by
      have hc : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
      have h := Int.natAbs_sub_le ((n : ℤ) - 1) (S.card : ℤ)
      rw [hc, Int.natAbs_natCast, Int.natAbs_natCast] at h
      omega
    have hb : ((n : ℤ) - 1 - (S.card : ℤ)).natAbs + (k - S.card) + 1 ≤
        (2 * k + 3) * (Nat.card G.edgeSet + 1) := by
      have hsub : k - S.card ≤ k := Nat.sub_le _ _
      nlinarith
    simp only [comparisonTerm, hs, ↓reduceIte, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
    calc
      _ ≤ (((n : ℤ) - 1 - (S.card : ℤ)).natAbs + (k - S.card) + 1) ^
          (k - S.card) := integer_choose_bound _ _
      _ ≤ ((2 * k + 3) * (Nat.card G.edgeSet + 1)) ^ (k - S.card) :=
        Nat.pow_le_pow_left hb _
      _ = (2 * k + 3) ^ (k - S.card) *
          (Nat.card G.edgeSet + 1) ^ (k - S.card) := mul_pow _ _ _
      _ ≤ (2 * k + 3) ^ k * (Nat.card G.edgeSet + 1) ^ (k - graphRank G S) :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))
          (Nat.pow_le_pow_right (by omega) (by omega))
  · simp [comparisonTerm, hs]

private theorem forest_term_eq_comparison {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (k : ℕ) (S : Finset (graphEdge G))
    (hf : graphRank G S = S.card) :
    termCoefficient n k (graphRank G) (fun S => (graph_rank_bounds hn G S).2.2) S =
      comparisonTerm ((n : ℤ) - 1) k S.card := by
  by_cases hs : S.card ≤ k
  · have he := stateExponent_cast_eq_integer (graph_rank_bounds hn G S).2.2
    have heq : (stateExponent n (graphRank G S) S.card
        (graph_rank_bounds hn G S).2.2 : ℤ) = (n : ℤ) - 1 - S.card := by
      dsimp [stateExponentInteger] at he
      omega
    have hc : Ring.choose ((n : ℤ) - 1 - S.card) (k - S.card) =
        ((stateExponent n (graphRank G S) S.card (graph_rank_bounds hn G S).2.2).choose
          (k - S.card) : ℤ) := by rw [← heq, Ring.choose_natCast]
    simp only [termCoefficient, comparisonTerm, hf, hs, ↓reduceIte]
    simpa only [hf] using congrArg ((-1 : ℤ) ^ S.card * ·) hc.symm
  · simp [termCoefficient, comparisonTerm, hf, hs]

private theorem forest_comparison_error {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (k : ℕ) :
    forestCoefficient n k (graphRank G) (fun S => (graph_rank_bounds hn G S).2.2) -
        idealCoefficient (Nat.card G.edgeSet + 1 - n) k =
      -(∑ S ∈ cyclicStates (graphRank G), comparisonTerm ((n : ℤ) - 1) k S.card) := by
  classical
  have hv : n ≤ Nat.card G.edgeSet + 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      hG.card_vert_le_card_edgeSet_add_one
  have harg : (n : ℤ) - 1 - (Nat.card G.edgeSet : ℤ) =
      -((Nat.card G.edgeSet + 1 - n : ℕ) : ℤ) := by
    -- Connectedness and positivity ensure the natural cyclomatic number casts exactly.
    omega
  have hall : (∑ S : Finset (graphEdge G), comparisonTerm ((n : ℤ) - 1) k S.card) =
      idealCoefficient (Nat.card G.edgeSet + 1 - n) k := by
    have h := sum_comparisonTerm (Finset.univ : Finset (graphEdge G)) ((n : ℤ) - 1) k
    simpa only [Finset.powerset_univ, Finset.card_univ, ← Nat.card_eq_fintype_card,
      graph_edge_card, harg, idealCoefficient] using h
  have hfilter : Finset.univ.filter (fun S : Finset (graphEdge G) =>
      ¬ graphRank G S = S.card) = cyclicStates (graphRank G) := by
    ext S
    have hr := (graph_rank_bounds hn G S).1
    simp only [cyclicStates, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hforest : forestCoefficient n k (graphRank G)
      (fun S => (graph_rank_bounds hn G S).2.2) =
      ∑ S ∈ forestStates (graphRank G), comparisonTerm ((n : ℤ) - 1) k S.card := by
    apply Finset.sum_congr rfl
    intro S hS
    exact forest_term_eq_comparison hn G k S (Finset.mem_filter.mp hS).2
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Finset (graphEdge G))))
    (fun S => graphRank G S = S.card)
    (fun S => comparisonTerm ((n : ℤ) - 1) k S.card)
  rw [hfilter, hall] at hsplit
  change (∑ S ∈ forestStates (graphRank G), comparisonTerm ((n : ℤ) - 1) k S.card) +
    _ = _ at hsplit
  rw [hforest]
  omega

private theorem graph_first_coefficient {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    (graphStatePolynomial hn G).coeff 1 = -((Nat.card G.edgeSet + 1 - n : ℕ) : ℤ) := by
  classical
  have hcyczero : cyclicCoefficient n 1 (graphRank G)
      (fun S => (graph_rank_bounds hn G S).2.2) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hc : graphRank G S < S.card := (Finset.mem_filter.mp hS).2
    have hr := cyclic_graph_rank_ge_two G S hc
    simp only [termCoefficient, show ¬ graphRank G S ≤ 1 by omega, ↓reduceIte]
  have hcompzero : (∑ S ∈ cyclicStates (graphRank G),
      comparisonTerm ((n : ℤ) - 1) 1 S.card) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hc : graphRank G S < S.card := (Finset.mem_filter.mp hS).2
    have hr := cyclic_graph_rank_ge_two G S hc
    simp only [comparisonTerm, show ¬ S.card ≤ 1 by omega, ↓reduceIte]
  have hf := forest_comparison_error hn G hG 1
  rw [hcompzero, neg_zero, sub_eq_zero] at hf
  have hs := coeff_split (fun S => (graph_rank_bounds hn G S).1)
    (fun S => (graph_rank_bounds hn G S).2.2) (k := 1)
  change (graphStatePolynomial hn G).coeff 1 = _ at hs
  rw [hs, hcyczero, hf, add_zero]
  simp [idealCoefficient, Ring.choose_one_right]

/-- The forest error is bounded; it is not assumed to vanish. Integer binomial
    coefficients include every small-vertex case without Nat-truncated exponents. -/
theorem graph_forest_coefficient_estimate {n D : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (hD : boundedForwardDegree D G)
    (k : ℕ) :
    (forestCoefficient n k (graphRank G) (fun S => (graph_rank_bounds hn G S).2.2) -
      idealCoefficient (Nat.card G.edgeSet + 1 - n) k).natAbs ≤
      ((2 * k + 3) ^ k * cyclicErrorConstant D k) *
        (Nat.card G.edgeSet + 1) ^ (k - 1) := by
  rw [forest_comparison_error hn G hG, Int.natAbs_neg]
  apply cyclic_weighted_sum_bound G hG hD
  · intro S hS
    have hr := (graph_rank_bounds hn G S).1
    simp [comparisonTerm, show ¬ S.card ≤ k by omega]
  · intro S hS hk
    exact comparison_term_bound hn G hG k S

/-- A uniform constant for the actual signed rank-state coefficient estimate. -/
noncomputable def uniformCoefficientConstant (D k : ℕ) : ℕ :=
  (2 ^ k + (2 * k + 3) ^ k) * cyclicErrorConstant D k

/-- Uniform coefficient estimate for every connected simple graph equipped with
    a vertex order of forward degree at most D. The constant is independent of
    the graph, its carrier size, and its edge count. -/
theorem signed_tutte_coefficient_estimate {n D : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hG : G.Connected) (hD : boundedForwardDegree D G)
    (k : ℕ) (hk : 1 ≤ k) :
    ((graphStatePolynomial hn G).coeff k -
      (-1 : ℤ) ^ k * ((Nat.card G.edgeSet + 1 - n) + k - 1).choose k).natAbs ≤
      uniformCoefficientConstant D k * (Nat.card G.edgeSet + 1) ^ (k - 1) := by
  classical
  by_cases hk1 : k = 1
  · subst k
    rw [graph_first_coefficient hn G hG]
    simp
  have hs := coeff_split (fun S => (graph_rank_bounds hn G S).1)
    (fun S => (graph_rank_bounds hn G S).2.2) (k := k)
  change (graphStatePolynomial hn G).coeff k = _ at hs
  rw [← idealCoefficient_formula, hs]
  have hc := graph_cyclic_coefficient_estimate hn G hG hD k
  have hf := graph_forest_coefficient_estimate hn G hG hD k
  calc
    _ = ((forestCoefficient n k (graphRank G)
        (fun S => (graph_rank_bounds hn G S).2.2) -
        idealCoefficient (Nat.card G.edgeSet + 1 - n) k) +
        cyclicCoefficient n k (graphRank G)
          (fun S => (graph_rank_bounds hn G S).2.2)).natAbs := by congr 1; ring
    _ ≤ _ := Int.natAbs_add_le _ _
    _ ≤ _ := Nat.add_le_add hf hc
    _ = _ := by unfold uniformCoefficientConstant; ring

end D5.S3.Combinatorics.Graph.Polynomials.TutteCoefficientAsymptotics
