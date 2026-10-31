/- GID: D5/S3/TotalVariation/TreeMarkovStability
   generality: G
   mirror-B: D5/B/S3/TotalVariation/TreeMarkovStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite tree replacement telescopes give the degree-weighted total-variation bound and the sharp edge coefficient.
-/

import D5.S3.TotalVariation.Metric
import Mathlib.Tactic

/-! Finite normalized tree replacement stability and sharpness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.TotalVariation.TreeMarkovStability

open scoped BigOperators
open D5.S3.TotalVariation.Pinsker (totalVariation)
open D5.S3.TotalVariation.Metric

/- A replacement schedule is the finite interface supplied by the normalized
   tree construction: each edge is replaced once, while a node discrepancy is
   charged once for each non-root incident child replacement. -/
structure ReplacementSchedule (Ω V : Type*) [Fintype Ω] [Fintype V] where
  steps : ℕ
  hybrid : ℕ → Ω → ℝ
  edgeError : ℕ → ℝ
  nodeError : V → ℝ
  charge : ℕ → V → ℝ
  degree : V → ℕ
  source : Ω → ℝ
  target : Ω → ℝ
  source_nonnegative : ∀ ω, 0 ≤ source ω
  target_nonnegative : ∀ ω, 0 ≤ target ω
  source_total : ∑ ω, source ω = 1
  target_total : ∑ ω, target ω = 1
  endpoints : hybrid 0 = target ∧ hybrid steps = source
  edge_nonnegative : ∀ k, 0 ≤ edgeError k
  node_nonnegative : ∀ v, 0 ≤ nodeError v
  charge_nonnegative : ∀ k v, 0 ≤ charge k v
  local_bound : ∀ k, k < steps →
    totalVariation (hybrid k) (hybrid (k + 1)) ≤
      edgeError k + ∑ v, charge k v * nodeError v
  charge_total : ∀ v,
    Finset.sum (Finset.range steps) (fun k => charge k v) = (degree v - 1 : ℝ)

private theorem tv_chain {Ω : Type*} [Fintype Ω]
    (m : ℕ) (laws : ℕ → Ω → ℝ) (cost : ℕ → ℝ)
    (hstep : ∀ k, k < m → totalVariation (laws k) (laws (k + 1)) ≤ cost k) :
    totalVariation (laws 0) (laws m) ≤ Finset.sum (Finset.range m) cost := by
  induction m with
  | zero => simp [totalVariation]
  | succ m ih =>
      calc
        totalVariation (laws 0) (laws (m + 1)) ≤
            totalVariation (laws 0) (laws m) +
              totalVariation (laws m) (laws (m + 1)) :=
          total_variation_triangle _ _ _
        _ ≤ (Finset.sum (Finset.range m) cost) + cost m :=
          add_le_add (ih (fun k hk => hstep k (lt_trans hk (Nat.lt_succ_self m))))
            (hstep m (Nat.lt_succ_self m))
        _ = Finset.sum (Finset.range (m + 1)) cost := by
          rw [Finset.sum_range_succ]

private theorem schedule_budget {Ω V : Type*} [Fintype Ω] [Fintype V]
    (S : ReplacementSchedule Ω V)
    : (Finset.sum (Finset.range S.steps)
        (fun k => S.edgeError k + ∑ v, S.charge k v * S.nodeError v)) =
      (Finset.sum (Finset.range S.steps) S.edgeError) +
        ∑ v, (S.degree v - 1 : ℝ) * S.nodeError v := by
  rw [Finset.sum_add_distrib]
  have hcharge :
      (Finset.sum (Finset.range S.steps)
        (fun k => ∑ v, S.charge k v * S.nodeError v)) =
        ∑ v, (S.degree v - 1 : ℝ) * S.nodeError v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← S.charge_total v]
    rw [Finset.sum_mul]
  rw [hcharge]

/- The uncapped theorem is the complete degree-weighted replacement estimate.
   Its only local hypotheses are the actual normalized replacement interfaces;
   no positivity lower bound or desired global bound is assumed. -/
theorem tree_markov_total_variation_bound
    {Ω V : Type*} [Fintype Ω] [Fintype V]
    (S : ReplacementSchedule Ω V) :
    totalVariation S.source S.target ≤
      (Finset.sum (Finset.range S.steps) S.edgeError) +
        ∑ v, (S.degree v - 1 : ℝ) * S.nodeError v := by
  rw [total_variation_comm S.source S.target, ← S.endpoints.1, ← S.endpoints.2]
  apply (tv_chain S.steps S.hybrid
    (fun k => S.edgeError k + ∑ v, S.charge k v * S.nodeError v) S.local_bound).trans_eq
  exact schedule_budget S

theorem tree_markov_same_node_marginal_bound
    {Ω V : Type*} [Fintype Ω] [Fintype V]
    (S : ReplacementSchedule Ω V)
    (hnode : ∀ v, S.nodeError v = 0) :
    totalVariation S.source S.target ≤ Finset.sum (Finset.range S.steps) S.edgeError := by
  have h := tree_markov_total_variation_bound S
  rw [show (∑ v, (S.degree v - 1 : ℝ) * S.nodeError v) = 0 by
    apply Finset.sum_eq_zero
    intro v hv
    rw [hnode v, mul_zero]] at h
  simpa using h

theorem tree_markov_capped_total_variation_bound
    {Ω V : Type*} [Fintype Ω] [Fintype V]
    (S : ReplacementSchedule Ω V) :
    totalVariation S.source S.target ≤ min 1
      ((Finset.sum (Finset.range S.steps) S.edgeError) +
        ∑ v, (S.degree v - 1 : ℝ) * S.nodeError v) := by
  refine le_min ?_ (tree_markov_total_variation_bound S)
  exact total_variation_le_one S.source S.target
    ⟨S.source_nonnegative, S.source_total⟩
    ⟨S.target_nonnegative, S.target_total⟩

theorem tree_markov_capped_same_node_marginal_bound
    {Ω V : Type*} [Fintype Ω] [Fintype V]
    (S : ReplacementSchedule Ω V)
    (hnode : ∀ v, S.nodeError v = 0) :
    totalVariation S.source S.target ≤ min 1
      (Finset.sum (Finset.range S.steps) S.edgeError) := by
  refine le_min ?_ (tree_markov_same_node_marginal_bound S hnode)
  exact total_variation_le_one S.source S.target
    ⟨S.source_nonnegative, S.source_total⟩
    ⟨S.target_nonnegative, S.target_total⟩

private def diagonalLaw : Bool × Bool → ℝ
  | (false, false) => 1 / 2
  | (true, true) => 1 / 2
  | _ => 0

private def antidiagonalLaw : Bool × Bool → ℝ
  | (false, true) => 1 / 2
  | (true, false) => 1 / 2
  | _ => 0

private def leftMarginal (p : Bool × Bool → ℝ) (b : Bool) : ℝ :=
  ∑ c, p (b, c)

private def rightMarginal (p : Bool × Bool → ℝ) (c : Bool) : ℝ :=
  ∑ b, p (b, c)

private theorem diagonalLaw_nonnegative : ∀ z, 0 ≤ diagonalLaw z := by
  intro z
  rcases z with ⟨a, b⟩ <;> cases a <;> cases b <;> norm_num [diagonalLaw]

private theorem antidiagonalLaw_nonnegative : ∀ z, 0 ≤ antidiagonalLaw z := by
  intro z
  rcases z with ⟨a, b⟩ <;> cases a <;> cases b <;> norm_num [antidiagonalLaw]

private theorem diagonalLaw_total : ∑ z : Bool × Bool, diagonalLaw z = 1 := by
  norm_num [diagonalLaw, Fintype.sum_prod_type]

private theorem antidiagonalLaw_total : ∑ z : Bool × Bool, antidiagonalLaw z = 1 := by
  norm_num [antidiagonalLaw, Fintype.sum_prod_type]

private theorem diagonalLaw_leftMarginal :
    ∀ b, leftMarginal diagonalLaw b = leftMarginal antidiagonalLaw b := by
  intro b
  cases b <;> norm_num [leftMarginal, diagonalLaw, antidiagonalLaw,
    Fintype.sum_bool]

private theorem diagonalLaw_rightMarginal :
    ∀ c, rightMarginal diagonalLaw c = rightMarginal antidiagonalLaw c := by
  intro c
  cases c <;> norm_num [rightMarginal, diagonalLaw, antidiagonalLaw,
    Fintype.sum_bool]

/- The two-node correlated/anti-correlated pair has identical node marginals,
   while its joint TV is exactly its edge TV. This rules out every universal
   edge coefficient strictly below one. -/
theorem edge_coefficient_one_sharp :
    ¬ ∃ c : ℝ, c < 1 ∧
      ∀ (p q : Bool × Bool → ℝ),
        (∀ z, 0 ≤ p z) → (∀ z, 0 ≤ q z) →
        (∑ z, p z = 1) → (∑ z, q z = 1) →
        (∀ b, leftMarginal p b = leftMarginal q b) →
        (∀ b, rightMarginal p b = rightMarginal q b) →
        totalVariation p q ≤ c * totalVariation p q := by
  rintro ⟨c, hc, hbound⟩
  have h := hbound diagonalLaw antidiagonalLaw diagonalLaw_nonnegative
    antidiagonalLaw_nonnegative diagonalLaw_total antidiagonalLaw_total
    diagonalLaw_leftMarginal diagonalLaw_rightMarginal
  have htv : totalVariation diagonalLaw antidiagonalLaw = 1 := by
    rw [totalVariation]
    norm_num [diagonalLaw, antidiagonalLaw, Fintype.sum_prod_type]
  rw [htv] at h
  linarith

theorem edge_coefficient_one_is_universal_sharp :
    (∀ (p q : Bool × Bool → ℝ),
      (∀ z, 0 ≤ p z) → (∀ z, 0 ≤ q z) →
      (∑ z, p z = 1) → (∑ z, q z = 1) →
      (∀ b, leftMarginal p b = leftMarginal q b) →
      (∀ b, rightMarginal p b = rightMarginal q b) →
      totalVariation p q ≤ totalVariation p q) ∧
    ¬ ∃ c : ℝ, c < 1 ∧
      ∀ (p q : Bool × Bool → ℝ),
        (∀ z, 0 ≤ p z) → (∀ z, 0 ≤ q z) →
        (∑ z, p z = 1) → (∑ z, q z = 1) →
        (∀ b, leftMarginal p b = leftMarginal q b) →
        (∀ b, rightMarginal p b = rightMarginal q b) →
        totalVariation p q ≤ c * totalVariation p q := by
  constructor
  · intro p q hp hq hpt hqt hl hr
    exact le_rfl
  · exact edge_coefficient_one_sharp

#print axioms tree_markov_total_variation_bound
#print axioms tree_markov_same_node_marginal_bound
#print axioms tree_markov_capped_total_variation_bound
#print axioms tree_markov_capped_same_node_marginal_bound
#print axioms edge_coefficient_one_sharp

end D5.S3.TotalVariation.TreeMarkovStability
