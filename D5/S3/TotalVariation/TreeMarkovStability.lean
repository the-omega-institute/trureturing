/- GID: D5/S3/TotalVariation/TreeMarkovStability
   generality: G
   mirror-B: D5/B/S3/TotalVariation/TreeMarkovStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite tree replacement telescopes give the degree-weighted total-variation bound and the sharp edge coefficient.
-/

import D5.S3.TotalVariation.Metric
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import D5.S3.Entropy.Forgetting.PushforwardComposition
import D5.S3.Divergence.ChainRule

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


namespace Actual

open D5.S3.Entropy.Forgetting.CapacityMonotone (pushforward)
open D5.S3.Entropy.Forgetting.PushforwardComposition (pushforward_comp)
open D5.S3.Divergence.ChainRule (marginal conditional)

/-- A conditional row completed by a prescribed probability row at zero mass. -/
def completedConditional {A B : Type*} [Fintype B]
    (π : A × B → ℝ) (fallback : B → ℝ) (a : A) (b : B) : ℝ :=
  if marginal π a = 0 then fallback b else conditional π a b

private theorem completed_conditional_properties {A B : Type*} [Fintype B]
    (π : A × B → ℝ) (fallback : B → ℝ)
    (hπ : ∀ z, 0 ≤ π z) (hf : (∀ b, 0 ≤ fallback b) ∧ ∑ b, fallback b = 1) :
    (∀ a b, 0 ≤ completedConditional π fallback a b) ∧
    (∀ a, ∑ b, completedConditional π fallback a b = 1) ∧
    (∀ a b, marginal π a * completedConditional π fallback a b = π (a,b)) := by
  classical
  have hm (a : A) : 0 ≤ marginal π a := Finset.sum_nonneg fun b _ => hπ (a,b)
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    unfold completedConditional
    split_ifs
    · exact hf.1 b
    · exact div_nonneg (hπ _) (hm a)
  · intro a
    by_cases h : marginal π a = 0
    · simp [completedConditional, h, hf.2]
    · simp only [completedConditional, if_neg h, conditional]
      rw [← Finset.sum_div]
      exact div_self h
  · intro a b
    by_cases h : marginal π a = 0
    · have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hπ (a,c))).mp h b
        (Finset.mem_univ b)
      simp [completedConditional, h, hz]
    · simp only [completedConditional, if_neg h, conditional]
      exact mul_div_cancel₀ _ h

/-- Retain the old configuration and add one new coordinate through its parent. -/
def extend {Ω A B : Type*} (p : Ω → ℝ) (f : Ω → A) (K : A → B → ℝ) : Ω × B → ℝ :=
  fun z => p z.1 * K (f z.1) z.2

private theorem extend_same_kernel {Ω A B : Type*} [Fintype Ω] [Fintype B]
    (p q : Ω → ℝ) (f : Ω → A) (K : A → B → ℝ)
    (hK : (∀ a b, 0 ≤ K a b) ∧ ∀ a, ∑ b, K a b = 1) :
    totalVariation (extend p f K) (extend q f K) = totalVariation p q := by
  unfold totalVariation extend
  rw [Fintype.sum_prod_type]
  simp_rw [← sub_mul, abs_mul, abs_of_nonneg (hK.1 _ _), ← Finset.mul_sum, hK.2,
    mul_one]

private theorem sum_pushforward_mul {Ω A : Type*} [Fintype Ω] [Fintype A]
    (p : Ω → ℝ) (f : Ω → A) (h : A → ℝ) :
    (∑ a, pushforward f p a * h a) = ∑ x, p x * h (f x) := by
  classical
  simp only [pushforward, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

private theorem extend_change_kernel {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (q : Ω → ℝ) (f : Ω → A) (K L : A → B → ℝ) (hq : ∀ x, 0 ≤ q x) :
    totalVariation (extend q f K) (extend q f L) =
      totalVariation (fun z : A × B => pushforward f q z.1 * K z.1 z.2)
        (fun z => pushforward f q z.1 * L z.1 z.2) := by
  have hn (a : A) : 0 ≤ pushforward f q a := by
    classical
    exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all [pushforward]
  unfold totalVariation extend
  simp_rw [Fintype.sum_prod_type, ← mul_sub, abs_mul, abs_of_nonneg (hq _),
    abs_of_nonneg (hn _), ← Finset.mul_sum]
  rw [sum_pushforward_mul]

/-- The actual leaf extension estimate, with its parent laws obtained as marginals. -/
private theorem leaf_extension_bound {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (p q : Ω → ℝ) (f : Ω → A) (π χ : A × B → ℝ) (K L : A → B → ℝ)
    (hq : ∀ x, 0 ≤ q x)
    (hK : (∀ a b, 0 ≤ K a b) ∧ ∀ a, ∑ b, K a b = 1)
    (hp : pushforward f p = marginal π) (hq' : pushforward f q = marginal χ)
    (hπ : ∀ a b, marginal π a * K a b = π (a,b))
    (hχ : ∀ a b, marginal χ a * L a b = χ (a,b)) :
    totalVariation (extend p f K) (extend q f L) ≤
      totalVariation p q + totalVariation π χ + totalVariation (marginal π) (marginal χ) := by
  let νK : A × B → ℝ := fun z => marginal χ z.1 * K z.1 z.2
  have h1 := total_variation_triangle (extend p f K) (extend q f K) (extend q f L)
  rw [extend_same_kernel p q f K hK, extend_change_kernel q f K L hq] at h1
  rw [hq'] at h1
  have hχfun : (fun z : A × B => marginal χ z.1 * L z.1 z.2) = χ :=
    funext fun z => hχ z.1 z.2
  rw [hχfun] at h1
  have h2 := total_variation_triangle νK π χ
  have h3 : totalVariation νK π = totalVariation (marginal χ) (marginal π) := by
    have he : π = extend (marginal π) id K := (funext fun z => hπ z.1 z.2).symm
    rw [he]
    exact extend_same_kernel _ _ id K hK
  rw [h3, total_variation_comm (marginal χ) (marginal π)] at h2
  exact le_trans h1 (by dsimp [νK] at h2; linarith)

private theorem extend_marginals {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (p : Ω → ℝ) (f : Ω → A) (K : A → B → ℝ)
    (hK : ∀ a, ∑ b, K a b = 1) :
    pushforward Prod.fst (extend p f K) = p ∧
      pushforward (fun z : Ω × B => (f z.1,z.2)) (extend p f K) =
        fun z : A × B => pushforward f p z.1 * K z.1 z.2 := by
  classical
  constructor
  · funext x
    simp only [pushforward, extend, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x]
    · simp [← Finset.mul_sum, hK]
    · intro y _ hy
      simp [hy]
    · simp
  · funext z
    rcases z with ⟨a,b⟩
    simp only [pushforward, extend, Fintype.sum_prod_type, Prod.mk.injEq]
    simp_rw [show ∀ x : Ω, (∑ y : B, if f x = a ∧ y = b then p x * K (f x) y else 0) =
      if f x = a then p x * K a b else 0 by
      intro x; by_cases hx : f x = a <;> simp [hx]]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all

/-- A finite tree is reduced to an edge by removing leaves; vertices are never identified. -/
inductive TreeOrder : {V : Type} → SimpleGraph V → Type 1
  | edge {V : Type} {G : SimpleGraph V} (r s : V) (hne : r ≠ s)
      (cover : ∀ v, v = r ∨ v = s) (adj : G.Adj r s) : TreeOrder G
  | leaf {V : Type} {G : SimpleGraph V} (v : V) (u : {w : V // w ≠ v})
      (adj : ∀ w, G.Adj v w ↔ w = u.val)
      (old : TreeOrder (G.induce {w | w ≠ v})) : TreeOrder G

private theorem tree_order_exists {V : Type} [Fintype V] (G : SimpleGraph V)
    (hG : G.IsTree) (hV : 2 ≤ Fintype.card V) : Nonempty (TreeOrder G) := by
  classical
  have aux : ∀ n : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → G.IsTree → 2 ≤ n → Nonempty (TreeOrder G) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ G hn ht hn2
      letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨v, hv⟩ := ht.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      have huv : u ≠ v := G.ne_of_adj hu.symm
      by_cases htwo : n = 2
      · have cover : ∀ w : V, w = v ∨ w = u := by
          intro w
          by_contra h
          have h3 : 3 ≤ Fintype.card V :=
            Fintype.card_le_of_injective (fun b : Fin 3 => ![v,u,w] b) (by
              intro a b he
              fin_cases a <;> fin_cases b <;> simp_all)
          omega
        exact ⟨TreeOrder.edge v u (Ne.symm huv) cover hu⟩
      · let W := {w : V // w ≠ v}
        let G' : SimpleGraph W := G.induce {w | w ≠ v}
        have hcard : Fintype.card W + 1 = Fintype.card V := by
          simpa [W] using (Fintype.card_subtype_compl (fun w : V => w = v))
        have ht' : G'.IsTree :=
          ⟨by simpa [G', W, Set.compl_singleton_iff] using
            ht.connected.induce_compl_singleton_of_degree_eq_one hv,
            ht.isAcyclic.induce _⟩
        obtain ⟨t⟩ := ih (Fintype.card W) (by omega) W G' rfl ht' (by omega)
        exact ⟨TreeOrder.leaf v ⟨u,huv⟩ (by
          intro w
          exact ⟨fun hw => huniq w hw, fun hw => hw ▸ hu⟩) t⟩
  exact aux (Fintype.card V) V G rfl hG hV

end Actual

end D5.S3.TotalVariation.TreeMarkovStability
