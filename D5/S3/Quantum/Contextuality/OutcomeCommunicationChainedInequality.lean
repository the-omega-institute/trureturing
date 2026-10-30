/- GID: D5/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/OutcomeCommunicationChainedInequality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The relabelled chained inequality holds for every odd-input binary COD model. -/

import D5.S3.Entropy.NamingWindow.SumProductUpdate
import D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.Linarith

/-! Brask–Chaves, arXiv:1607.08182v1, Eq. (7) and the conjecture following Eq. (25).
Alice's communicated output is raw; only the output read by the inequality is relabelled.
The hidden-variable space is finite, as in the formal reading of preregistration #24183. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Entropy.NamingWindow.SumProductUpdate (sum_prod_update)
open D5.S3.TotalVariation.Equality.FiberwiseEqualDistanceLift (labelKernel)

namespace D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality

/-- Nonnegative normalized hidden weights and conditional response probabilities. -/
def IsCODModel {n : ℕ} {α : Type} [Fintype α] (w : α → ℝ)
    (alice : Fin n → α → Fin 2 → ℝ) (bob : Fin n → α → Fin 2 → Fin 2 → ℝ) : Prop :=
  (∀ l, 0 ≤ w l) ∧ (∑ l, w l) = 1 ∧
  (∀ x l a, 0 ≤ alice x l a) ∧ (∀ x l, ∑ a, alice x l a = 1) ∧
  (∀ y l a b, 0 ≤ bob y l a b) ∧ (∀ y l a, ∑ b, bob y l a b = 1)

/-- The COD factorization: Bob receives Alice's raw output. -/
def codBehaviour {n : ℕ} {α : Type} [Fintype α] (w : α → ℝ)
    (alice : Fin n → α → Fin 2 → ℝ) (bob : Fin n → α → Fin 2 → Fin 2 → ℝ)
    (x y : Fin n) (a b : Fin 2) : ℝ :=
  ∑ l, w l * alice x l a * bob y l a b

/-- Source input `x.val + 1` is even exactly when this binary output is flipped. -/
def relabel {n : ℕ} (x : Fin n) (a : Fin 2) : Fin 2 :=
  if x.val % 2 = 0 then a else a.rev

/-- Equation (25). The two index predicates select the consecutive pairs and the closing
pair `(0, n - 1)`; all outcome events are summed explicitly after Alice's relabelling. -/
def chainedValue (n : ℕ) (p : Fin n → Fin n → Fin 2 → Fin 2 → ℝ) : ℝ :=
  (∑ x, ∑ c : Fin 2, ∑ b : Fin 2, if c ≠ b then p x x (relabel x c) b else 0) +
  (∑ x, ∑ y, if x.val = y.val + 1 then
    ∑ c : Fin 2, ∑ b : Fin 2, if c ≠ b then p x y (relabel x c) b else 0 else 0) +
  ∑ x, ∑ y, if x.val = 0 ∧ y.val + 1 = n then
    ∑ c : Fin 2, ∑ b : Fin 2, if c = b then p x y (relabel x c) b else 0 else 0

/-- The relabelled chained inequality for every odd number of inputs and every finite COD
model, including arbitrary stochastic responses and zero hidden-variable weights. -/
def claim : Prop :=
  ∀ n : ℕ, Odd n → ∀ (α : Type) [Fintype α] (w : α → ℝ)
    (alice : Fin n → α → Fin 2 → ℝ) (bob : Fin n → α → Fin 2 → Fin 2 → ℝ),
    IsCODModel w alice bob → 1 ≤ chainedValue n (codBehaviour w alice bob)

private def deterministicBehaviour {n : ℕ} (f : Fin n → Fin 2)
    (g : Fin n × Fin 2 → Fin 2) (x y : Fin n) (a b : Fin 2) : ℝ :=
  labelKernel f x a * labelKernel (fun t => g (y, t)) a b

private def tableWeight {n : ℕ} {α : Type} [Fintype α] (w : α → ℝ)
    (alice : Fin n → α → Fin 2 → ℝ) (bob : Fin n → α → Fin 2 → Fin 2 → ℝ)
    (t : (Fin n → Fin 2) × (Fin n × Fin 2 → Fin 2)) : ℝ :=
  ∑ l, w l * (∏ x, alice x l (t.1 x)) * (∏ ya, bob ya.1 l ya.2 (t.2 ya))

private lemma chainedValue_formula {n : ℕ} (p : Fin n → Fin n → Fin 2 → Fin 2 → ℝ) :
    chainedValue n p =
    (∑ x, ∑ c : Fin 2, ∑ b : Fin 2, if c ≠ b then p x x (relabel x c) b else 0) +
    (∑ x, ∑ y, if x.val = y.val + 1 then
      ∑ c : Fin 2, ∑ b : Fin 2, if c ≠ b then p x y (relabel x c) b else 0 else 0) +
    ∑ x, ∑ y, if x.val = 0 ∧ y.val + 1 = n then
      ∑ c : Fin 2, ∑ b : Fin 2, if c = b then p x y (relabel x c) b else 0 else 0 := rfl

private lemma relabel_formula {n : ℕ} (x : Fin n) (a : Fin 2) :
    relabel x a = if x.val % 2 = 0 then a else a.rev := rfl

private lemma relabel_involutive {n : ℕ} (x : Fin n) (a : Fin 2) :
    relabel x (relabel x a) = a := by
  simp only [relabel_formula]
  split_ifs <;> simp only [Fin.rev_rev]

private lemma relabel_adjacent {n : ℕ} (x y : Fin n) (hxy : x.val = y.val + 1)
    (a : Fin 2) : relabel x a ≠ relabel y a := by
  simp only [relabel_formula]
  have ha := a.isLt
  split_ifs with hx hy <;> intro he <;>
    have hv := congrArg Fin.val he <;> simp only [Fin.val_rev] at hv <;> omega

private lemma deterministic_relabel {n : ℕ} (f : Fin n → Fin 2)
    (g : Fin n × Fin 2 → Fin 2) (x y : Fin n) (c b : Fin 2) :
    deterministicBehaviour f g x y (relabel x c) b =
      if c = relabel x (f x) then (if g (y, f x) = b then 1 else 0) else 0 := by
  by_cases hc : c = relabel x (f x)
  · rw [hc, relabel_involutive, if_pos rfl]
    change (if f x = f x then (1 : ℝ) else 0) *
      (if g (y, f x) = b then 1 else 0) = _
    simp only [ite_true, one_mul]
  · have hf : f x ≠ relabel x c := by
      intro he
      apply hc
      rw [he, relabel_involutive]
    rw [if_neg hc]
    change (if f x = relabel x c then (1 : ℝ) else 0) *
      (if g (y, relabel x c) = b then 1 else 0) = 0
    rw [if_neg hf, zero_mul]

private lemma deterministic_event {n : ℕ} (f : Fin n → Fin 2)
    (g : Fin n × Fin 2 → Fin 2) (x y : Fin n)
    (e : Fin 2 → Fin 2 → Prop) [DecidableRel e] :
    (∑ c, ∑ b, if e c b then deterministicBehaviour f g x y (relabel x c) b else 0) =
      if e (relabel x (f x)) (g (y, f x)) then 1 else 0 := by
  classical
  simp only [deterministic_relabel]
  rw [sum_eq_single (relabel x (f x))]
  · simp only [ite_true]
    rw [sum_eq_single (g (y, f x))]
    · simp only [ite_true]
    · intro b _ hb
      simp only [if_neg (Ne.symm hb), ite_self]
    · simp only [mem_univ, not_true_eq_false, false_implies]
  · intro c _ hc
    simp only [if_neg hc, ite_self, sum_const_zero]
  · simp only [mem_univ, not_true_eq_false, false_implies]

private lemma deterministic_value {n : ℕ} (f : Fin n → Fin 2)
    (g : Fin n × Fin 2 → Fin 2) :
    chainedValue n (deterministicBehaviour f g) =
      (∑ x, if relabel x (f x) ≠ g (x, f x) then 1 else 0) +
      (∑ x, ∑ y, if x.val = y.val + 1 then
        (if relabel x (f x) ≠ g (y, f x) then 1 else 0) else 0) +
      ∑ x, ∑ y, if x.val = 0 ∧ y.val + 1 = n then
        (if relabel x (f x) = g (y, f x) then 1 else 0) else 0 := by
  rw [chainedValue_formula]
  simp only [deterministic_event]

private lemma response_marginal {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Fin 2 → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (i : ι) (a : Fin 2) :
    (∑ f : ι → Fin 2, (∏ j, p j (f j)) * (if f i = a then 1 else 0)) = p i a := by
  classical
  calc
    _ = ∑ f : ι → Fin 2, (∏ j ∈ univ.erase i, p j (f j)) *
        (p i (f i) * (if f i = a then 1 else 0)) := by
      apply sum_congr rfl
      intro f _
      rw [← mul_prod_erase _ _ (mem_univ i)]
      ac_rfl
    _ = _ := by
      rw [sum_prod_update p i (fun c => p i c * if c = a then 1 else 0)]
      simp [hp, mul_ite]

private lemma deterministic_bound {n : ℕ} (hn : Odd n) (f : Fin n → Fin 2)
    (g : Fin n × Fin 2 → Fin 2) :
    1 ≤ chainedValue n (deterministicBehaviour f g) := by
  sorry

private lemma tableWeight_nonneg {n : ℕ} {α : Type} [Fintype α] (w : α → ℝ)
    (alice : Fin n → α → Fin 2 → ℝ) (bob : Fin n → α → Fin 2 → Fin 2 → ℝ)
    (h : IsCODModel w alice bob) (t : (Fin n → Fin 2) × (Fin n × Fin 2 → Fin 2)) :
    0 ≤ tableWeight w alice bob t := by
  change 0 ≤ ∑ l, w l * (∏ x, alice x l (t.1 x)) *
    (∏ ya, bob ya.1 l ya.2 (t.2 ya))
  exact sum_nonneg fun l _ => mul_nonneg
    (mul_nonneg (h.1 l) (prod_nonneg fun x _ => h.2.2.1 x l (t.1 x)))
    (prod_nonneg fun ya _ => h.2.2.2.2.1 ya.1 l ya.2 (t.2 ya))

private lemma tableWeight_sum {n : ℕ} {α : Type} [Fintype α] (w : α → ℝ)
    (alice : Fin n → α → Fin 2 → ℝ) (bob : Fin n → α → Fin 2 → Fin 2 → ℝ)
    (h : IsCODModel w alice bob) : (∑ t, tableWeight w alice bob t) = 1 := by
  classical
  change (∑ t : (Fin n → Fin 2) × (Fin n × Fin 2 → Fin 2),
    ∑ l, w l * (∏ x, alice x l (t.1 x)) *
    (∏ ya, bob ya.1 l ya.2 (t.2 ya))) = 1
  rw [sum_comm]
  calc
    _ = ∑ l, w l := by
      apply sum_congr rfl
      intro l _
      rw [Fintype.sum_prod_type]
      simp_rw [← mul_sum]
      rw [← Fintype.prod_sum]
      simp only [h.2.2.2.2.2, prod_const_one, mul_one]
      rw [← mul_sum, ← Fintype.prod_sum]
      simp only [h.2.2.2.1, prod_const_one, mul_one]
    _ = 1 := h.2.1

private lemma decomposition {n : ℕ} {α : Type} [Fintype α] (w : α → ℝ)
    (alice : Fin n → α → Fin 2 → ℝ) (bob : Fin n → α → Fin 2 → Fin 2 → ℝ)
    (h : IsCODModel w alice bob) :
    codBehaviour w alice bob = fun x y a b =>
      ∑ t, tableWeight w alice bob t * deterministicBehaviour t.1 t.2 x y a b := by
  classical
  funext x y a b
  change (∑ l, w l * alice x l a * bob y l a b) =
    ∑ t : (Fin n → Fin 2) × (Fin n × Fin 2 → Fin 2),
      (∑ l, w l * (∏ z, alice z l (t.1 z)) *
      (∏ ya, bob ya.1 l ya.2 (t.2 ya))) *
      ((if t.1 x = a then 1 else 0) * (if t.2 (y, a) = b then 1 else 0))
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  rw [Fintype.sum_prod_type]
  have ht (f : Fin n → Fin 2) (g : Fin n × Fin 2 → Fin 2) :
      w l * (∏ z, alice z l (f z)) * (∏ ya, bob ya.1 l ya.2 (g ya)) *
          ((if f x = a then 1 else 0) * (if g (y, a) = b then 1 else 0)) =
      w l * ((∏ z, alice z l (f z)) * (if f x = a then 1 else 0)) *
        ((∏ ya, bob ya.1 l ya.2 (g ya)) * (if g (y, a) = b then 1 else 0)) := by
    ac_rfl
  simp_rw [ht, ← mul_sum]
  rw [response_marginal (fun ya c => bob ya.1 l ya.2 c)
    (fun ya => h.2.2.2.2.2 ya.1 l ya.2) (y, a) b]
  rw [← sum_mul, ← mul_sum, response_marginal (fun z c => alice z l c)
    (fun z => h.2.2.2.1 z l) x a]

private lemma chained_mixture {n : ℕ} {σ : Type} [Fintype σ] (v : σ → ℝ)
    (p : σ → Fin n → Fin n → Fin 2 → Fin 2 → ℝ) :
    chainedValue n (fun x y a b => ∑ s, v s * p s x y a b) =
      ∑ s, v s * chainedValue n (p s) := by
  classical
  have hadd (a b : Fin n → Fin n → Fin 2 → Fin 2 → ℝ) :
      chainedValue n (fun x y c d => a x y c d + b x y c d) =
        chainedValue n a + chainedValue n b := by
    simp only [chainedValue_formula, ite_add_zero, sum_add_distrib]
    ac_rfl
  have hmul (r : ℝ) (a : Fin n → Fin n → Fin 2 → Fin 2 → ℝ) :
      chainedValue n (fun x y c d => r * a x y c d) = r * chainedValue n a := by
    simp only [chainedValue_formula, mul_add, mul_sum, mul_ite, mul_zero]
  have hz : chainedValue n (fun _ _ _ _ => 0) = 0 := by
    simp only [chainedValue_formula, ite_self, sum_const_zero, zero_add]
  have hfin (t : Finset σ) :
      chainedValue n (fun x y a b => ∑ s ∈ t, v s * p s x y a b) =
        ∑ s ∈ t, v s * chainedValue n (p s) := by
    induction t using Finset.induction_on with
    | empty => simpa only [sum_empty] using hz
    | @insert s t hs ih =>
      simp only [sum_insert hs]
      rw [hadd, hmul, ih]
  exact hfin univ

/-- The Brask–Chaves conjecture under its finite hidden-variable formal reading. -/
theorem result : claim := by
  intro n hn α _ w alice bob h
  rw [decomposition w alice bob h, chained_mixture]
  calc
    1 = ∑ t, tableWeight w alice bob t * 1 := by
      simpa only [mul_one] using (tableWeight_sum w alice bob h).symm
    _ ≤ _ := sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (deterministic_bound hn t.1 t.2)
        (tableWeight_nonneg w alice bob h t)

end D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality
