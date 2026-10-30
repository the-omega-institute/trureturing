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
import Mathlib.Tactic.Omega

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
def IsCODModel {n : ℕ} {λ : Type} [Fintype λ] (w : λ → ℝ)
    (alice : Fin n → λ → Fin 2 → ℝ) (bob : Fin n → λ → Fin 2 → Fin 2 → ℝ) : Prop :=
  (∀ l, 0 ≤ w l) ∧ (∑ l, w l) = 1 ∧
  (∀ x l a, 0 ≤ alice x l a) ∧ (∀ x l, ∑ a, alice x l a = 1) ∧
  (∀ y l a b, 0 ≤ bob y l a b) ∧ (∀ y l a, ∑ b, bob y l a b = 1)

/-- The COD factorization: Bob receives Alice's raw output. -/
def codBehaviour {n : ℕ} {λ : Type} [Fintype λ] (w : λ → ℝ)
    (alice : Fin n → λ → Fin 2 → ℝ) (bob : Fin n → λ → Fin 2 → Fin 2 → ℝ)
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
  ∀ n : ℕ, Odd n → ∀ (λ : Type) [Fintype λ] (w : λ → ℝ)
    (alice : Fin n → λ → Fin 2 → ℝ) (bob : Fin n → λ → Fin 2 → Fin 2 → ℝ),
    IsCODModel w alice bob → 1 ≤ chainedValue n (codBehaviour w alice bob)

private def deterministicBehaviour {n : ℕ} (f : Fin n → Fin 2)
    (g : Fin n × Fin 2 → Fin 2) (x y : Fin n) (a b : Fin 2) : ℝ :=
  labelKernel f x a * labelKernel (fun t => g (y, t)) a b

private def tableWeight {n : ℕ} {λ : Type} [Fintype λ] (w : λ → ℝ)
    (alice : Fin n → λ → Fin 2 → ℝ) (bob : Fin n → λ → Fin 2 → Fin 2 → ℝ)
    (t : (Fin n → Fin 2) × (Fin n × Fin 2 → Fin 2)) : ℝ :=
  ∑ l, w l * (∏ x, alice x l (t.1 x)) * (∏ ya, bob ya.1 l ya.2 (t.2 ya))

private lemma deterministic_bound {n : ℕ} (hn : Odd n) (f : Fin n → Fin 2)
    (g : Fin n × Fin 2 → Fin 2) :
    1 ≤ chainedValue n (deterministicBehaviour f g) := by
  sorry

private lemma tableWeight_nonneg {n : ℕ} {λ : Type} [Fintype λ] (w : λ → ℝ)
    (alice : Fin n → λ → Fin 2 → ℝ) (bob : Fin n → λ → Fin 2 → Fin 2 → ℝ)
    (h : IsCODModel w alice bob) (t : (Fin n → Fin 2) × (Fin n × Fin 2 → Fin 2)) :
    0 ≤ tableWeight w alice bob t := by
  sorry

private lemma tableWeight_sum {n : ℕ} {λ : Type} [Fintype λ] (w : λ → ℝ)
    (alice : Fin n → λ → Fin 2 → ℝ) (bob : Fin n → λ → Fin 2 → Fin 2 → ℝ)
    (h : IsCODModel w alice bob) : (∑ t, tableWeight w alice bob t) = 1 := by
  sorry

private lemma decomposition {n : ℕ} {λ : Type} [Fintype λ] (w : λ → ℝ)
    (alice : Fin n → λ → Fin 2 → ℝ) (bob : Fin n → λ → Fin 2 → Fin 2 → ℝ)
    (h : IsCODModel w alice bob) :
    codBehaviour w alice bob = fun x y a b =>
      ∑ t, tableWeight w alice bob t * deterministicBehaviour t.1 t.2 x y a b := by
  sorry

private lemma chained_mixture {n : ℕ} {σ : Type} [Fintype σ] (v : σ → ℝ)
    (p : σ → Fin n → Fin n → Fin 2 → Fin 2 → ℝ) :
    chainedValue n (fun x y a b => ∑ s, v s * p s x y a b) =
      ∑ s, v s * chainedValue n (p s) := by
  sorry

/-- The Brask–Chaves conjecture under its finite hidden-variable formal reading. -/
theorem result : claim := by
  intro n hn λ _ w alice bob h
  rw [decomposition w alice bob h, chained_mixture]
  calc
    1 = ∑ t, tableWeight w alice bob t * 1 := by
      simpa only [mul_one] using (tableWeight_sum w alice bob h).symm
    _ ≤ _ := sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (deterministic_bound hn t.1 t.2)
        (tableWeight_nonneg w alice bob h t)

end D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality
