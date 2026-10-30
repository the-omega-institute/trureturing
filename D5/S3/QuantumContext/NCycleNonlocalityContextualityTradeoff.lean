/- GID: D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff
   generality: I
   mirror-B: D5/B/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Normalized Bell and contextuality inequalities obey the binary n-cycle trade-off. -/

import D5.S3.Combinatorics.Graph.LayeredCirculation.PositiveCircuitSupplier
import Mathlib.Logic.Equiv.Fin.Rotate

/-! The binary generalized Bell scenario of Porto–Ruffolo–Rabelo–Terra Cunha–Kurzyński,
arXiv:2405.02964v2. Context `i` consists of measurements `i` and `finRotate n i`.
Boolean outcomes encode the two signs; `true` in an edge-sign vector means anticorrelation. -/

set_option autoImplicit false

noncomputable section

open Finset

namespace D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff

/-- Joint conditional probabilities for two Alice settings and the cyclic Bob contexts. -/
def Behavior (n : ℕ) := Fin 2 → Fin n → Bool → Bool → Bool → ℝ

/-- Bob's probabilities for the ordered outcomes in each cyclic context. -/
def BobBehavior (n : ℕ) := Fin n → Bool → Bool → ℝ

/-- Alice's probabilities, indexed by setting and outcome. -/
def AliceResponse := Fin 2 → Bool → ℝ

/-- Nonnegative, normalized Alice responses. -/
def IsAliceResponse (α : AliceResponse) : Prop :=
  (∀ x a, 0 ≤ α x a) ∧ ∀ x, ∑ a, α x a = 1

/-- Nondisturbance identifies the shared measurement in consecutive contexts. -/
def IsND {n : ℕ} (r : BobBehavior n) : Prop :=
  (∀ i b c, 0 ≤ r i b c) ∧
  (∀ i, ∑ b, ∑ c, r i b c = 1) ∧
  ∀ i c, ∑ b, r i b c = ∑ d, r (finRotate n i) c d

/-- Nonsignaling and nondisturbance, including the joint Alice/shared-Bob marginal. -/
def IsNSND {n : ℕ} (p : Behavior n) : Prop :=
  (∀ x i a b c, 0 ≤ p x i a b c) ∧
  (∀ x i, ∑ a, ∑ b, ∑ c, p x i a b c = 1) ∧
  (∀ x i a c, ∑ b, p x i a b c = ∑ d, p x (finRotate n i) a c d) ∧
  (∀ x y i b c, ∑ a, p x i a b c = ∑ a, p y i a b c) ∧
  ∀ x i j a, ∑ b, ∑ c, p x i a b c = ∑ b, ∑ c, p x j a b c

/-- The nonsignaling Bob marginal, read at Alice's setting zero. -/
def bobMarginal {n : ℕ} (p : Behavior n) : BobBehavior n :=
  fun i b c => ∑ a, p 0 i a b c

/-- An independent product of an Alice response and a Bob behavior. -/
def productBehavior {n : ℕ} (α : AliceResponse) (r : BobBehavior n) : Behavior n :=
  fun x i a b c => α x a * r i b c

/-- The context probabilities induced by a global deterministic assignment. -/
def deterministic {n : ℕ} (s : Fin n → Bool) : BobBehavior n :=
  fun i b c => if s i = b ∧ s (finRotate n i) = c then 1 else 0

/-- Generalized locality permits arbitrary nondisturbing hidden Bob behaviors. -/
def IsGeneralizedLocal {n : ℕ} (p : Behavior n) : Prop :=
  p ∈ convexHull ℝ {q | ∃ α r, IsAliceResponse α ∧ IsND r ∧ q = productBehavior α r}

/-- Noncontextuality is the convex hull of global deterministic assignments. -/
def IsNoncontextual {n : ℕ} (r : BobBehavior n) : Prop :=
  r ∈ convexHull ℝ (Set.range (deterministic : (Fin n → Bool) → BobBehavior n))

/-- The affine Bell functional is nonpositive locally and has attained NSND maximum one. -/
def IsNormalizedGBell {n : ℕ} (f : (Behavior n →ₗ[ℝ] ℝ) × ℝ) : Prop :=
  (∀ p, IsGeneralizedLocal p → f.1 p + f.2 ≤ 0) ∧
  (∀ p, IsNSND p → f.1 p + f.2 ≤ 1) ∧
  ∃ p, IsNSND p ∧ f.1 p + f.2 = 1

/-- The affine contextuality functional has attained maximum one over NSND Bob marginals. -/
def IsNormalizedNC {n : ℕ} (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ) : Prop :=
  (∀ r, IsNoncontextual r → t.1 r + t.2 ≤ 0) ∧
  (∀ p, IsNSND p → t.1 (bobMarginal p) + t.2 ≤ 1) ∧
  ∃ p, IsNSND p ∧ t.1 (bobMarginal p) + t.2 = 1

/-- The normalized nonlocality–contextuality trade-off for every binary n-cycle. -/
def claim : Prop :=
  ∀ n, 3 ≤ n → ∀ (f : (Behavior n →ₗ[ℝ] ℝ) × ℝ)
    (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ),
    IsNormalizedGBell f → IsNormalizedNC t →
    ∀ p, IsNSND p → f.1 p + f.2 + (t.1 (bobMarginal p) + t.2) ≤ 1

private def oddSigns {n : ℕ} (γ : Fin n → Bool) : Prop :=
  (∏ i, if γ i then (-1 : ℝ) else 1) = -1

private def vertex {n : ℕ} (γ : Fin n → Bool) : BobBehavior n :=
  fun i b c => if Bool.xor b c = γ i then 1 / 2 else 0

private def generators (n : ℕ) : Set (BobBehavior n) :=
  Set.range deterministic ∪ {r | ∃ γ, oddSigns γ ∧ r = vertex γ}

private lemma bob_nd {n : ℕ} {p : Behavior n} (hp : IsNSND p) :
    IsND (bobMarginal p) := by
  sorry

private lemma product_nsnd {n : ℕ} {α : AliceResponse} {r : BobBehavior n}
    (hα : IsAliceResponse α) (hr : IsND r) : IsNSND (productBehavior α r) := by
  sorry

private lemma vertex_nd {n : ℕ} (γ : Fin n → Bool) : IsND (vertex γ) := by
  sorry

private lemma cycle_generators {n : ℕ} (hn : 3 ≤ n)
    (r : BobBehavior n) (hr : IsND r) : r ∈ convexHull ℝ (generators n) := by
  sorry

private lemma midpoint_noncontextual {n : ℕ} (hn : 3 ≤ n)
    (γ η : Fin n → Bool) (hγ : oddSigns γ) (hη : oddSigns η) (hne : γ ≠ η) :
    IsNoncontextual ((1 / 2 : ℝ) • vertex γ + (1 / 2 : ℝ) • vertex η) := by
  sorry

private lemma unique_positive_generator {n : ℕ}
    (hgen : ∀ r : BobBehavior n, IsND r → r ∈ convexHull ℝ (generators n))
    (hmid : ∀ γ η : Fin n → Bool, oddSigns γ → oddSigns η → γ ≠ η →
      IsNoncontextual ((1 / 2 : ℝ) • vertex γ + (1 / 2 : ℝ) • vertex η))
    (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ) (ht : IsNormalizedNC t) :
    ∃ γ : Fin n → Bool, oddSigns γ ∧ t.1 (vertex γ) + t.2 = 1 ∧
      ∀ η, oddSigns η → η ≠ γ → t.1 (vertex η) + t.2 ≤ 0 := by
  have hmarg := bob_nd ht.2.2.choose_spec.1
  sorry

private lemma common_local_part {n : ℕ}
    (hgen : ∀ r : BobBehavior n, IsND r → r ∈ convexHull ℝ (generators n))
    (p : Behavior n) (hp : IsNSND p)
    (t : (BobBehavior n →ₗ[ℝ] ℝ) × ℝ) (ht : IsNormalizedNC t)
    (hc : 0 < t.1 (bobMarginal p) + t.2)
    (γ : Fin n → Bool) (hγ : oddSigns γ) (hmax : t.1 (vertex γ) + t.2 = 1)
    (hother : ∀ η, oddSigns η → η ≠ γ → t.1 (vertex η) + t.2 ≤ 0) :
    ∃ α : AliceResponse, IsAliceResponse α ∧
      ∀ x i a b c, (t.1 (bobMarginal p) + t.2) *
        (α x a * vertex γ i b c) ≤ p x i a b c := by
  sorry

private lemma dominated_local_tradeoff {n : ℕ}
    (p l : Behavior n) (hp : IsNSND p) (hl : IsNSND l)
    (hloc : IsGeneralizedLocal l) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hdom : ∀ x i a b d, c * l x i a b d ≤ p x i a b d)
    (f : (Behavior n →ₗ[ℝ] ℝ) × ℝ) (hf : IsNormalizedGBell f) :
    f.1 p + f.2 ≤ 1 - c := by
  sorry

/-- The Porto–Ruffolo–Rabelo–Terra Cunha–Kurzyński n-cycle conjecture. -/
theorem result : claim := by
  intro n hn f t hf ht p hp
  by_cases hc : t.1 (bobMarginal p) + t.2 ≤ 0
  · linarith [hf.2.1 p hp]
  · have hcpos : 0 < t.1 (bobMarginal p) + t.2 := lt_of_not_ge hc
    obtain ⟨γ, hγ, hmax, hother⟩ := unique_positive_generator
      (cycle_generators hn) (midpoint_noncontextual hn) t ht
    obtain ⟨α, hα, hdom⟩ := common_local_part
      (cycle_generators hn) p hp t ht hcpos γ hγ hmax hother
    have hlocal : IsGeneralizedLocal (productBehavior α (vertex γ)) :=
      subset_convexHull ℝ _ ⟨α, vertex γ, hα, vertex_nd γ, rfl⟩
    have hbound := dominated_local_tradeoff p (productBehavior α (vertex γ)) hp
      (product_nsnd hα (vertex_nd γ)) hlocal (t.1 (bobMarginal p) + t.2)
      hcpos (ht.2.1 p hp) hdom f hf
    linarith

end D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff
