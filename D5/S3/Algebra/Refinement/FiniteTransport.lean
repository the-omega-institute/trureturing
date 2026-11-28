/- GID: D5/S3/Algebra/Refinement/FiniteTransport
   generality: G
   mirror-B: none(waiver:covered-by-finite-fiber-transport-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite transportation in conical commutative refinement monoids. -/

module

public import OmegaBuild.Commands
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
Omega original.

Finite transportation in conical commutative refinement monoids.
The finite-family construction is the transportation argument of Atserias and
Kolaitis, "Consistency Witnesses for Annotated Relations", Theorem 1 and Section 6.
-/

compile_only_with_mathlib

@[expose] public section

namespace Omega.Refinement

open scoped BigOperators

universe u v w z

variable {K : Type u} [AddCommMonoid K]

/-- Zero has no nonzero additive summands. -/
def Conical (K : Type u) [AddCommMonoid K] : Prop :=
  ∀ x y : K, x + y = 0 → x = 0 ∧ y = 0

/-- Every equality of two binary sums has a refinement matrix. -/
def BinaryRefinement (K : Type u) [AddCommMonoid K] : Prop :=
  ∀ a₀ a₁ b₀ b₁ : K, a₀ + a₁ = b₀ + b₁ →
    ∃ c₀₀ c₀₁ c₁₀ c₁₁ : K,
      c₀₀ + c₀₁ = a₀ ∧ c₁₀ + c₁₁ = a₁ ∧
      c₀₀ + c₁₀ = b₀ ∧ c₀₁ + c₁₁ = b₁

/-- Conicality detects each term of a vanishing finite sum. -/
theorem term_eq_zero_of_sum_eq_zero (hc : Conical K) {I : Type v}
    (s : Finset I) (p : I → K) (h : ∑ i ∈ s, p i = 0) :
    ∀ i ∈ s, p i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha] at h
      obtain ⟨h₁, h₂⟩ := hc _ _ h
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h₁
      · exact ih h₂ i hi

/-- Split a finite family into two families with prescribed totals. -/
theorem split_sum (hc : Conical K) (hr : BinaryRefinement K) {I : Type v}
    (s : Finset I) (p : I → K) (x y : K) (h : x + y = ∑ i ∈ s, p i) :
    ∃ r t : I → K, (∀ i ∈ s, r i + t i = p i) ∧
      (∑ i ∈ s, r i) = x ∧ (∑ i ∈ s, t i) = y := by
  classical
  induction s using Finset.induction_on generalizing x y with
  | empty =>
      obtain ⟨hx, hy⟩ := hc x y (by simpa using h)
      exact ⟨fun _ => 0, fun _ => 0, by simp, by simpa using hx.symm,
        by simpa using hy.symm⟩
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha] at h
      obtain ⟨c₀₀, c₀₁, c₁₀, c₁₁, h₀, h₁, h₂, h₃⟩ := hr x y (p a) _ h
      obtain ⟨r, t, hrt, hs, ht⟩ := ih c₀₁ c₁₁ h₃
      refine ⟨Function.update r a c₀₀, Function.update t a c₁₀, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa using h₂
        · have hia : i ≠ a := fun e => ha (e ▸ hi)
          simpa [hia] using hrt i hi
      · rw [Finset.sum_insert ha]
        rw [Function.update_self]
        have he : (∑ i ∈ s, Function.update r a c₀₀ i) = ∑ i ∈ s, r i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Function.update_of_ne (show i ≠ a from fun e => ha (e ▸ hi)) _ _
        rw [he, hs]
        exact h₀
      · rw [Finset.sum_insert ha]
        rw [Function.update_self]
        have he : (∑ i ∈ s, Function.update t a c₁₀ i) = ∑ i ∈ s, t i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Function.update_of_ne (show i ≠ a from fun e => ha (e ▸ hi)) _ _
        rw [he, ht]
        exact h₁

/-- Construct a matrix over finite sets, allowing either set to be empty. -/
theorem transport_finsets (hc : Conical K) (hr : BinaryRefinement K)
    {A : Type v} {B : Type w} (s : Finset A) (t : Finset B)
    (p : A → K) (q : B → K) (h : ∑ a ∈ s, p a = ∑ b ∈ t, q b) :
    ∃ m : A → B → K,
      (∀ a ∈ s, ∑ b ∈ t, m a b = p a) ∧
      (∀ b ∈ t, ∑ a ∈ s, m a b = q b) := by
  classical
  induction s using Finset.induction_on generalizing q with
  | empty =>
      refine ⟨fun _ _ => 0, by simp, ?_⟩
      intro b hb
      simpa using (term_eq_zero_of_sum_eq_zero hc t q (by simpa using h.symm) b hb).symm
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha] at h
      obtain ⟨r, q', hsplit, hr', hq'⟩ := split_sum hc hr t q (p a) (∑ i ∈ s, p i) h
      obtain ⟨m, hmrow, hmcol⟩ := ih q' hq'.symm
      refine ⟨Function.update m a r, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa using hr'
        · have hia : i ≠ a := fun e => ha (e ▸ hi)
          simpa [hia] using hmrow i hi
      · intro b hb
        rw [Finset.sum_insert ha]
        rw [Function.update_self]
        have he : (∑ i ∈ s, Function.update m a r i b) = ∑ i ∈ s, m i b := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Function.update_of_ne (show i ≠ a from fun e => ha (e ▸ hi))]
        rw [he, hmcol b hb]
        exact hsplit b hb

/-- Exact row and column sums over arbitrary finite carriers. -/
theorem transport_fintypes (hc : Conical K) (hr : BinaryRefinement K)
    {A : Type v} {B : Type w} [Fintype A] [Fintype B]
    (p : A → K) (q : B → K) (h : ∑ a, p a = ∑ b, q b) :
    ∃ m : A → B → K, (∀ a, ∑ b, m a b = p a) ∧ (∀ b, ∑ a, m a b = q b) := by
  obtain ⟨m, hm⟩ := transport_finsets hc hr Finset.univ Finset.univ p q h
  exact ⟨m, fun a => hm.1 a (Finset.mem_univ a), fun b => hm.2 b (Finset.mem_univ b)⟩

/-- Finite fibers have a joint weighting with the specified exact marginals. -/
def FiniteFiberTransport (K : Type u) [AddCommMonoid K] : Prop := by
  classical
  exact
  ∀ (A : Type v) (B : Type w) (Z : Type z) [Fintype A] [Fintype B]
    (f : A → Z) (g : B → Z) (p : A → K) (q : B → K),
    (∀ z, (∑ a, if f a = z then p a else 0) = ∑ b, if g b = z then q b else 0) →
    ∃ m : A → B → K,
      (∀ a b, f a ≠ g b → m a b = 0) ∧
      (∀ a, ∑ b, m a b = p a) ∧ (∀ b, ∑ a, m a b = q b)

/-- Fiberwise transportation does not require enumerating the label type. -/
theorem finite_fiber_transport (hc : Conical K) (hr : BinaryRefinement K) :
    FiniteFiberTransport.{u,v,w,z} K := by
  classical
  intro A B Z _ _ f g p q h
  have hex (z : Z) := transport_fintypes hc hr
    (fun a => if f a = z then p a else 0)
    (fun b => if g b = z then q b else 0) (h z)
  choose m hmrow hmcol using hex
  have rowzero (z : Z) (a : A) (ha : f a ≠ z) (b : B) : m z a b = 0 :=
    term_eq_zero_of_sum_eq_zero hc Finset.univ (m z a)
      (by simpa [ha] using hmrow z a) b (Finset.mem_univ b)
  have colzero (z : Z) (b : B) (hb : g b ≠ z) (a : A) : m z a b = 0 :=
    term_eq_zero_of_sum_eq_zero hc Finset.univ (fun a => m z a b)
      (by simpa [hb] using hmcol z b) a (Finset.mem_univ a)
  refine ⟨fun a b => m (f a) a b, ?_, ?_, ?_⟩
  · intro a b hab
    exact colzero (f a) b (Ne.symm hab) a
  · intro a
    simpa using hmrow (f a) a
  · intro b
    calc
      (∑ a, m (f a) a b) = ∑ a, m (g b) a b := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases hab : f a = g b
        · rw [hab]
        · rw [colzero (f a) b (Ne.symm hab) a, rowzero (g b) a hab b]
      _ = q b := by simpa using hmcol (g b) b

end Omega.Refinement
