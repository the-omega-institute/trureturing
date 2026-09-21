/- GID: D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Pi]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.claim; result=D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.result; claim=D5/S0/Certificates/AraujoOrthodoxCompleteMappingRefutation.claim
   digest: Refutes Problem 15.5 using a five-element orthodox semigroup. -/

/- Formalization classification:
   proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #9377)
   Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation

/-- Page 59: regular, and the idempotents form a subsemigroup (an E-semigroup). -/
def Orthodox (S : Type) [Semigroup S] : Prop :=
  (∀ x : S, ∃ y : S, x * y * x = x) ∧
    ∀ e f : S, e * e = e → f * f = f → (e * f) * (e * f) = e * f

/-- Page 1: a bijection `α` whose product map `x ↦ x · xα` is also a bijection. -/
def CompleteMapping {S : Type} [Semigroup S] (α : S → S) : Prop :=
  Function.Bijective α ∧ Function.Bijective (fun x => x * α x)

/-- An ordering `c₁, …, c_n` of all elements of `S` whose product `c₁ ⋯ c_n` is an idempotent. -/
def IdempotentOrdering (S : Type) [Semigroup S] : Prop :=
  ∃ (c : S) (l : List S), (c :: l).Nodup ∧ (∀ x : S, x ∈ c :: l) ∧
    (l.foldl (· * ·) c) * (l.foldl (· * ·) c) = l.foldl (· * ·) c

/-- Problem 15.5 (page 60) read as the universal claim. -/
def claim : Prop :=
  ∀ (S : Type) [Semigroup S], Orthodox S → IdempotentOrdering S →
    ∃ α : S → S, CompleteMapping α

private inductive W where
  | w0 | w1 | w2 | w3 | w4
  deriving DecidableEq

private instance : Fintype W where
  elems := {W.w0, W.w1, W.w2, W.w3, W.w4}
  complete x := by cases x <;> simp

private def mulW : W → W → W
  | .w0, y => y
  | .w1, .w0 => .w1
  | .w1, .w1 => .w0
  | .w1, .w2 => .w2
  | .w1, .w3 => .w3
  | .w1, .w4 => .w4
  | .w2, .w0 => .w2
  | .w2, .w1 => .w2
  | .w2, y => y
  | .w3, .w0 => .w3
  | .w3, .w1 => .w3
  | .w3, .w2 => .w3
  | .w3, .w3 => .w4
  | .w3, .w4 => .w2
  | .w4, .w0 => .w4
  | .w4, .w1 => .w4
  | .w4, .w2 => .w4
  | .w4, .w3 => .w2
  | .w4, .w4 => .w3

private instance : Semigroup W where
  mul := mulW
  mul_assoc := by decide

example : W.w1 * W.w1 = W.w0 := by decide
example : W.w3 * W.w3 = W.w4 := by decide
example : W.w3 * W.w4 = W.w2 := by decide

example : Orthodox W := by
  simp only [Orthodox]
  decide

example : IdempotentOrdering W := by
  refine ⟨W.w0, [W.w1, W.w2, W.w3, W.w4], ?_⟩
  decide

example : [W.w1, W.w2, W.w3, W.w4].foldl (· * ·) W.w0 = W.w2 := by decide

example : ∀ z : W, ¬ ∀ x : W, z * x = z ∧ x * z = z := by decide

set_option maxRecDepth 100000 in
/-- Problem 15.5 has a negative answer. -/
theorem result : ¬ claim := by
  intro h
  have hOrthodox : Orthodox W := by
    simp only [Orthodox]
    decide
  have hOrdering : IdempotentOrdering W := by
    refine ⟨W.w0, [W.w1, W.w2, W.w3, W.w4], ?_⟩
    decide
  obtain ⟨α, hα⟩ := h W hOrthodox hOrdering
  have hNoCompleteMapping : ∀ α : W → W, ¬ CompleteMapping α := by
    simp only [CompleteMapping, Function.Bijective, Function.Injective, Function.Surjective]
    decide
  exact hNoCompleteMapping α hα

#print axioms result

end D5.S0.Certificates.AraujoOrthodoxCompleteMappingRefutation
