/- GID: D5/S3/Combinatorics/Transportation/FiniteFiberTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/FiniteFiberTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conical binary refinement is equivalent to exact finite-fiber transportation. -/

import OmegaMath.Algebra.Refinement.FiniteTransport

/-! Exact transportation characterizes conical commutative refinement monoids. -/

namespace D5.S3.Combinatorics.Transportation.FiniteFiberTransport

open Omega.Refinement
open scoped BigOperators Classical

universe u v w z

private theorem sum_ulift_bool {K : Type u} [AddCommMonoid K]
    (p : ULift.{v} Bool → K) : (∑ i, p i) = p ⟨true⟩ + p ⟨false⟩ :=
  (Fintype.sum_equiv Equiv.ulift p (fun b => p ⟨b⟩) (fun _ => rfl)).trans
    (Fintype.sum_bool _)

/-- The full finite-fiber transportation equivalence, including empty carriers. -/
theorem conical_refinement_iff_finite_fiber_transport (K : Type u) [AddCommMonoid K] :
    ((∀ x y : K, x + y = 0 → x = 0 ∧ y = 0) ∧
      (∀ a₀ a₁ b₀ b₁ : K, a₀ + a₁ = b₀ + b₁ →
        ∃ c₀₀ c₀₁ c₁₀ c₁₁ : K,
          c₀₀ + c₀₁ = a₀ ∧ c₁₀ + c₁₁ = a₁ ∧
          c₀₀ + c₁₀ = b₀ ∧ c₀₁ + c₁₁ = b₁)) ↔
      (∀ (A : Type v) (B : Type w) (Z : Type z) [Fintype A] [Fintype B]
        (f : A → Z) (g : B → Z) (p : A → K) (q : B → K),
        (∀ z, (∑ a, if f a = z then p a else 0) = ∑ b, if g b = z then q b else 0) →
        ∃ m : A → B → K,
          (∀ a b, f a ≠ g b → m a b = 0) ∧
          (∀ a, ∑ b, m a b = p a) ∧ (∀ b, ∑ a, m a b = q b)) := by
  classical
  change (Conical K ∧ BinaryRefinement K) ↔ FiniteFiberTransport.{u,v,w,z} K
  constructor
  · rintro ⟨hc, hr⟩
    exact finite_fiber_transport hc hr
  · intro h
    constructor
    · intro x y hxy
      let p : ULift.{v} Bool → K := fun i => if i.down then x else y
      obtain ⟨m, _, hm, _⟩ := h (ULift.{v} Bool) (ULift.{w} Empty) (ULift.{z} Unit)
        (fun _ => ⟨()⟩) (fun b => nomatch b.down) p (fun b => nomatch b.down) (by
          intro label
          rcases label with ⟨⟨⟩⟩
          simpa [sum_ulift_bool, p] using hxy)
      constructor
      · simpa [p] using (hm ⟨true⟩).symm
      · simpa [p] using (hm ⟨false⟩).symm
    · intro a₀ a₁ b₀ b₁ hab
      let p : ULift.{v} Bool → K := fun i => if i.down then a₀ else a₁
      let q : ULift.{w} Bool → K := fun i => if i.down then b₀ else b₁
      obtain ⟨m, _, hmrow, hmcol⟩ := h (ULift.{v} Bool) (ULift.{w} Bool)
        (ULift.{z} Unit) (fun _ => ⟨()⟩) (fun _ => ⟨()⟩) p q (by
          intro label
          rcases label with ⟨⟨⟩⟩
          simpa [sum_ulift_bool, p, q] using hab)
      exact ⟨m ⟨true⟩ ⟨true⟩, m ⟨true⟩ ⟨false⟩,
        m ⟨false⟩ ⟨true⟩, m ⟨false⟩ ⟨false⟩,
        by simpa [p, sum_ulift_bool] using hmrow ⟨true⟩,
        by simpa [p, sum_ulift_bool] using hmrow ⟨false⟩,
        by simpa [q, sum_ulift_bool] using hmcol ⟨true⟩,
        by simpa [q, sum_ulift_bool] using hmcol ⟨false⟩⟩

end D5.S3.Combinatorics.Transportation.FiniteFiberTransport
