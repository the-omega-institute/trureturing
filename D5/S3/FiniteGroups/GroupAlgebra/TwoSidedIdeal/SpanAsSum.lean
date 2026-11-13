/- GID: D5/S3/FiniteGroups/GroupAlgebra/TwoSidedIdeal/SpanAsSum
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/TwoSidedIdeal/SpanAsSum
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Needed finite multiplier sum for the attributed tensor simplicity proof. -/

/-
Classical algebra proofs used for the actual finite-group representation image.
Proof attribution: AxiomMath/Stacks contributors, Apache-2.0 (see upstream/LICENSE).
Pinned revision: 5ed82d14634e8d9576bb844c7bd4e3da66d450e7
Upstream: StacksCore/RingTheory/TwoSidedIdeal/SpanAsSum.lean
SHA-256: 123adece5b72fe7eddcbf9d854712612bb5868fedb65a541b31db7c9b8ba71a4
The pinned source files contain no individual author or copyright notices.
Retirement: when the Mathlib revision pinned in this repository's lake-manifest.json
provides an equivalent of this namespace's `exists_sum_mul_mul_eq_one` for any
unital simple ring R and a ≠ 0, producing n : ℕ and x, y : Fin n → R with
∑ i, x i * a * y i = 1, replace that fragment with direct Mathlib reuse and remove
unused transplanted helpers. No commutativity, field, or finiteness is required.
-/

import Mathlib.Algebra.Group.Subgroup.Finsupp
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
import Mathlib.RingTheory.TwoSidedIdeal.Operations

namespace D5.S3.RingTheory.TwoSidedIdeal.SpanAsSum

open scoped Pointwise
open Set _root_.TwoSidedIdeal

private lemma univ_mul_mul_univ_eq_range {α : Type*} [Mul α] (s : Set α) :
    univ * s * univ = range fun t : α × s × α ↦ t.1 * t.2.1 * t.2.2 := by
  ext; simp [mem_mul]

universe u v

variable {R : Type u} [Ring R]

/-- A finite sum `∑ i ∈ t, xL i * y i * xR i` with each `y i ∈ s` lies in `span s`. -/
private theorem sum_mul_mul_mem_span {ι : Type*} (s : Set R) (t : Finset ι) (xL xR : ι → R)
    (y : ι → s) : ∑ i ∈ t, xL i * (y i : R) * xR i ∈ span s :=
  sum_mem fun _ _ ↦ mul_mem_right _ _ _ <| mul_mem_left _ _ _ <| subset_span (y _).2

private lemma mem_span_iff_exists_fin' (s : Set R) (x : R) :
    x ∈ span s ↔ ∃ (ι : Type u) (t : Finset ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
      x = ∑ i ∈ t, xL i * (y i : R) * xR i := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ := AddSubgroup.mem_closure_range_iff.1
      (univ_mul_mul_univ_eq_range s ▸ mem_span_iff_mem_addSubgroup_closure.1 hx)
    simp_rw [← smul_mul_assoc, Finsupp.sum] at ha
    exact ⟨_, a.support, _, _, _, ha⟩
  · rintro ⟨_, _, _, _, _, rfl⟩
    exact sum_mul_mul_mem_span ..

private lemma mem_span_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span s ↔ ∃ (n : ℕ) (xL : Fin n → R) (xR : Fin n → R) (y : Fin n → s),
      x = ∑ i : Fin n, xL i * (y i : R) * xR i := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨ι, t, xL, xR, y, hy⟩ := (mem_span_iff_exists_fin' s x).1 hx
    let f := Subtype.val ∘ (Finset.equivFin t).symm
    refine ⟨t.card, xL ∘ f, xR ∘ f, y ∘ f, hy ▸ (Finset.sum_bij'
      (fun x hx ↦ Finset.equivFin t ⟨x, hx⟩) (fun i _ ↦ f i) ?_ ?_ ?_ ?_ ?_)⟩
    all_goals simp [f]
  · rintro ⟨_, _, _, _, rfl⟩
    exact sum_mul_mul_mem_span ..


/-- In a simple ring, every nonzero element `a` admits finite families `x y` of left and right
multipliers such that `∑ i, x i * a * y i = 1`. -/
lemma exists_sum_mul_mul_eq_one {R : Type*} [Ring R] [IsSimpleRing R] {a : R}
    (ha : a ≠ 0) : ∃ (n : ℕ) (x y : Fin n → R), ∑ i, x i * a * y i = 1 := by
  obtain ⟨n, x, y, z, eq⟩ := (mem_span_iff_exists_fin {a} 1).1 <|
    IsSimpleRing.one_mem_of_ne_zero_mem _ ha (TwoSidedIdeal.subset_span rfl)
  simp_rw [show ∀ i, (z i : R) = a from fun i ↦ (z i).2] at eq
  exact ⟨n, x, y, eq.symm⟩

end D5.S3.RingTheory.TwoSidedIdeal.SpanAsSum
