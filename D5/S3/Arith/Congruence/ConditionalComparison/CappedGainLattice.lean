/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainLattice
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Combining disjoint ending-load and future-label coordinates. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainLattice.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainScalar

/-!
# Combining disjoint ending-load and future-label coordinates

This file proves the full-label, rather than projected-state, lattice bridge.
-/

namespace Erdos7

variable {ι : Type*} [DecidableEq ι]

theorem Supermodular.of_marginal_mono {F : Finset ι → ℚ}
    (hM : ∀ {A B : Finset ι}, A ⊆ B → ∀ {x : ι}, x ∉ B →
      F (insert x A) - F A ≤ F (insert x B) - F B) : Supermodular F := by
  have hMany : ∀ (T A B : Finset ι), A ⊆ B → Disjoint T B →
      F (T ∪ A) - F A ≤ F (T ∪ B) - F B := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro A B _ _; simp
    | @insert x T hx ih =>
      intro A B hAB hdis
      have hd : Disjoint T B := (Finset.disjoint_insert_left.mp hdis).2
      have hxB : x ∉ B := (Finset.disjoint_insert_left.mp hdis).1
      have hi := ih A B hAB hd
      have hm := hM (Finset.union_subset_union (Finset.Subset.refl T) hAB)
        (show x ∉ T ∪ B by simp [hx, hxB])
      simp only [Finset.insert_union]
      linarith
  intro A B
  have h := hMany (A \ B) (A ∩ B) B Finset.inter_subset_right
    Finset.sdiff_disjoint
  have h1 : A \ B ∪ A ∩ B = A := by ext x; simp <;> tauto
  have h2 : A \ B ∪ B = A ∪ B := by ext x; simp <;> tauto
  rw [h1, h2] at h
  linarith

namespace CappedGain

def modularLoad (w : ι → ℚ) (A : Finset ι) : ℚ := ∑ x ∈ A, w x

theorem modularLoad_nonneg {w : ι → ℚ} (hw : ∀ x, 0 ≤ w x) (A : Finset ι) :
    0 ≤ modularLoad w A := Finset.sum_nonneg fun x _ ↦ hw x

theorem modularLoad_increasing {w : ι → ℚ} (hw : ∀ x, 0 ≤ w x) :
    Increasing (modularLoad w) := by
  intro A B hAB
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ ↦ hw x)

/-- Increasing load increments and increasing load/future differences imply
supermodularity on the original individual labels. Future labels have zero
current load, so the two coordinate families are disjoint. -/
theorem supermodular_load_filter
    (P : ι → Prop) [DecidablePred P] (w : ι → ℚ)
    (hw : ∀ x, 0 ≤ w x) (hzero : ∀ x, P x → w x = 0)
    (H : ℚ → Finset ι → ℚ)
    (hS : ∀ l, 0 ≤ l → Supermodular (H l))
    (hL : ∀ (S : Finset ι) {x y d : ℚ}, 0 ≤ x → x ≤ y → 0 ≤ d →
      H (x + d) S - H x S ≤ H (y + d) S - H y S)
    (hX : ∀ {l m : ℚ}, 0 ≤ l → l ≤ m → ∀ {S T : Finset ι}, S ⊆ T →
      H m S - H l S ≤ H m T - H l T) :
    Supermodular (fun A ↦ H (modularLoad w A) (A.filter P)) := by
  apply Supermodular.of_marginal_mono
  intro A B hAB x hxB
  have hxA : x ∉ A := fun h ↦ hxB (hAB h)
  have hload0 := modularLoad_nonneg hw A
  have hloadB0 := modularLoad_nonneg hw B
  have hloadAB := modularLoad_increasing hw hAB
  have hfilter : A.filter P ⊆ B.filter P := Finset.filter_subset_filter P hAB
  have hinsA : modularLoad w (insert x A) = w x + modularLoad w A := by
    exact Finset.sum_insert hxA
  have hinsB : modularLoad w (insert x B) = w x + modularLoad w B := by
    exact Finset.sum_insert hxB
  by_cases hxP : P x
  · have hfuture := (hS _ hload0).marginal_mono hfilter
      (show x ∉ B.filter P from fun h ↦ hxB (Finset.mem_filter.mp h).1)
    have hcross := hX hload0 hloadAB
      (Finset.subset_insert x (B.filter P))
    simp only [hinsA, hinsB, hzero x hxP, zero_add, Finset.filter_insert,
      hxP, if_true]
    linarith
  · have hload := hL (A.filter P) hload0 hloadAB (hw x)
    have hcross := hX hloadB0
      (show modularLoad w B ≤ modularLoad w B + w x by linarith [hw x]) hfilter
    simp only [hinsA, hinsB, Finset.filter_insert, hxP, if_false]
    simpa only [add_comm (w x)] using hload.trans hcross

theorem increasing_load_filter
    (P : ι → Prop) [DecidablePred P] (w : ι → ℚ)
    (hw : ∀ x, 0 ≤ w x) (H : ℚ → Finset ι → ℚ)
    (hS : ∀ l, 0 ≤ l → Increasing (H l))
    (hL : ∀ S {l m : ℚ}, 0 ≤ l → l ≤ m → H l S ≤ H m S) :
    Increasing (fun A ↦ H (modularLoad w A) (A.filter P)) := by
  intro A B hAB
  exact (hL _ (modularLoad_nonneg hw A) (modularLoad_increasing hw hAB)).trans
    (hS _ (modularLoad_nonneg hw B) (Finset.filter_subset_filter P hAB))

end CappedGain
end Erdos7
