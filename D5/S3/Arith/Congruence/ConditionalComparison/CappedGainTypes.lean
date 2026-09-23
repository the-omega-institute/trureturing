/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainTypes
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ConditionalComparison/CappedGainTypes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Injective full-type admissibility and saturation. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainTypes.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainGeometric
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Injective full-type admissibility and saturation

The predecessor index is proof metadata, not a stochastic state. Distinct
labels stay distinct when the index is enlarged by the current depth.
-/

namespace Erdos7.CappedGain

variable {ι I : Type*} [DecidableEq ι] [DecidableEq I]

structure Admissible {n : ℕ} (depth : ι → Fin (n + 1) → ℕ)
    (index : ι → I) (zero : I) (A : Finset ι) : Prop where
  injective : Set.InjOn (fun x ↦ (index x, depth x)) A
  nonzero : ∀ x ∈ A, ∃ j, depth x j ≠ 0
  mixed_zero : ∀ x ∈ A, index x = zero →
    ∃ j k, j ≠ k ∧ depth x j ≠ 0 ∧ depth x k ≠ 0

namespace Admissible

theorem tail_zero {n : ℕ} {depth : ι → Fin (n + 1) → ℕ} {x : ι}
    (hx : ¬ Future depth x) (j : Fin n) : depth x j.succ = 0 := by
  by_contra h
  exact hx ⟨j, h⟩

theorem positive_coordinate_eq_zero {n : ℕ} {depth : ι → Fin (n + 1) → ℕ} {x : ι}
    (hx : ¬ Future depth x) {j : Fin (n + 1)} (hj : depth x j ≠ 0) : j = 0 := by
  cases j using Fin.cases with
  | zero => rfl
  | succ j => exact (hj (tail_zero hx j)).elim

theorem ending_positive {n : ℕ} {depth : ι → Fin (n + 1) → ℕ}
    {index : ι → I} {zero : I} {A : Finset ι} (hA : Admissible depth index zero A)
    {x : ι} (hx : x ∈ A) (hf : ¬ Future depth x) : 0 < depth x 0 := by
  obtain ⟨j, hj⟩ := hA.nonzero x hx
  have he := positive_coordinate_eq_zero hf hj
  subst j
  omega

theorem ending_index_ne {n : ℕ} {depth : ι → Fin (n + 1) → ℕ}
    {index : ι → I} {zero : I} {A : Finset ι} (hA : Admissible depth index zero A)
    {x : ι} (hx : x ∈ A) (hf : ¬ Future depth x) : index x ≠ zero := by
  intro he
  obtain ⟨j, k, hjk, hj, hk⟩ := hA.mixed_zero x hx he
  exact hjk ((positive_coordinate_eq_zero hf hj).trans (positive_coordinate_eq_zero hf hk).symm)

theorem ending_pair_injective {n : ℕ} {depth : ι → Fin (n + 1) → ℕ}
    {index : ι → I} {zero : I} {A : Finset ι} (hA : Admissible depth index zero A) :
    Set.InjOn (fun x ↦ (index x, depth x 0)) (A.filter fun x ↦ ¬ Future depth x) := by
  intro x hx y hy hxy
  have hxA := (Finset.mem_filter.mp hx).1
  have hyA := (Finset.mem_filter.mp hy).1
  have hxf := (Finset.mem_filter.mp hx).2
  have hyf := (Finset.mem_filter.mp hy).2
  apply hA.injective hxA hyA
  change (index x, depth x) = (index y, depth y)
  apply Prod.ext
  · change index x = index y
    exact congrArg (fun z : I × ℕ ↦ z.1) hxy
  · funext j
    change depth x j = depth y j
    cases j using Fin.cases with
    | zero => exact congrArg Prod.snd hxy
    | succ j => rw [tail_zero hxf j, tail_zero hyf j]

end Admissible

theorem saturation_bound [Fintype I] {p : ℚ} (hp : 1 ≤ p)
    (A : Finset ι) (index : ι → I) (zero : I) (depth : ι → ℕ) (D : ℕ)
    (hinj : Set.InjOn (fun x ↦ (index x, depth x)) A)
    (hindex : ∀ x ∈ A, index x ≠ zero) (hpositive : ∀ x ∈ A, 0 < depth x)
    (hdepth : ∀ x ∈ A, depth x ≤ D) :
    (∑ x ∈ A, beta p (depth x)) ≤ (Fintype.card I : ℚ) - 1 := by
  classical
  let f : ι → I × ℕ := fun x ↦ (index x, depth x - 1)
  have hfi : Set.InjOn f A := by
    intro x hx y hy hxy
    apply hinj hx hy
    change (index x, depth x) = (index y, depth y)
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    apply Prod.ext
    · exact h1
    · change depth x = depth y
      dsimp [f] at h2
      have hx0 := hpositive x hx
      have hy0 := hpositive y hy
      omega
  have himage : A.image f ⊆ (Finset.univ.erase zero).product (Finset.range D) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_erase.mpr ⟨hindex x hx, Finset.mem_univ _⟩, ?_⟩
    apply Finset.mem_range.mpr
    dsimp [f]
    have hp0 := hpositive x hx
    have hd := hdepth x hx
    omega
  have he : (∑ v ∈ A.image f, beta p (v.2 + 1)) = ∑ x ∈ A, beta p (depth x) := by
    rw [Finset.sum_image (fun x hx y hy hxy ↦ hfi hx hy hxy)]
    apply Finset.sum_congr rfl
    intro x hx
    have hpos := hpositive x hx
    simp [f, Nat.sub_add_cancel (show 1 ≤ depth x by omega)]
  calc
    (∑ x ∈ A, beta p (depth x)) = ∑ v ∈ A.image f, beta p (v.2 + 1) := he.symm
    _ ≤ ∑ v ∈ (Finset.univ.erase zero).product (Finset.range D), beta p (v.2 + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (fun v _ _ ↦ beta_nonneg hp _)
    _ = ∑ _i ∈ Finset.univ.erase zero, ∑ d ∈ Finset.range D, beta p (d + 1) :=
      Finset.sum_product _ _ _
    _ ≤ ∑ _i ∈ Finset.univ.erase zero, (1 : ℚ) :=
      Finset.sum_le_sum fun _ _ ↦ beta_sum_le_one p hp D
    _ = (Fintype.card I : ℚ) - 1 := by
      have hcard : 1 ≤ Fintype.card I := by
        letI : Nonempty I := ⟨zero⟩
        exact Fintype.card_pos
      simp [Finset.card_erase_of_mem, Nat.cast_sub hcard]

theorem ending_load_saturation {n : ℕ} [Fintype I]
    {depth : ι → Fin (n + 1) → ℕ} {index : ι → I} {zero : I} {A : Finset ι}
    (hA : Admissible depth index zero A) (v : Param) (D : ℕ)
    (hdepth : ∀ x ∈ A, depth x 0 ≤ D) :
    modularLoad (endingWeight v depth) A ≤ (Fintype.card I : ℚ) - 1 := by
  classical
  let E := A.filter fun x ↦ ¬ Future depth x
  have he : modularLoad (endingWeight v depth) A = ∑ x ∈ E, beta v.P (depth x 0) := by
    dsimp [E, modularLoad]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : Future depth x <;> simp [endingWeight, hx]
  rw [he]
  exact saturation_bound (by linarith [v.p_three, v.prime_le]) E index zero _ D
    hA.ending_pair_injective
    (fun x hx ↦ hA.ending_index_ne (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
    (fun x hx ↦ hA.ending_positive (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
    (fun x hx ↦ hdepth x (Finset.mem_filter.mp hx).1)

theorem terminal_type_bound [Fintype I]
    {depth : ι → Fin 1 → ℕ} {index : ι → I} {zero : I} {A : Finset ι}
    (hA : Admissible depth index zero A) (D : ℕ) (hdepth : ∀ x ∈ A, depth x 0 ≤ D) :
    terminal (fun x ↦ depth x 0) A ≤ max ((Fintype.card I : ℚ) - 10) 0 / 8 := by
  have hf : ∀ x, ¬ Future depth x := by
    rintro x ⟨j, _⟩
    exact Fin.elim0 j
  have hi : Set.InjOn (fun x ↦ (index x, depth x 0)) A := by
    simpa only [hf, not_false_eq_true, Finset.filter_true] using hA.ending_pair_injective
  have h := saturation_bound (by norm_num : (1 : ℚ) ≤ 18) A index zero _ D hi
    (fun x hx ↦ hA.ending_index_ne hx (hf x))
    (fun x hx ↦ hA.ending_positive hx (hf x)) hdepth
  unfold terminal modularLoad
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact max_le_max (by linarith) (le_refl _)

/-- Total index map; clipping only affects labels outside the depth-restricted
family. On the family being bounded, it records the exact current depth. -/
def extendedIndex {n : ℕ} (index : ι → I) (depth : ι → Fin (n + 2) → ℕ)
    (d : ℕ) (x : ι) : I × Fin (d + 1) :=
  (index x, ⟨min (depth x 0) d, Nat.lt_succ_of_le (min_le_right _ _)⟩)

theorem admissible_tail {n : ℕ} {depth : ι → Fin (n + 2) → ℕ}
    {index : ι → I} {zero : I} {A : Finset ι} (hA : Admissible depth index zero A)
    (d : ℕ) :
    Admissible (fun x ↦ Fin.tail (depth x)) (extendedIndex index depth d) (zero, 0)
      (depthLe (fun x ↦ depth x 0) d (A.filter (Future depth))) := by
  let B := depthLe (fun x ↦ depth x 0) d (A.filter (Future depth))
  have hBA : ∀ x ∈ B, x ∈ A := fun x hx ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hBF : ∀ x ∈ B, Future depth x := fun x hx ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hBd : ∀ x ∈ B, depth x 0 ≤ d := fun x hx ↦ (Finset.mem_filter.mp hx).2
  have hidx : ∀ x ∈ B, ((extendedIndex index depth d x).2 : ℕ) = depth x 0 := by
    intro x hx
    exact min_eq_left (hBd x hx)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy he
    apply hA.injective (hBA x hx) (hBA y hy)
    change (index x, depth x) = (index y, depth y)
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    apply Prod.ext
    · change index x = index y
      exact congrArg (fun z : I × Fin (d + 1) ↦ z.1) h1
    · funext j
      change depth x j = depth y j
      cases j using Fin.cases with
      | zero =>
        have h := congrArg (fun z : I × Fin (d + 1) ↦ (z.2 : ℕ)) h1
        simpa only [hidx x hx, hidx y hy] using h
      | succ j => exact congrFun h2 j
  · intro x hx
    exact hBF x hx
  · intro x hx he
    have hz : index x = zero := congrArg Prod.fst he
    have hd0 : depth x 0 = 0 := by
      have h := congrArg (fun z : I × Fin (d + 1) ↦ (z.2 : ℕ)) he
      simpa only [hidx x hx, Fin.val_zero] using h
    obtain ⟨j, k, hjk, hj, hk⟩ := hA.mixed_zero x (hBA x hx) hz
    cases j using Fin.cases with
    | zero => exact (hj hd0).elim
    | succ j =>
      cases k using Fin.cases with
      | zero => exact (hk hd0).elim
      | succ k =>
        exact ⟨j, k, (fun h ↦ hjk (congrArg Fin.succ h)), hj, hk⟩

end Erdos7.CappedGain
