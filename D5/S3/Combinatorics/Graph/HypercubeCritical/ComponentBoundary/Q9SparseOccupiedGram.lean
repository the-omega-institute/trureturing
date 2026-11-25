/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Disjoint occupied column supports and strict column energy prevent empty-boundary kernels. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PositivePairedKernel

/-! For Hong–Wu–Xia, arXiv:2610.09483v1, Problem 2, a sparse occupied
mask provides a purely local obstruction to universal weighted sharpness.
The occupied and empty row Gram matrices sum to a scalar identity.
If no occupied row is shared by two columns, this yields a diagonal
empty Gram with strictly positive diagonal entries. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseOccupiedGram

open Finset

/-- In a split scalar Gram matrix, pairwise disjoint column supports on the
first row set and strictly smaller column energies force a trivial kernel
on the complementary row set. -/
theorem eq_zero_of_sparse_occupied_gram {ι ρ ε : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ρ] [Fintype ε] {O : Matrix ρ ι ℝ} {E : Matrix ε ι ℝ} {c : ℝ}
    (hGram : Oᵀ * O + Eᵀ * E = c • (1 : Matrix ι ι ℝ))
    (hrow : ∀ r x y, x ≠ y → O r x * O r y = 0)
    (hcol : ∀ x, (∑ r, O r x ^ 2) < c)
    {f : ι → ℝ} (hf : E *ᵥ f = 0) : f = 0 := by
  have hdiag : Oᵀ * O = Matrix.diagonal (fun x => ∑ r, O r x ^ 2) := by
    ext x y
    by_cases h : x = y
    · subst y
      simp [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
    · rw [Matrix.diagonal_apply_ne _ h]
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_eq_zero fun r _ => hrow r x y h
  have hvec := congrArg (fun M : Matrix ι ι ℝ => M *ᵥ f) hGram
  have he : (Eᵀ * E) *ᵥ f = 0 := by
    rw [← Matrix.mulVec_mulVec, hf, Matrix.mulVec_zero]
  rw [Matrix.add_mulVec, he, add_zero, Matrix.smul_mulVec, Matrix.one_mulVec, hdiag] at hvec
  funext x
  have hx := congrFun hvec x
  rw [Matrix.mulVec_diagonal] at hx
  change (∑ r, O r x ^ 2) * f x = c * f x at hx
  have hp : 0 < c - ∑ r, O r x ^ 2 := sub_pos.mpr (hcol x)
  have hzero : (c - ∑ r, O r x ^ 2) * f x = 0 := by
    rw [sub_mul, hx, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hp)

open BalancedCriticalSpectrum (Q flip IsSwitching)
open CoordinateHalves.Q9DominantAxisBoundary (PairedRows emptyFibreBoundary boundary
  exists_emptyFibreBoundary_kernel)
open Q9PositivePairedKernel (pairedVertex occupiedContact)
open private split_gram occupiedMatrix emptyMatrix occupied_entry occupied_entry_zero
  empty_boundary_iff switch_twice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PositivePairedKernel
open BalancedCubeComponentBoundary (flip_injective)

attribute [local instance] Classical.propDecidable

/-- A transverse mask contact with the retained vertex of a paired fibre. -/
def maskContact (C : Finset (Q 9)) (b : Bool) (i : Fin 9) (T : Finset (Fin 9))
    (r : Q 9) (x : PairedRows C b i) : Prop :=
  (r ∈ C ∨ flip r i ∈ C) ∧ ∃ a ∈ T, flip r a = pairedVertex x

private theorem occupied_mask_entry {C : Finset (Q 9)} {b : Bool} {i : Fin 9}
    {σ : Q 9 → ℝ} (hs : IsSwitching C σ) {T : Finset (Fin 9)} (hi : i ∉ T)
    (r : Q 9) (x : PairedRows C b i) :
    occupiedMatrix C b i σ (fun a => if a ∈ T then 1 else 0) r x =
      if maskContact C b i T r x then 1 else 0 := by
  classical
  let w (a : Fin 9) : ℝ := if a ∈ T then 1 else 0
  by_cases h : occupiedContact C b i r x
  · obtain ⟨hr, a, ha, he⟩ := h
    rw [occupied_entry hs w hr ha he]
    have hm : maskContact C b i T r x ↔ a ∈ T := by
      constructor
      · rintro ⟨_, d, hd, hde⟩
        have hda : d = a := flip_injective r (hde.trans he.symm)
        simpa only [hda] using hd
      · exact fun haT => ⟨hr, a, haT, he⟩
    simp only [w, hm]
  · rw [occupied_entry_zero σ w h]
    have hm : ¬ maskContact C b i T r x := by
      rintro ⟨hr, a, ha, he⟩
      exact h ⟨hr, a, fun e => hi (e ▸ ha), he⟩
    simp [hm]

/-- If every projected occupied row is adjacent through the mask to at most
one paired column and each column has fewer occupied neighbors than mask
directions, then the masked empty-fibre boundary has trivial kernel. -/
theorem eq_zero_of_sparse_mask {C : Finset (Q 9)} {b : Bool} {i : Fin 9}
    {σ : Q 9 → ℝ} (hs : IsSwitching C σ) (T : Finset (Fin 9)) (hi : i ∉ T)
    (hrow : ∀ r x y, maskContact C b i T r x → maskContact C b i T r y → x = y)
    (hcol : ∀ x : PairedRows C b i,
      ((univ : Finset (Q 9)).filter (fun r => maskContact C b i T r x)).card < T.card)
    {f : PairedRows C b i → ℝ}
    (hf : emptyFibreBoundary C b i (fun a => if a ∈ T then 1 else 0) *ᵥ f = 0) :
    f = 0 := by
  classical
  let w (a : Fin 9) : ℝ := if a ∈ T then 1 else 0
  let g (x : PairedRows C b i) := σ (pairedVertex x) * f x
  let O := occupiedMatrix C b i σ w
  let E := emptyMatrix C b i σ w
  have hGram : Oᵀ * O + Eᵀ * E = (T.card : ℝ) • (1 : Matrix _ _ ℝ) := by
    have h := split_gram (b := b) (i := i) hs w
    have hsum : (∑ a : Fin 9, (if a = i then 0 else w a) ^ 2) = (T.card : ℝ) := by
      have hp (a : Fin 9) : (if a = i then 0 else w a) ^ 2 =
          if a ∈ T then (1 : ℝ) else 0 := by
        by_cases h : a = i
        · subst a
          simp [hi]
        · by_cases hT : a ∈ T <;> simp [h, w, hT]
      simp only [hp]
      rw [← Finset.sum_filter]
      simp [Finset.filter_mem_eq_inter]
    rw [hsum] at h
    exact h
  have hentry (r : Q 9) (x : PairedRows C b i) :
      O r x = if maskContact C b i T r x then 1 else 0 := occupied_mask_entry hs hi r x
  have hrow' (r : Q 9) (x y : PairedRows C b i) (hne : x ≠ y) : O r x * O r y = 0 := by
    rw [hentry, hentry]
    by_cases hx : maskContact C b i T r x
    · have hy : ¬ maskContact C b i T r y := fun hy => hne (hrow r x y hx hy)
      simp [hx, hy]
    · simp [hx]
  have hcol' (x : PairedRows C b i) : (∑ r, O r x ^ 2) < (T.card : ℝ) := by
    have hp (r : Q 9) : O r x ^ 2 = if maskContact C b i T r x then (1 : ℝ) else 0 := by
      rw [hentry]
      split_ifs <;> norm_num
    simp only [hp]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast hcol x
  have hg : E *ᵥ g = 0 := (empty_boundary_iff σ w g).mpr (by
    change emptyFibreBoundary C b i w *ᵥ
      (fun x => σ (pairedVertex x) * (σ (pairedVertex x) * f x)) = 0
    rw [switch_twice hs f]
    exact hf)
  have hz : g = 0 := eq_zero_of_sparse_occupied_gram hGram hrow' hcol' hg
  funext x
  have hx := congrFun hz x
  change σ (pairedVertex x) * f x = 0 at hx
  rcases hs.1 (pairedVertex x) x.1.1.property with h | h <;> simpa [h] using hx

/-- The same local mask excludes a universally saturated switched component. -/
theorem not_universal_boundary_of_sparse_mask {C : Finset (Q 9)} {b : Bool} {i : Fin 9}
    {σ : Q 9 → ℝ} (hs : IsSwitching C σ) (T : Finset (Fin 9)) (hi : i ∉ T)
    (hrow : ∀ r x y, maskContact C b i T r x → maskContact C b i T r y → x = y)
    (hcol : ∀ x : PairedRows C b i,
      ((univ : Finset (Q 9)).filter (fun r => maskContact C b i T r x)).card < T.card) :
    ¬ (∀ w : Fin 9 → ℝ, ∃ f ≠ 0, boundary C b w *ᵥ f = 0) := by
  intro h
  obtain ⟨f, hf, he⟩ := exists_emptyFibreBoundary_kernel C b h i
    (fun a => if a ∈ T then 1 else 0)
  exact hf (eq_zero_of_sparse_mask hs T hi hrow hcol he)

#print axioms eq_zero_of_sparse_occupied_gram
#print axioms eq_zero_of_sparse_mask
#print axioms not_universal_boundary_of_sparse_mask

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SparseOccupiedGram
