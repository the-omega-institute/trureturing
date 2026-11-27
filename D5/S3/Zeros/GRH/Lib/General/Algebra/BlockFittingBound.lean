/- GID: D5/S3/Zeros/GRH/Lib/General/Algebra/BlockFittingBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Algebra/BlockFittingBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Algebra.BlockFittingBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Algebra/BlockFittingBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Algebra.GeneralisedIndex
import D5.S3.Zeros.GRH.Lib.General.Algebra.FittingDuality
import D5.S3.Zeros.GRH.Lib.CM.LocalHeight.IsogenyIntegrality
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Fitting ideal bounded by a length over a DVR, through a matrix algebra quotient. -/

open IsDiscreteValuationRing Matrix Module Submodule Fintype Ideal LinearMap

/-- Let ψ: A → M_d(O) be onto, N ⊆ A^ι an A-submodule, p ≠ 0, b < v(p). If the w in ((O/p)^d)^ι
killed by N through ψ lie in a submodule of length ≤ b, some square matrix B with rows in N
has v(det ψ(B)) ≤ b. -/
lemma exists_rows_addVal_det_le {O ι A d : Type} [CommRing O] [DVR O] [Fintype ι] [Ring A]
  [Algebra O A] [Fintype d] (ψ : A →ₐ[O] Matrix d d O) (hψ : (⇑ψ).Surjective)
  (N : Submodule A _) {p} (hp : p ≠ 0) {b} (hb : b < addVal O p) {Z : Submodule O (ι → d →
  QuotSpan p)} (hZ : length O Z ≤ b) (h : ∀ w, (∀ t ∈ N, ∑ j, ψ (t j) • w j = 0) → w ∈ Z) : ∃ B :
  Matrix .., (∀ i, B i ∈ N) ∧ addVal O ((comp ..) (B.map ψ)).det ≤ b := by
  choose E hE using hψ
  choose M S m s k using
    exists_matrix_addVal_det_le_length (range (p • .id) ⊔ (N.restrictScalars O).map (.pi
    fun (j, l) ↦ ∑ c, entryLinearMap O O c l ∘ₗ ψ.toLinearMap ∘ₗ proj j)) hp (mem_sup_left ⟨·, rfl⟩)
  choose u t _ ht' using by simpa [mem_sup] using m
  grw [length_le_of_le_map (LinearEquiv.curry ..).symm.1 Z fun w m ↦ ⟨_, h _ fun t h ↦ by
    ext i; simpa [*, sum_prod_type] using (s _).1 (mem_sup_right ⟨_, N.smul_mem
    (E (diagonal (ψ 1 i))) h, rfl⟩) w m, rfl⟩, hZ] at k
  use of (∑ c, E (updateRow 0 c 1) • t · c), fun k ↦ sum_mem (by bound)
  rwa [(addVal O).map_eq_of_lt_sub]
  simp [↓k.trans_lt, hb.trans_le, addVal_le_iff_dvd, ← Quotient.eq_zero_iff_dvd, det_apply, ← ht',
    *, mul_apply, Matrix.sum_apply, updateRow_apply]
