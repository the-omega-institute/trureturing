/- GID: D5/S3/Quantum/Measurement/FactorWidth/NonnegativeFactorWidthTwo
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FactorWidth/NonnegativeFactorWidthTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative real reconstruction from a complex two-sparse Gram decomposition. -/

/-
admission_basis: escape-witness
escape_witness: compress_complex_pair_moments compresses an exact pair group to one nonnegative
factor consuming its first diagonal budget and leaving a nonnegative second diagonal remainder.
proof_shape: compress_complex_pair_moments: content; consumer: nonnegative_two_sparse_gram
proof_shape: pair_subset_support: bind-only; consumer: nonnegative_two_sparse_gram
proof_shape: nonnegative_two_sparse_gram: content
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31511
-/

import D5.S3.Quantum.Measurement.FactorWidthTwoCone
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Nonnegative two-sparse Gram decomposition -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Matrix Finset

namespace D5.S3.Quantum.Measurement.FactorWidth.NonnegativeFactorWidthTwo
noncomputable section

private theorem compress_complex_pair_moments {n : ℕ} {ι : Type*}
    (s : Finset ι) (v : ι → Fin n → ℂ) (i j : Fin n)
    (c : ℝ) (hc : 0 ≤ c)
    (hcross : c = ∑ t ∈ s, (v t i * star (v t j)).re) :
    ∃ x y d : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ d ∧
      x * y = c ∧
      x ^ 2 = (∑ t ∈ s, Complex.normSq (v t i)) ∧
      y ^ 2 + d = (∑ t ∈ s, Complex.normSq (v t j)) ∧
      (c = 0 → y = 0) := by
  let A := ∑ t ∈ s, Complex.normSq (v t i)
  let B := ∑ t ∈ s, Complex.normSq (v t j)
  have hA : 0 ≤ A := Finset.sum_nonneg fun t _ => Complex.normSq_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun t _ => Complex.normSq_nonneg _
  have hle : c ≤ ∑ t ∈ s, ‖v t i‖ * ‖v t j‖ := by
    rw [hcross]
    apply Finset.sum_le_sum
    intro t _
    simpa [norm_mul, Complex.star_def, Complex.norm_conj] using
      Complex.re_le_norm (v t i * star (v t j))
  have hbound : c ^ 2 ≤ A * B := by
    calc
      c ^ 2 ≤ (∑ t ∈ s, ‖v t i‖ * ‖v t j‖) ^ 2 := by
        nlinarith
      _ ≤ A * B := by
        simpa only [A, B, Complex.normSq_eq_norm_sq] using
          Finset.sum_mul_sq_le_sq_mul_sq s (fun t => ‖v t i‖) (fun t => ‖v t j‖)
  by_cases hzero : A = 0
  · have hc0 : c = 0 := by rw [hzero, zero_mul] at hbound; nlinarith
    exact ⟨0, 0, B, le_rfl, le_rfl, hB, by simp [hc0], by change (0 : ℝ) ^ 2 = A; rw [hzero]; norm_num,
      by simp [B], fun _ => rfl⟩
  · have hx : 0 < Real.sqrt A := Real.sqrt_pos.2 (lt_of_le_of_ne hA (Ne.symm hzero))
    have hs : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
    let y := c / Real.sqrt A
    have hxy : Real.sqrt A * y = c := by
      dsimp [y]
      field_simp
    have hyB : y ^ 2 ≤ B := by
      apply (le_of_mul_le_mul_right _ (show 0 < A from lt_of_le_of_ne hA (Ne.symm hzero)))
      rw [← hs, ← mul_pow, mul_comm y, hxy]
      simpa only [hs, mul_comm B] using hbound
    exact ⟨Real.sqrt A, y, B - y ^ 2, hx.le, div_nonneg hc hx.le,
      sub_nonneg.mpr hyB, hxy, hs, by ring, fun h => by simp [y, h]⟩


private theorem pair_subset_support {n : ℕ} {s : Finset (Fin n)} {i j : Fin n}
    (hs : s.card ≤ 2) (hij : i ≠ j) (hi : i ∈ s) (hj : j ∈ s) :
    s = {i, j} := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)
  · simpa [hij] using hs

/-- An entrywise nonnegative matrix with a complex two-sparse Gram decomposition admits an
entrywise nonnegative real two-sparse decomposition with at most one slot per vertex and pair. -/
theorem nonnegative_two_sparse_gram {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hnonneg : ∀ i j, 0 ≤ X i j)
    (hgram : FactorWidthTwoCone.IsKIncoherentSum 2 (X.map Complex.ofReal)) :
    ∃ (k : ℕ) (v : Fin k → Fin n → ℝ),
      k ≤ n + Nat.choose n 2 ∧
      (∀ t i, 0 ≤ v t i) ∧
      (∀ t, (Finset.univ.filter fun i => v t i ≠ 0).card ≤ 2) ∧
      X = ∑ t, vecMulVec (v t) (v t) := by
  classical
  obtain ⟨m, w, hsparse, hw⟩ := hgram
  let support (t : Fin m) := Finset.univ.filter fun i => w t i ≠ 0
  have hmem (t : Fin m) (i : Fin n) : i ∈ support t ↔ w t i ≠ 0 := by
    simp [support]
  have hreal (i j : Fin n) : X i j = ∑ t, (w t i * star (w t j)).re := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).re) hw
    simpa only [Matrix.map_apply, Complex.ofReal_re, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.re_sum] using h
  have hdiag (i : Fin n) : X i i = ∑ t, Complex.normSq (w t i) := by
    rw [hreal]
    apply Finset.sum_congr rfl
    intro t _
    simp [Complex.mul_conj]
  have hsymm (i j : Fin n) : X i j = X j i := by
    rw [hreal, hreal]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  let pairs := (Finset.univ : Finset (Fin n)).powersetCard 2
  have horient (p : pairs) : ∃ i j : Fin n, i ≠ j ∧ p.val = {i, j} :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp p.property).2
  choose left right hne hpair using horient
  let fiber (p : Finset (Fin n)) := Finset.univ.filter fun t => support t = p
  have hcross (i j : Fin n) (hij : i ≠ j) :
      X i j = ∑ t ∈ fiber {i, j}, (w t i * star (w t j)).re := by
    rw [hreal]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t _ ht
    by_contra hnonzero
    have hi : w t i ≠ 0 := by
      intro h
      exact hnonzero (by simp [h])
    have hj : w t j ≠ 0 := by
      intro h
      exact hnonzero (by simp [h])
    exact ht (by simpa [fiber] using
      pair_subset_support (hsparse t) hij ((hmem t i).2 hi) ((hmem t j).2 hj))
  have hcompress (p : pairs) := compress_complex_pair_moments (fiber p.val) w
    (left p) (right p) (X (left p) (right p)) (hnonneg _ _)
    (by rw [hpair p]; exact hcross _ _ (hne p))
  choose x y slack hx hy hslack hxy hxx hyy _ using hcompress
  let edge (p : pairs) (i : Fin n) :=
    if i = left p then x p else if i = right p then y p else 0
  have hedge_nonneg (p : pairs) (i : Fin n) : 0 ≤ edge p i := by
    dsimp [edge]
    split_ifs <;> first | exact hx p | exact hy p | exact le_rfl
  have hedge_zero (p : pairs) (i : Fin n) (hi : i ∉ p.val) : edge p i = 0 := by
    rw [hpair p] at hi
    have hne' : i ≠ left p ∧ i ≠ right p := by simpa using hi
    simp [edge, hne'.1, hne'.2]
  have hedge_budget (p : pairs) (i : Fin n) :
      edge p i ^ 2 ≤ ∑ t ∈ fiber p.val, Complex.normSq (w t i) := by
    by_cases hl : i = left p
    · subst i
      simpa [edge] using (hxx p).le
    by_cases hr : i = right p
    · subst i
      simp only [edge, ite_eq_right hl, ← hyy p]
      exact le_add_of_nonneg_right (hslack p)
    · simpa [edge, hl, hr] using
        (Finset.sum_nonneg fun t (_ : t ∈ fiber p.val) => Complex.normSq_nonneg (w t i))
  have htotal_budget (i : Fin n) : (∑ p : pairs, edge p i ^ 2) ≤ X i i := by
    calc
      _ ≤ ∑ p : pairs, ∑ t ∈ fiber p.val, Complex.normSq (w t i) :=
        Finset.sum_le_sum fun p _ => hedge_budget p i
      _ = ∑ p ∈ pairs, ∑ t ∈ fiber p, Complex.normSq (w t i) :=
        pairs.sum_coe_sort (fun p => ∑ t ∈ fiber p, Complex.normSq (w t i))
      _ ≤ X i i := by
        rw [hdiag]
        exact Finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg
          (s := Finset.univ) (g := support)
          (fun p _ => Finset.sum_nonneg fun t _ => Complex.normSq_nonneg (w t i))
  have hedge_support (p : pairs) :
      (Finset.univ.filter fun i => edge p i ≠ 0).card ≤ 2 := by
    rw [← (Finset.mem_powersetCard.mp p.property).2]
    exact Finset.card_le_card fun i hi =>
      Classical.byContradiction fun hz => (Finset.mem_filter.mp hi).2 (hedge_zero p i hz)
  let vertex (j i : Fin n) :=
    if i = j then Real.sqrt (X j j - ∑ p : pairs, edge p j ^ 2) else 0
  have hvertex_nonneg (j i : Fin n) : 0 ≤ vertex j i := by
    simp [vertex, apply_ite, Real.sqrt_nonneg]
  have hvertex_support (j : Fin n) :
      (Finset.univ.filter fun i => vertex j i ≠ 0).card ≤ 2 := by
    calc
      _ ≤ ({j} : Finset (Fin n)).card := by
        apply Finset.card_le_card
        intro i hi
        by_contra hn
        exact (Finset.mem_filter.mp hi).2 (by simp [vertex, show i ≠ j by simpa using hn])
      _ ≤ 2 := by simp
  have hedge_offdiag (i j : Fin n) (hij : i ≠ j) :
      (∑ p : pairs, edge p i * edge p j) = X i j := by
    let p₀ : pairs := ⟨{i, j}, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp [hij]⟩⟩
    rw [Finset.sum_eq_single p₀]
    · have hil : i = left p₀ ∨ i = right p₀ := by
        have hi : i ∈ p₀.val := by simp [p₀]
        rw [hpair] at hi
        simpa using hi
      have hjl : j = left p₀ ∨ j = right p₀ := by
        have hj : j ∈ p₀.val := by simp [p₀]
        rw [hpair] at hj
        simpa using hj
      rcases hil with hil | hir <;> rcases hjl with hjl | hjr
      · exact (hij (hil.trans hjl.symm)).elim
      · simp [edge, hil, hjr, Ne.symm (hne p₀), hxy]
      · simp [edge, hir, hjl, Ne.symm (hne p₀), mul_comm (y p₀), hxy, hsymm]
      · exact (hij (hir.trans hjr.symm)).elim
    · intro p _ hp
      by_cases hi : i ∈ p.val
      · have hj : j ∉ p.val := by
          intro hj
          exact hp (Subtype.ext (pair_subset_support
            (Finset.mem_powersetCard.mp p.property).2.le hij hi hj))
        simp [hedge_zero p j hj]
      · simp [hedge_zero p i hi]
    · simp
  let Index := Fin n ⊕ pairs
  let factor : Index → Fin n → ℝ := Sum.elim vertex edge
  let e := Fintype.equivFin Index
  refine ⟨Fintype.card Index, factor ∘ e.symm, ?_, ?_, ?_, ?_⟩
  · simp [Index, pairs]
  · have hfactor (a : Index) (i : Fin n) : 0 ≤ factor a i := by
      cases a with
      | inl j => exact hvertex_nonneg j i
      | inr p => exact hedge_nonneg p i
    exact fun t i => hfactor (e.symm t) i
  · have hfactor (a : Index) : (Finset.univ.filter fun i => factor a i ≠ 0).card ≤ 2 := by
      cases a with
      | inl j => exact hvertex_support j
      | inr p => exact hedge_support p
    exact fun t => hfactor (e.symm t)
  · ext i j
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Function.comp_apply]
    rw [Equiv.sum_comp e.symm (fun t => factor t i * factor t j), Fintype.sum_sum_type]
    change X i j = (∑ v, vertex v i * vertex v j) + ∑ p : pairs, edge p i * edge p j
    by_cases hij : i = j
    · subst j
      rw [Finset.sum_eq_single i]
      · simp only [vertex, ite_eq_left rfl, ← sq, Real.sq_sqrt (sub_nonneg.mpr (htotal_budget i))]
        ring
      · intro v _ hv
        simp [vertex, Ne.symm hv]
      · simp
    · rw [hedge_offdiag i j hij]
      have hvertex_zero : (∑ v, vertex v i * vertex v j) = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        by_cases hi : i = v
        · have hj : j ≠ v := fun h => hij (hi.trans h.symm)
          simp [vertex, hj]
        · simp [vertex, hi]
      rw [hvertex_zero, zero_add]

end

end D5.S3.Quantum.Measurement.FactorWidth.NonnegativeFactorWidthTwo
