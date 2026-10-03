/- GID: D5/S3/Arith/DiophantineApproximation/BinaryForm
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/BinaryForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An irrational complex root of a suitable integer polynomial has multiplicity below half its degree. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable

-- Used only inside proofs.

@[expose] public section

open Polynomial

theorem Polynomial.two_mul_count_roots_lt_natDegree {g : ℤ[X]} (hg : g ≠ 0) {r : ℂ}
    (hr : r ∈ (g.map (Int.castRingHom ℂ)).roots) (hirr : r ∉ Set.range (algebraMap ℚ ℂ))
    (h3 : 3 ≤ (g.map (Int.castRingHom ℂ)).roots.toFinset.card) :
    2 * (g.map (Int.castRingHom ℂ)).roots.count r < g.natDegree := by
  classical
  set gq := g.map (Int.castRingHom ℚ) with hgq
  have hgq0 : gq ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hg
  have hgc : g.map (Int.castRingHom ℂ) = gq.map (algebraMap ℚ ℂ) := by
    rw [hgq, Polynomial.map_map]
    congr 1
  have hdeg : g.natDegree = gq.natDegree :=
    (natDegree_map_eq_of_injective (RingHom.injective_int _) g).symm
  rw [hgc] at hr h3 ⊢
  rw [hdeg]
  set gc := gq.map (algebraMap ℚ ℂ) with hgcdef
  have hgc0 : gc ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective).mpr hgq0
  have hroot : gc.IsRoot r := (mem_roots hgc0).mp hr
  have hint : IsIntegral ℚ r := by
    refine IsAlgebraic.isIntegral ⟨gq, hgq0, ?_⟩
    rw [aeval_def, ← eval_map]
    exact hroot
  set p := minpoly ℚ r with hp
  have hpmon : p.Monic := minpoly.monic hint
  have hk : 2 ≤ p.natDegree := by
    have h0 : 0 < p.natDegree := minpoly.natDegree_pos hint
    have h1 : p.natDegree ≠ 1 := fun h ↦ hirr (minpoly.natDegree_eq_one_iff.mp h)
    omega
  have hsep : (p.map (algebraMap ℚ ℂ)).Separable :=
    (PerfectField.separable_of_irreducible (minpoly.irreducible hint)).map
  have hp0 : p.map (algebraMap ℚ ℂ) ≠ 0 := (hpmon.map _).ne_zero
  have hpow_le : ∀ j : ℕ, rootMultiplicity r ((p.map (algebraMap ℚ ℂ)) ^ j) ≤ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hp0) hp0)]
      have := rootMultiplicity_le_one_of_separable hsep r
      omega
  set μ := gc.roots.count r with hμ
  have hμr : μ = rootMultiplicity r gc := count_roots gc
  -- `(minpoly ℚ r) ^ μ ∣ g`, one factor at a time
  have hdvd : ∀ j ≤ μ, p ^ j ∣ gq := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨h, hh⟩ := ih (by omega)
      suffices hph : p ∣ h by
        rw [pow_succ, hh]
        exact mul_dvd_mul_left _ hph
      refine minpoly.dvd ℚ r ?_
      by_contra hne
      have h0 : rootMultiplicity r (h.map (algebraMap ℚ ℂ)) = 0 :=
        rootMultiplicity_eq_zero (by rwa [IsRoot, eval_map, ← aeval_def])
      have hmap : gc = (p.map (algebraMap ℚ ℂ)) ^ j * h.map (algebraMap ℚ ℂ) := by
        rw [hgcdef, hh, Polynomial.map_mul, Polynomial.map_pow]
      have := hpow_le j
      rw [hmap, rootMultiplicity_mul (hmap ▸ hgc0)] at hμr
      omega
  obtain ⟨h, hh⟩ := hdvd μ le_rfl
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hh
    exact hgq0 hh
  have hdegeq : gq.natDegree = μ * p.natDegree + h.natDegree := by
    rw [hh, natDegree_mul (pow_ne_zero _ hpmon.ne_zero) hh0, natDegree_pow]
  have hμ1 : 1 ≤ μ := Multiset.count_pos.mpr hr
  rcases Nat.eq_zero_or_pos h.natDegree with hh1 | hh1
  · -- a constant cofactor: every root of `g` is a root of the minimal polynomial
    have hsub : gc.roots.toFinset ⊆ (p.map (algebraMap ℚ ℂ)).roots.toFinset := by
      intro r' hr'
      rw [Multiset.mem_toFinset, mem_roots hgc0] at hr'
      rw [Multiset.mem_toFinset, mem_roots hp0]
      obtain ⟨c, hC⟩ : ∃ c, h = C c := ⟨_, eq_C_of_natDegree_eq_zero hh1⟩
      have hc : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at hC
        exact hh0 hC
      have : gc = (p.map (algebraMap ℚ ℂ)) ^ μ * C (algebraMap ℚ ℂ c) := by
        rw [hgcdef, hh, Polynomial.map_mul, Polynomial.map_pow, hC, map_C]
      rw [this, IsRoot, eval_mul, eval_pow, eval_C, mul_eq_zero] at hr'
      rcases hr' with hr' | hr'
      · exact pow_eq_zero_iff (by omega) |>.mp hr'
      · exact absurd ((algebraMap ℚ ℂ).injective (hr'.trans (map_zero _).symm)) hc
    have hk3 : 3 ≤ p.natDegree := by
      refine h3.trans ((Finset.card_le_card hsub).trans ?_)
      refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
      exact natDegree_map_le
    have : 3 * μ ≤ μ * p.natDegree := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hk3
    omega
  · have : 2 * μ ≤ μ * p.natDegree := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hk
    omega

