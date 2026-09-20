/- GID: D5/S3/Analytic/RealRootedCoefficientNewton
   generality: G
   mirror-B: D5/B/S3/Analytic/RealRootedCoefficientNewton
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Vieta, mathlib/module/Mathlib.Analysis.Calculus.LocalExtr.Polynomial, mathlib/module/Mathlib.Algebra.Order.Chebyshev, mathlib/module/Mathlib.Data.Multiset.Fintype]
   utility: none
   digest: Licensed upstream Newton inequality for real elementary symmetric functions. -/

/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0; the full license is preserved in
Library/Combinatorics/tao2026newton.md.
Authors: Terence Tao, Hanting Zhang, Johan Commelin, Mantas Bakšys, Yaël Dillies, Kyle Miller.

Source: mathlib4 PR 42876, immutable e3c1793d0e097d9b8d782a323e91c99c2ef0d64c.
Analysis/MeanInequalitiesSymmetric.lean SHA-256:
daab9424b8817d3e6bf62f14fe1bfb1c35cf96a47157897d46af2f64a70da2f2.
Prerequisites: RingTheory/MvPolynomial/Symmetric/Defs.lean,
Algebra/Order/Chebyshev.lean, Data/Multiset/Fintype.lean at the same revision.
Modifications: specialize prerequisites to real numbers; make them local to Newton;
retain only the reduced Newton form; adapt imports and the choose cast to v4.33.0.
Retirement: when this repository's own pinned Mathlib supplies equivalent declarations,
delete this port and directly import/apply those declarations in its Crown consumer.
-/

import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Multiset.Fintype

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.RealRootedCoefficientNewton

open Multiset Polynomial Real

/-- Newton's reduced inequality, transplanted from the immutable upstream source. -/
theorem esymm_mul_esymm_le_sq_esymm (s : Multiset ℝ) (k : ℕ) :
    ((k : ℝ) + 2) * ((s.card : ℝ) - k) * (s.esymm k * s.esymm (k + 2))
    ≤ ((k : ℝ) + 1) * ((s.card : ℝ) - k - 1) * (s.esymm (k + 1)) ^ 2 := by
  classical
  have esymm_cons (a : ℝ) (s : Multiset ℝ) (k : ℕ) :
      (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
    simp [esymm, sum_map_mul_left]

  have esymm_zero (s : Multiset ℝ) : s.esymm 0 = 1 := by
    clear esymm_cons
    simp [esymm]

  have esymm_one (s : Multiset ℝ) : s.esymm 1 = s.sum := by
    clear esymm_cons esymm_zero
    simp [esymm, powersetCard_one]

  have two_mul_esymm_two (s : Multiset ℝ) : 2 * s.esymm 2 =
    s.sum ^ 2 - (s.map (· ^ 2)).sum := by
    clear esymm_zero
    induction s using Multiset.induction with
    | empty => simp [esymm, powersetCard_zero_right]
    | cons a t ih => grind [sum_cons, map_cons]

  have esymm_card (s : Multiset ℝ) : s.esymm s.card = s.prod := by
    clear esymm_cons esymm_zero esymm_one two_mul_esymm_two
    simp [esymm]

  have esymm_eq_zero_of_card_lt {s : Multiset ℝ} {k : ℕ} (hk : s.card < k) : s.esymm k = 0 := by
    clear esymm_cons esymm_zero esymm_one two_mul_esymm_two esymm_card
    simp [esymm, hk]

  have esymm_map_inv_aux (s : Multiset ℝ) : 0 ∉ s →
      ∀ j k, s.card = j + k → (s.map (·⁻¹)).esymm k * s.prod = s.esymm j := by
    clear esymm_one two_mul_esymm_two esymm_eq_zero_of_card_lt
    induction s using Multiset.induction with
    | empty => grind [Multiset.map_zero, card_zero]
    | cons a t _ =>
      intro _ j k _
      cases k
      · grind []
      cases j
      · grind [card_map, prod_map_inv', prod_ne_zero]
      · grind [map_cons, prod_cons, card_cons]

  have esymm_map_inv {s : Multiset ℝ} (h0 : 0 ∉ s) {k : ℕ}
      (hk : k ≤ s.card) : s.esymm k = (s.map (·⁻¹)).esymm (s.card - k) * s.esymm s.card := by
    clear esymm_cons esymm_zero esymm_one two_mul_esymm_two esymm_eq_zero_of_card_lt
    grind []

  have sum_map_eq_sum_toEnumFinset (m : Multiset ℝ) (f : ℝ → ℝ) :
      (m.map f).sum = ∑ i ∈ m.toEnumFinset, f i.1 := by
    clear esymm_cons esymm_zero esymm_one two_mul_esymm_two esymm_card esymm_eq_zero_of_card_lt esymm_map_inv_aux esymm_map_inv
    grind [m.map_toEnumFinset_fst, Multiset.map_map, Finset.sum_map_val]

  have sq_sum_le_card_mul_sum_sq (m : Multiset ℝ) :
      m.sum ^ 2 ≤ m.card * (m.map (· ^ 2)).sum := by
    clear esymm_cons esymm_zero esymm_one two_mul_esymm_two esymm_card esymm_eq_zero_of_card_lt esymm_map_inv_aux esymm_map_inv
    have := sum_map_eq_sum_toEnumFinset m id
    have := _root_.sq_sum_le_card_mul_sum_sq (s := toEnumFinset m) (f := Prod.fst)
    simp_all [sum_map_eq_sum_toEnumFinset m (· ^ 2)]

  have exists_esymm_derivative {s : Multiset ℝ} {n : ℕ} (hs : s.card = n + 1) :
      ∃ t : Multiset ℝ, t.card = n ∧
        ∀ k ≤ n, (n + 1) * t.esymm k = (n + 1 - k) * s.esymm k := by
    clear esymm_cons esymm_zero esymm_one two_mul_esymm_two esymm_card esymm_eq_zero_of_card_lt esymm_map_inv_aux esymm_map_inv sum_map_eq_sum_toEnumFinset sq_sum_le_card_mul_sum_sq
    set f : ℝ[X] := (s.map (X + C ·)).prod with hf
    set g : ℝ[X] := C ((n : ℝ) + 1)⁻¹ * f.derivative
    set t := g.roots.map (- ·)
    have : f.natDegree = n + 1 := by
      rw [hf, natDegree_multiset_prod_of_monic]
      · simp [hs, add_comm]
      · grind [mem_map, monic_X_add_C]
    have : f.derivative.coeff n = (n : ℝ) + 1 := by
      grind [coeff_derivative, Monic.coeff_natDegree, monic_multiset_prod_of_monic, monic_X_add_C]
    have : f.derivative.natDegree ≤ n := by grind [natDegree_derivative_le]
    have : f.derivative.natDegree ≥ n := le_natDegree_of_ne_zero (by grind)
    have : g.natDegree = n := by grind [natDegree_C_mul]
    have : g.Splits := by grind [splits_iff_card_roots, roots_C_mul, card_roots_le_derivative, f.derivative.card_roots', Splits.multisetProd, mem_map, Splits.X_add_C]
    have : g = (t.map (X + C ·)).prod := by
      grind [prod_multiset_X_sub_C_of_monic_of_roots_card_eq, splits_iff_card_roots, Multiset.map_map, Monic, leadingCoeff]
    have : t.card = n := by grind [card_map, splits_iff_card_roots]
    refine ⟨t, this, fun k hk ↦ ?_⟩
    have : ((n - k + 1 : ℕ) : ℝ) = n + 1 - k := by simp [Nat.cast_sub hk]; grind
    have : g.coeff (n - k) = t.esymm k := by grind [prod_X_add_C_coeff]
    grind [coeff_derivative, prod_X_add_C_coeff]

  have exists_esymm_div_choose {s : Multiset ℝ} {n : ℕ} (hs : s.card = n + 1) : ∃ t : Multiset ℝ, t.card = n ∧
      ∀ k ≤ n, t.esymm k / (n.choose k) = s.esymm k / ((n + 1).choose k) := by
    clear esymm_cons esymm_zero esymm_one two_mul_esymm_two esymm_card esymm_eq_zero_of_card_lt esymm_map_inv_aux esymm_map_inv sum_map_eq_sum_toEnumFinset sq_sum_le_card_mul_sum_sq
    obtain ⟨t, htc, ht⟩ := exists_esymm_derivative hs
    refine ⟨t, htc, fun k hk ↦ ?_⟩
    rw [div_eq_div_iff]
    · apply mul_left_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)
      grind [Nat.cast_sub, (mod_cast n.choose_mul_succ_eq k : (n.choose k : ℝ) * (n + 1) =
        ((n + 1).choose k : ℝ) * (n + 1 - k : ℕ) )]
    all_goals exact_mod_cast (Nat.choose_pos (by omega)).ne'

  let nesymm (s : Multiset ℝ) (k : ℕ) : ℝ := s.esymm k / (s.card.choose k)

  have newton_base (s : Multiset ℝ) (n : ℕ) (hs : s.card = n) :
      (n : ℝ) ^ 2 * (2 * s.esymm 2) ≤ (n : ℝ) * ((n : ℝ) - 1) * (s.esymm 1) ^ 2 := by
    clear esymm_cons esymm_zero esymm_card esymm_eq_zero_of_card_lt esymm_map_inv_aux esymm_map_inv sum_map_eq_sum_toEnumFinset exists_esymm_derivative exists_esymm_div_choose nesymm
    subst hs
    rw [esymm_one, two_mul_esymm_two s]
    nlinarith [mul_nonneg s.card.cast_nonneg (sub_nonneg.mpr (sq_sum_le_card_mul_sum_sq s))]

  have newton_aux (n : ℕ) : ∀ s : Multiset ℝ, s.card = n → ∀ k, k + 2 ≤ n →
      (nesymm s k) * (nesymm s (k + 2)) ≤ (nesymm s (k + 1)) ^ 2 := by
    clear esymm_cons esymm_zero esymm_one two_mul_esymm_two esymm_eq_zero_of_card_lt esymm_map_inv_aux sum_map_eq_sum_toEnumFinset sq_sum_le_card_mul_sum_sq exists_esymm_derivative
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs k hk
      rcases eq_or_lt_of_le hk with rfl | _
      · by_cases h0 : 0 ∈ s
        · change nesymm s k * (s.esymm (k + 2) / (s.card.choose (k + 2))) ≤ _
          rw [← hs, esymm_card, prod_eq_zero h0]
          grind [sq_nonneg]
        · have : 2 * (k + 2) * (s.esymm k * s.esymm (k + 2)) ≤ (k + 1) * (s.esymm (k + 1)) ^ 2 := by
            rw [esymm_map_inv h0 (by omega : k + 1 ≤ s.card),
            esymm_map_inv h0 (by omega : k ≤ s.card),
            hs, (by grind : (k + 2) - (k + 1) = 1), (by grind : (k + 2) - k = 2)]
            have := newton_base (s.map (·⁻¹)) (k + 2) (by grind [card_map])
            push_cast at this
            nlinarith [sq_nonneg (s.esymm (k + 2))]
          have : ((k + 2).choose k : ℝ) * 2 = (k + 2) * (k + 1) := by
            norm_cast
            rw [← (k + 2).choose_symm (by omega), (by omega : k + 2 - k = 2)]
            rcases k.even_or_odd with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;> grind [Nat.choose_two_right]
          have : ((k + 2).choose (k + 1) : ℝ) = k + 2 := by
            rw [(by rfl : k + 1 = k + 2 - 1), (k + 2).choose_symm (k := 1) (by omega)]
            simp
          unfold nesymm
          field_simp
          rw [hs, this, div_le_div_iff₀ (mod_cast (by grind [Nat.choose_pos])) (by positivity)]
          simp
          nlinarith
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        grind [exists_esymm_div_choose hs]

  have nesymm_mul_nesymm_le_sq_nesymm (s : Multiset ℝ) (k : ℕ) :
      (nesymm s k) * (nesymm s (k + 2)) ≤ (nesymm s (k + 1)) ^ 2 := by
    clear esymm_cons esymm_zero esymm_one two_mul_esymm_two esymm_card esymm_map_inv_aux esymm_map_inv sum_map_eq_sum_toEnumFinset sq_sum_le_card_mul_sum_sq exists_esymm_derivative exists_esymm_div_choose newton_base
    rcases le_or_gt (k + 2) s.card with hk | hk
    · exact newton_aux s.card s rfl k hk
    · simp only [nesymm, hk, esymm_eq_zero_of_card_lt, zero_div]
      nlinarith

  have esymm_mul_esymm_le_sq_esymm (s : Multiset ℝ) (k : ℕ) :
      (s.card.choose (k + 1)) ^ 2 * (s.esymm k * s.esymm (k + 2))
        ≤ (s.card.choose k) * (s.card.choose (k + 2)) * (s.esymm (k + 1)) ^ 2 := by
    clear esymm_cons esymm_zero esymm_one two_mul_esymm_two esymm_card esymm_map_inv_aux esymm_map_inv sum_map_eq_sum_toEnumFinset sq_sum_le_card_mul_sum_sq exists_esymm_derivative exists_esymm_div_choose newton_base newton_aux
    rcases le_or_gt (k + 2) s.card with hk | hk
    · have : (0 : ℝ) < s.card.choose k := mod_cast Nat.choose_pos (by omega)
      have : (0 : ℝ) < s.card.choose (k + 1) := mod_cast Nat.choose_pos (by omega)
      have : (0 : ℝ) < s.card.choose (k + 2) := mod_cast Nat.choose_pos hk
      have h := nesymm_mul_nesymm_le_sq_nesymm s k
      simp only [nesymm] at h
      field_simp at h
      nlinarith
    · simp only [hk, esymm_eq_zero_of_card_lt, mul_zero]
      positivity
  clear esymm_cons esymm_zero esymm_one two_mul_esymm_two esymm_card esymm_map_inv_aux esymm_map_inv sum_map_eq_sum_toEnumFinset sq_sum_le_card_mul_sum_sq exists_esymm_derivative exists_esymm_div_choose nesymm newton_base newton_aux nesymm_mul_nesymm_le_sq_nesymm
  rcases (by omega : k + 2 ≤ s.card ∨ k + 1 = s.card ∨ s.card < k + 1) with _ | h | _
  · have : (0 : ℝ) < (s.card.choose (k + 1)) ^ 2 :=
      sq_pos_of_pos (mod_cast Nat.choose_pos (by omega))
    have : (0 : ℝ) ≤ (k + 2) * (s.card - k) :=
      mul_nonneg (by positivity) (by rw [sub_nonneg]; exact_mod_cast (by omega))
    have : (k + 2) * (s.card - k) * ((s.card.choose k : ℝ) * (s.card.choose (k + 2)))
        = (k + 1) * (s.card - k - 1) * (s.card.choose (k + 1)) ^ 2 := by
      rw [(by rw [Nat.cast_sub (by omega)]; grind : (s.card : ℝ) - k - 1 = (s.card - (k + 1) : ℕ)),
        ← Nat.cast_sub (by omega)]
      norm_cast
      grind [Nat.choose_succ_right_eq]
    nlinarith [esymm_mul_esymm_le_sq_esymm s k]
  · rw [esymm_eq_zero_of_card_lt (k := k + 2) (by omega)]
    simp [← h]
  · rw [esymm_eq_zero_of_card_lt (k := k + 2) (by omega),
      esymm_eq_zero_of_card_lt (k := k + 1) (by omega)]
    simp

end D5.S3.Analytic.RealRootedCoefficientNewton
