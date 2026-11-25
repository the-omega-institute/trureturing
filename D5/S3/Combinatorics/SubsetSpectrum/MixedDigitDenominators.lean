/- GID: D5/S3/Combinatorics/SubsetSpectrum/MixedDigitDenominators
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/MixedDigitDenominators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dense four-digit integer coverage excludes mixed reduced denominators two and three. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open Finset

namespace D5.S3.Combinatorics.SubsetSpectrum.MixedDigitDenominators

private theorem recover_two_digits {a b : ℤ} (aOdd : ¬ (2 : ℤ) ∣ a)
    (bNondiv : ¬ (3 : ℤ) ∣ b) {x x' y y' : Fin 4} {z : ℤ}
    (integral : 3 * a * ((x.val : ℤ) - (x'.val : ℤ)) +
      2 * b * ((y.val : ℤ) - (y'.val : ℤ)) = 6 * z)
    (qx : x.val / 2 = x'.val / 2) (qy : y.val / 3 = y'.val / 3) :
    x = x' ∧ y = y' := by
  have hxmod : x.val % 2 = x'.val % 2 := by
    have h := congrArg (fun n : ℤ => (n : ZMod 2)) integral
    push_cast at h
    simp only [show (3 : ZMod 2) = 1 by decide, show (2 : ZMod 2) = 0 by decide,
      show (6 : ZMod 2) = 0 by decide, one_mul, zero_mul, add_zero] at h
    have nonzero : (a : ZMod 2) ≠ 0 := fun h => aOdd ((ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp h)
    have eq := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left nonzero)
    simpa only [ZMod.val_natCast] using congrArg ZMod.val eq
  have hymod : y.val % 3 = y'.val % 3 := by
    have h := congrArg (fun n : ℤ => (n : ZMod 3)) integral
    push_cast at h
    simp only [show (3 : ZMod 3) = 0 by decide, show (6 : ZMod 3) = 0 by decide,
      zero_mul, zero_add] at h
    have nonzero : (b : ZMod 3) ≠ 0 := fun h => bNondiv ((ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp h)
    have nonzeroTwo : (2 : ZMod 3) ≠ 0 := by decide
    have eq := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (mul_ne_zero nonzeroTwo nonzero))
    simpa only [ZMod.val_natCast] using congrArg ZMod.val eq
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

theorem no_mixed_denominators_of_capacity_gap {J : Type*} [Fintype J] {L : ℕ}
    (w : J → ℝ) (digit : Fin L → J → Fin 4)
    (calibration : ∀ k, ∑ j, (digit k j).val * w j = (k.val : ℝ))
    (gap : 4^(Fintype.card J - 1) < L) {i j : J} (ne : i ≠ j)
    {a b : ℤ} (aOdd : ¬ (2 : ℤ) ∣ a) (bNondiv : ¬ (3 : ℤ) ∣ b)
    (wi : 2 * w i = (a : ℝ)) (wj : 3 * w j = (b : ℝ)) : False := by
  classical
  let t : Finset J := (univ.erase i).erase j
  let J' := {k : J // k ∈ t}
  let enc (k : Fin L) : (J' → Fin 4) × Fin 2 × Fin 2 :=
    (fun j' => digit k j'.val, ⟨(digit k i).val / 2, by have := (digit k i).isLt; omega⟩,
      ⟨(digit k j).val / 3, by have := (digit k j).isLt; omega⟩)
  have wSum (k : Fin L) :
      (∑ u ∈ t, (digit k u).val * w u) + (digit k j).val * w j + (digit k i).val * w i =
        (k.val : ℝ) := by
    rw [show t = (univ.erase i).erase j from rfl,
      sum_erase_add _ _ (mem_erase.mpr ⟨ne.symm, mem_univ _⟩),
      sum_erase_add _ _ (mem_univ i), calibration]
  have inj : Function.Injective enc := by
    intro k l eq
    have eqSum : (∑ u ∈ t, (digit k u).val * w u) = ∑ u ∈ t, (digit l u).val * w u := by
      refine sum_congr rfl (fun u hu => ?_)
      have same := congrFun (congrArg Prod.fst eq) (⟨u, hu⟩ : J')
      change digit k u = digit l u at same
      rw [same]
    have real :
        3 * (a : ℝ) * ((digit k i).val - (digit l i).val : ℝ) +
          2 * (b : ℝ) * ((digit k j).val - (digit l j).val : ℝ) =
          6 * ((k.val : ℝ) - (l.val : ℝ)) := by
      have hk := wSum k
      rw [eqSum] at hk
      linear_combination 6*(hk - wSum l) +
        3*((digit k i).val - (digit l i).val : ℝ)*(wi.symm) +
        2*((digit k j).val - (digit l j).val : ℝ)*(wj.symm)
    have hInt :
        3 * a * ((digit k i).val - (digit l i).val : ℤ) +
          2 * b * ((digit k j).val - (digit l j).val : ℤ) =
          6 * ((k.val : ℤ) - (l.val : ℤ)) := by exact_mod_cast real
    have qi := congrArg (fun e => e.2.1.val) eq
    have qj := congrArg (fun e => e.2.2.val) eq
    obtain ⟨di,dj⟩ := recover_two_digits aOdd bNondiv hInt qi qj
    have hk := wSum k
    rw [eqSum, di, dj, wSum l] at hk
    exact Fin.ext (by exact_mod_cast hk.symm)
  have jcard : Fintype.card J' = Fintype.card J - 2 := by
    rw [Fintype.card_coe]
    change #((univ.erase i).erase j) = _
    rw [card_erase_of_mem (mem_erase.mpr ⟨ne.symm, mem_univ _⟩),
      card_erase_of_mem (mem_univ i), card_univ]
    omega
  have remains : Fintype.card J - 2 + 1 = Fintype.card J - 1 := by
    have two : 2 ≤ Fintype.card J := by
      have ht := Finset.card_le_card (Finset.subset_univ ({i,j} : Finset J))
      simpa only [Finset.card_pair ne, Finset.card_univ] using ht
    omega
  have hc := Fintype.card_le_of_injective enc inj
  rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, jcard] at hc
  norm_num at hc
  rw [← pow_succ, remains] at hc
  exact (not_le_of_gt gap) hc

end D5.S3.Combinatorics.SubsetSpectrum.MixedDigitDenominators
