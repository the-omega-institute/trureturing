/- GID: D5/S3/Combinatorics/RealRootedPermutations/Realization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RealRootedPermutations/Realization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.BigOperators, mathlib/module/Mathlib.Algebra.BigOperators.Ring.Finset, mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.Finset, mathlib/module/Mathlib.Algebra.BigOperators.Intervals, mathlib/module/Mathlib.Algebra.BigOperators.Fin, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Positivity, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Integer heights and dominant prefix products realize every unimodal coefficient ordering strictly. -/

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19903; product_zpow. -/
import D5.S3.Combinatorics.RealRootedPermutations.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Polynomial
open scoped BigOperators
namespace D5.S3.Combinatorics.RealRootedPermutations.Realization
noncomputable section

private lemma coefficient_formula {n : ℕ} (r : Fin (n + 1) → ℝ) (k : ℕ) :
    coeffs r k = ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
      ∏ i ∈ S, r i := by
  classical
  unfold coeffs
  rw [Finset.prod_one_add, finsetSum_coeff]
  have he (S : Finset (Fin (n + 1))) :
      (∏ i ∈ S, C (r i) * X) = C (∏ i ∈ S, r i) * X ^ S.card := by
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const]
  simp_rw [he, coeff_C_mul_X_pow]
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [eq_comm]

private def weight {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) (k : ℕ) : ℤ :=
  if hk : k < n + 1 then 2 ^ (n - (π.symm ⟨k, hk⟩).val) else 0

private def height {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) : ℕ → ℤ
  | 0 => 0
  | k + 1 => 2 ^ (n + 1) - weight π k

private def slope {n : ℕ} (π : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) : ℤ :=
  height π (i.val + 1) - height π i.val

private lemma weight_pos {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : 0 < weight π i := by
  simp only [weight, dite_eq_left i.isLt]
  positivity

private lemma weight_double {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) (h : π.symm i < π.symm j) :
    2 * weight π j ≤ weight π i := by
  simp only [weight, dite_eq_left i.isLt, dite_eq_left j.isLt]
  have hi := (π.symm i).isLt
  have hj := (π.symm j).isLt
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    (show n - (π.symm j).val + 1 ≤ n - (π.symm i).val by
      change (π.symm i).val < (π.symm j).val at h
      omega)
  rw [pow_succ] at hpow
  linarith

private lemma height_rank {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) (h : π.symm i < π.symm j) :
    height π (i.val + 1) + 1 ≤ height π (j.val + 1) := by
  have hd := weight_double π i j h
  have hp := weight_pos π j
  simp only [height]
  omega

private lemma slope_step {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (hπ : IsUnimodal π) (k : ℕ) (hk : k + 1 < n + 1) :
    slope π ⟨k + 1, hk⟩ < slope π ⟨k, by omega⟩ := by
  have hp := weight_pos π (⟨k + 1, hk⟩ : Fin (n + 1))
  cases k with
  | zero =>
    have hb : weight π 0 ≤ (2 : ℤ) ^ n := by
      simp only [weight, dite_eq_left (show 0 < n + 1 by omega)]
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    simp only [slope, height] at *
    have he : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
    omega
  | succ k =>
    let a : Fin (n + 1) := ⟨k, by omega⟩
    let b : Fin (n + 1) := ⟨k + 1, by omega⟩
    let c : Fin (n + 1) := ⟨k + 1 + 1, hk⟩
    have hwb := weight_pos π b
    by_cases hb : b ≤ π (Fin.last n)
    · have hd := weight_double π a b (hπ.1 a b (by simp [a, b]) hb)
      simp only [slope, height]
      change 2 * weight π (k + 1) ≤ weight π k at hd
      change 0 < weight π (k + 1 + 1) at hp
      omega
    · have hd := weight_double π c b
        (hπ.2 b c (le_of_lt (lt_of_not_ge hb)) (by simp [b, c]))
      have ha := weight_pos π a
      simp only [slope, height]
      change 2 * weight π (k + 1) ≤ weight π (k + 1 + 1) at hd
      change 0 < weight π k at ha
      omega

private lemma slope_antitone {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (hπ : IsUnimodal π) : Antitone (slope π) := by
  apply StrictAnti.antitone
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  exact slope_step π hπ i.val (by omega)


private def initialSegment {N : ℕ} (k : ℕ) (hk : k ≤ N) : Finset (Fin N) :=
  Finset.univ.map (Fin.castLEEmb hk)

private lemma initialSegment_card {N k : ℕ} (hk : k ≤ N) : (initialSegment k hk).card = k := by
  simp [initialSegment]

private lemma initialSegment_sum {n k : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (hk : k ≤ n + 1) : ∑ i ∈ initialSegment k hk, slope π i = height π k := by
  simp only [initialSegment, Finset.sum_map, Fin.castLEEmb, Function.Embedding.coeFn_mk,
    slope, Fin.val_castLE]
  rw [Fin.sum_univ_eq_sum_range (fun j => height π (j + 1) - height π j),
    Finset.sum_range_sub]
  simp [height]


private lemma subset_sum_le {n k : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (hπ : IsUnimodal π) (hk : k ≤ n + 1) (S : Finset (Fin (n + 1)))
    (hS : S.card = k) : ∑ i ∈ S, slope π i ≤ height π k := by
  classical
  have hindex (i : Fin k) : i.val ≤ (S.orderEmbOfFin hS i).val := by
    cases k with
    | zero => exact Fin.elim0 i
    | succ k =>
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ i ih =>
        have hh := (S.orderEmbOfFin hS).strictMono (Fin.castSucc_lt_succ (i := i))
        change (S.orderEmbOfFin hS i.castSucc).val <
          (S.orderEmbOfFin hS i.succ).val at hh
        change i.val ≤ _ at ih
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hh)
  calc
    ∑ i ∈ S, slope π i = ∑ j : Fin k, slope π (S.orderEmbOfFin hS j) := by
      conv_lhs => rw [← S.map_orderEmbOfFin_univ hS]
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ j : Fin k, slope π (Fin.castLE hk j) := by
      apply Finset.sum_le_sum
      intro j _
      exact slope_antitone π hπ (hindex j)
    _ = height π k := by
      simpa only [initialSegment, Finset.sum_map, Fin.coe_castLEEmb] using initialSegment_sum π hk

lemma product_zpow {ι : Type*} (S : Finset ι) (b : ι → ℤ) (T : ℝ)
    (hT : T ≠ 0) : ∏ i ∈ S, T ^ b i = T ^ (∑ i ∈ S, b i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hT]


private lemma coefficient_bounds {n k : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (hπ : IsUnimodal π) (hk : k ≤ n + 1) (T : ℝ) (hT : 1 < T) :
    T ^ height π k ≤ coeffs (fun i => T ^ slope π i) k ∧
    coeffs (fun i => T ^ slope π i) k ≤ (2 : ℝ) ^ (n + 1) * T ^ height π k := by
  classical
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  rw [coefficient_formula]
  simp_rw [product_zpow _ _ _ hT0.ne']
  constructor
  · have hm : initialSegment k hk ∈
        (Finset.univ : Finset (Fin (n + 1))).powersetCard k := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, initialSegment_card hk⟩
    have h := Finset.single_le_sum
      (fun S (_ : S ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k) =>
        (zpow_pos hT0 (∑ i ∈ S, slope π i)).le) hm
    simpa only [initialSegment_sum π hk] using h
  · have hcard : ((Finset.univ : Finset (Fin (n + 1))).powersetCard k).card ≤
        2 ^ (n + 1) := by
      calc
        _ ≤ ((Finset.univ : Finset (Fin (n + 1))).powerset).card :=
          Finset.card_le_card (by
            intro S hS
            exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1)
        _ = _ := by simp
    calc
      _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
          T ^ height π k := by
        apply Finset.sum_le_sum
        intro S hS
        exact zpow_le_zpow_right₀ hT.le
          (subset_sum_le π hπ hk S (Finset.mem_powersetCard.mp hS).2)
      _ = (((Finset.univ : Finset (Fin (n + 1))).powersetCard k).card : ℝ) *
          T ^ height π k := by simp
      _ ≤ (2 : ℝ) ^ (n + 1) * T ^ height π k := by
        apply mul_le_mul_of_nonneg_right _ (zpow_pos hT0 _).le
        exact_mod_cast hcard

/-- Every unimodal permutation strictly sorts a positive real-rooted product. -/
theorem realize_strict {n : ℕ} (π : Equiv.Perm (Fin (n + 1)))
    (hπ : IsUnimodal π) : ∃ r : Fin (n + 1) → ℝ, (∀ i, 0 < r i) ∧
      StrictMono (fun t : Fin (n + 1) => coeffs r ((π t : ℕ) + 1)) := by
  let T : ℝ := 2 ^ (n + 1) + 1
  have hpow : 0 < (2 : ℝ) ^ (n + 1) := by positivity
  have hT : 1 < T := by dsimp [T]; linarith
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  refine ⟨fun i => T ^ slope π i, fun i => zpow_pos hT0 _, ?_⟩
  intro t u htu
  have hh := height_rank π (π t) (π u) (by simpa using htu)
  have ht' := coefficient_bounds π hπ (show (π t).val + 1 ≤ n + 1 by omega) T hT
  have hu' := coefficient_bounds π hπ (show (π u).val + 1 ≤ n + 1 by omega) T hT
  apply lt_of_le_of_lt ht'.2
  apply lt_of_lt_of_le _ hu'.1
  calc
    (2 : ℝ) ^ (n + 1) * T ^ height π ((π t).val + 1) <
        T * T ^ height π ((π t).val + 1) := by
      apply mul_lt_mul_of_pos_right _ (zpow_pos hT0 _)
      dsimp [T]
      linarith
    _ = T ^ (height π ((π t).val + 1) + 1) := by
      rw [zpow_add₀ hT0.ne', zpow_one, mul_comm]
    _ ≤ T ^ height π ((π u).val + 1) := zpow_le_zpow_right₀ hT.le hh

end
end D5.S3.Combinatorics.RealRootedPermutations.Realization
