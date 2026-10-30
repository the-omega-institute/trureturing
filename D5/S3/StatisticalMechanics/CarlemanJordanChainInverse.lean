/- GID: D5/S3/StatisticalMechanics/CarlemanJordanChainInverse
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CarlemanJordanChainInverse
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Critical Carleman Jordan-chain inverses are increasing-path sums. -/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Real.Basic

/-! The normalized Jordan chain of each critical Carleman truncation is dual to
the rows of powers of its strictly upper triangular part. -/

namespace D5.S3.StatisticalMechanics.CarlemanJordanChainInverse

open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- Principal truncation of the coefficient matrix of the powers of the source series. -/
def carleman (α : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => PowerSeries.coeff (j.val + 1) ((PowerSeries.mk α) ^ (i.val + 1))

/-- The source's normalized upper triangular Jordan chain, with indices shifted by one. -/
def IsJordanChain (α : ℕ → ℝ) (n : ℕ) (w : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ j, (carleman α n - 1) *ᵥ (fun i => w i j) =
    if h : j.val = 0 then 0 else fun i => w i ⟨j.val - 1, by omega⟩) ∧
  (∀ i j, i.val = 0 → w i j = if j.val = 0 then 1 else 0) ∧
  (∀ i j, j < i → w i j = 0)

/-- Increasing-path sum: append the final edge to each shorter path from index zero.
The zero-edge path has weight one exactly at index zero. -/
noncomputable def sigma (α : ℕ → ℝ) (n : ℕ) : ℕ → Fin n → ℝ
  | 0, j => if j.val = 0 then 1 else 0
  | m + 1, j => ∑ i : Fin n, if i < j then sigma α n m i * carleman α n i j else 0

/-- Every critical principal truncation has a normalized Jordan chain, and every such
chain has inverse entries given by the source's increasing-path sum. -/
def claim : Prop :=
  ∀ α : ℕ → ℝ, α 0 = 0 → α 1 = 1 → α 2 ≠ 0 →
    ∀ n : ℕ, 0 < n → (∃ w, IsJordanChain α n w) ∧
      ∀ w, IsJordanChain α n w → IsUnit w.det ∧
        ∀ k j : Fin n, k ≤ j → w⁻¹ k j = sigma α n k.val j

private lemma carleman_structure (α : ℕ → ℝ) (n : ℕ)
    (h0 : α 0 = 0) (h1 : α 1 = 1) :
    (∀ i j : Fin n, j ≤ i → (carleman α n - 1) i j = 0) ∧
    (∀ i j : Fin n, j.val = i.val + 1 →
      (carleman α n - 1) i j = (i.val + 1 : ℕ) * α 2) := by
  let f : PowerSeries ℝ := PowerSeries.mk (fun k => α (k + 1))
  have hf : PowerSeries.mk α = PowerSeries.X * f := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
      h0, map_zero, add_zero] using PowerSeries.eq_X_mul_shift_add_const (PowerSeries.mk α)
  have hc (i j : Fin n) : carleman α n i j =
      if i.val + 1 ≤ j.val + 1 then
        PowerSeries.coeff (j.val + 1 - (i.val + 1)) (f ^ (i.val + 1)) else 0 := by
    change PowerSeries.coeff _ ((PowerSeries.mk α) ^ _) = _
    rw [hf, mul_pow, PowerSeries.coeff_X_pow_mul']
  have hfc : PowerSeries.constantCoeff f = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    change PowerSeries.coeff 0 (PowerSeries.mk _) = 1
    simpa only [PowerSeries.coeff_mk, zero_add] using h1
  constructor
  · intro i j hij
    change carleman α n i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0
    by_cases he : i = j
    · subst j
      rw [hc, ite_eq_left (by omega), Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff,
        map_pow, hfc, one_pow, Matrix.one_apply_eq, sub_self]
    · have hji0 : j < i := lt_of_le_of_ne hij (Ne.symm he)
      have hji : j.val < i.val := hji0
      rw [hc, ite_eq_right (by omega), Matrix.one_apply_ne he, sub_self]
  · intro i j hij
    change carleman α n i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j = _
    have he : i ≠ j := by intro h; have := congrArg Fin.val h; omega
    rw [hc, ite_eq_left (by omega), show j.val + 1 - (i.val + 1) = 1 by omega,
      PowerSeries.coeff_one_pow, hfc, one_pow, mul_one, Matrix.one_apply_ne he, sub_zero]
    simp only [f, PowerSeries.coeff_mk]

private lemma back_substitution (n : ℕ) (a : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i j, j ≤ i → a i j = 0)
    (hs : ∀ i j, j.val = i.val + 1 → a i j ≠ 0)
    (k : ℕ) (hk : k < n) (b : Fin n → ℝ)
    (hb : ∀ i, k ≤ i.val → b i = 0) :
    ∃ v : Fin n → ℝ, (∀ i, i.val = 0 → v i = 0) ∧
      (∀ i, k < i.val → v i = 0) ∧ a *ᵥ v = b := by
  classical
  induction k generalizing b with
  | zero =>
    refine ⟨0, ?_, ?_, ?_⟩
    · intro i _; rfl
    · intro i _; rfl
    · rw [Matrix.mulVec_zero]
      exact (funext fun i => (hb i (Nat.zero_le _)).symm)
  | succ k ih =>
    let p : Fin n := ⟨k + 1, hk⟩
    let r : Fin n := ⟨k, by omega⟩
    let c : ℝ := b r / a r p
    let e : Fin n → ℝ := Pi.single p c
    have he : a *ᵥ e = fun i => a i p * c := Matrix.mulVec_single a p c
    have hp : a r p ≠ 0 := hs r p rfl
    have hr : ∀ i : Fin n, k ≤ i.val → (b - a *ᵥ e) i = 0 := by
      intro i hi
      rw [he]
      change b i - a i p * c = 0
      by_cases h : i = r
      · subst i
        dsimp only [c]
        rw [mul_div_cancel₀ _ hp, sub_self]
      · have hir : k < i.val := by
          have : i.val ≠ k := by intro hval; exact h (Fin.ext hval)
          omega
        rw [hb i (by omega), ha i p (by change k + 1 ≤ i.val; omega), zero_mul,
          sub_self]
    obtain ⟨u, hu0, hus, hu⟩ := ih (by omega) (b - a *ᵥ e) hr
    refine ⟨u + e, ?_, ?_, ?_⟩
    · intro i hi
      have hip : i ≠ p := by intro h; have := congrArg Fin.val h; dsimp only [p] at this; omega
      change u i + e i = 0
      rw [hu0 i hi]
      simp only [e, Pi.single_eq_of_ne hip, add_zero]
    · intro i hi
      have hip : i ≠ p := by intro h; subst i; exact (lt_irrefl _ hi)
      change u i + e i = 0
      rw [hus i (by omega)]
      simp only [e, Pi.single_eq_of_ne hip, add_zero]
    · rw [Matrix.mulVec_add, hu, sub_add_cancel]

private lemma chain_exists (α : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (ha : ∀ i j : Fin n, j ≤ i → (carleman α n - 1) i j = 0)
    (hs : ∀ i j : Fin n, j.val = i.val + 1 → (carleman α n - 1) i j ≠ 0) :
    ∃ w, IsJordanChain α n w := by
  classical
  let a : Matrix (Fin n) (Fin n) ℝ := carleman α n - 1
  have build : ∀ t : ℕ, t ≤ n → ∃ w : Matrix (Fin n) (Fin n) ℝ,
      ∀ j : Fin n, j.val < t →
        (a *ᵥ (fun i => w i j) =
          if h : j.val = 0 then 0 else fun i => w i ⟨j.val - 1, by omega⟩) ∧
        (∀ i, i.val = 0 → w i j = if j.val = 0 then 1 else 0) ∧
        (∀ i, j < i → w i j = 0) := by
    intro t ht
    induction t with
    | zero => exact ⟨0, fun j hj => (Nat.not_lt_zero _ hj).elim⟩
    | succ t ih =>
      obtain ⟨w, hw⟩ := ih (by omega)
      have htlt : t < n := by omega
      let j : Fin n := ⟨t, htlt⟩
      have next : ∃ v : Fin n → ℝ,
          (a *ᵥ v = if h : t = 0 then 0 else
            fun i => w i ⟨t - 1, by omega⟩) ∧
          (∀ i, i.val = 0 → v i = if t = 0 then 1 else 0) ∧
          (∀ i, t < i.val → v i = 0) := by
        by_cases ht0 : t = 0
        · refine ⟨fun i => if i.val = 0 then 1 else 0, ?_, ?_, ?_⟩
          · rw [dite_eq_left ht0]
            have he : (fun i : Fin n => if i.val = 0 then (1 : ℝ) else 0) =
                Pi.single ⟨0, hn⟩ 1 := by
              funext i
              simp only [Pi.single_apply, Fin.ext_iff]
            rw [he, Matrix.mulVec_single_one]
            funext i
            exact ha i ⟨0, hn⟩ (Nat.zero_le _)
          · intro i hi
            change (if i.val = 0 then 1 else 0) = _
            rw [ite_eq_left hi, ite_eq_left ht0]
          · intro i hi
            change (if i.val = 0 then 1 else 0) = 0
            rw [ite_eq_right (by omega)]
        · let p : Fin n := ⟨t - 1, by omega⟩
          obtain ⟨v, hv0, hvs, hv⟩ := back_substitution n a ha hs t htlt
            (fun i => w i p) (by
              intro i hi
              exact (hw p (by dsimp only [p]; omega)).2.2 i
                (by change t - 1 < i.val; omega))
          refine ⟨v, ?_, ?_, hvs⟩
          · rw [dite_eq_right ht0]; exact hv
          · intro i hi; rw [ite_eq_right ht0]; exact hv0 i hi
      obtain ⟨v, hv, hv0, hvs⟩ := next
      let u : Matrix (Fin n) (Fin n) ℝ := fun i k => if k.val = t then v i else w i k
      refine ⟨u, ?_⟩
      intro k hk
      by_cases hkt : k.val = t
      · have hcol : (fun i => u i k) = v := by
          funext i; exact ite_eq_left hkt
        refine ⟨?_, ?_, ?_⟩
        · rw [hcol, hv]
          by_cases ht0 : t = 0
          · rw [dite_eq_left ht0, dite_eq_left (hkt.trans ht0)]
          · rw [dite_eq_right ht0, dite_eq_right (by omega)]
            funext i
            change w i ⟨t - 1, _⟩ = if k.val - 1 = t then v i else w i ⟨k.val - 1, _⟩
            rw [ite_eq_right (by omega)]
            congr 1
            apply Fin.ext
            dsimp only
            omega
        · intro i hi
          change (if k.val = t then v i else w i k) = _
          rw [ite_eq_left hkt, hv0 i hi, hkt]
        · intro i hi
          change (if k.val = t then v i else w i k) = 0
          rw [ite_eq_left hkt]
          exact hvs i (by change k.val < i.val at hi; omega)
      · have hklt : k.val < t := by omega
        obtain ⟨hc, hc0, hcs⟩ := hw k hklt
        have hcol : (fun i => u i k) = fun i => w i k := by
          funext i; exact ite_eq_right hkt
        refine ⟨?_, ?_, ?_⟩
        · rw [hcol, hc]
          by_cases hk0 : k.val = 0
          · rw [dite_eq_left hk0, dite_eq_left hk0]
          · rw [dite_eq_right hk0, dite_eq_right hk0]
            funext i
            change w i ⟨k.val - 1, _⟩ =
              if k.val - 1 = t then v i else w i ⟨k.val - 1, _⟩
            rw [ite_eq_right (by omega)]
        · intro i hi
          change (if k.val = t then v i else w i k) = _
          rw [ite_eq_right hkt]
          exact hc0 i hi
        · intro i hi
          change (if k.val = t then v i else w i k) = 0
          rw [ite_eq_right hkt]
          exact hcs i hi
  obtain ⟨w, hw⟩ := build n le_rfl
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j; exact (hw j j.isLt).1
  · intro i j; exact (hw j j.isLt).2.1 i
  · intro i j; exact (hw j j.isLt).2.2 i

private lemma chain_power (α : ℕ → ℝ) (n : ℕ)
    (w : Matrix (Fin n) (Fin n) ℝ) (hw : IsJordanChain α n w)
    (m : ℕ) (j : Fin n) :
    (carleman α n - 1) ^ m *ᵥ (fun i => w i j) =
      if h : m ≤ j.val then fun i => w i ⟨j.val - m, by omega⟩ else 0 := by
  induction m generalizing j with
  | zero => simp only [pow_zero, Matrix.one_mulVec, Nat.zero_le, dite_eq_left,
      Nat.sub_zero]
  | succ m ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hw.1 j]
    by_cases hj : j.val = 0
    · rw [dite_eq_left hj, Matrix.mulVec_zero, dite_eq_right (by omega)]
    · rw [dite_eq_right hj, ih]
      by_cases hm : m + 1 ≤ j.val
      · rw [dite_eq_left (by dsimp only; omega), dite_eq_left hm]
        funext i
        congr 1
        apply Fin.ext
        dsimp only
        omega
      · rw [dite_eq_right (by dsimp only; omega), dite_eq_right hm]

private lemma krylov_inverse (α : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (w : Matrix (Fin n) (Fin n) ℝ) (hw : IsJordanChain α n w) :
    IsUnit w.det ∧ w⁻¹ = fun k j => ((carleman α n - 1) ^ k.val) ⟨0, hn⟩ j := by
  let q : Matrix (Fin n) (Fin n) ℝ :=
    fun k j => ((carleman α n - 1) ^ k.val) ⟨0, hn⟩ j
  have hq : q * w = 1 := by
    ext k j
    change (∑ l, ((carleman α n - 1) ^ k.val) ⟨0, hn⟩ l * w l j) = _
    change ((carleman α n - 1) ^ k.val *ᵥ (fun i => w i j)) ⟨0, hn⟩ = _
    rw [chain_power α n w hw]
    by_cases h : k.val ≤ j.val
    · rw [dite_eq_left h, hw.2.1 _ _ rfl, Matrix.one_apply]
      have he : j.val - k.val = 0 ↔ k = j := by
        constructor
        · intro hh; apply Fin.ext; omega
        · intro hh; subst j; simp
      change (if j.val - k.val = 0 then 1 else 0) = _
      simp only [he]
    · rw [dite_eq_right h, Matrix.one_apply_ne (by intro he; subst j; omega)]
      rfl
  exact ⟨Matrix.isUnit_det_of_left_inverse hq, Matrix.inv_eq_left_inv hq⟩

private lemma path_expansion (α : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (ha : ∀ i j : Fin n, j ≤ i → (carleman α n - 1) i j = 0)
    (m : ℕ) (j : Fin n) :
    ((carleman α n - 1) ^ m) ⟨0, hn⟩ j = sigma α n m j := by
  have hs (r : ℕ) (l : Fin n) : sigma α n r l = sigma._sunfold α n r l := by
    cases r <;> rfl
  rw [hs]
  induction m generalizing j with
  | zero =>
    change (1 : Matrix (Fin n) (Fin n) ℝ) ⟨0, hn⟩ j = if j.val = 0 then 1 else 0
    rw [Matrix.one_apply]
    have he : (⟨0, hn⟩ : Fin n) = j ↔ j.val = 0 := by
      constructor
      · intro h; subst j; rfl
      · intro h; exact Fin.ext h.symm
    simp only [he]
  | succ m ih =>
    rw [pow_succ, Matrix.mul_apply]
    change (∑ i, ((carleman α n - 1) ^ m) ⟨0, hn⟩ i *
      (carleman α n - 1) i j) =
      ∑ i, if i < j then sigma α n m i * carleman α n i j else 0
    apply Finset.sum_congr rfl
    intro i _
    by_cases hij : i < j
    · rw [ite_eq_left hij, ih, ← hs m i]
      change _ * (carleman α n i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j) = _
      rw [Matrix.one_apply_ne (ne_of_lt hij), sub_zero]
    · rw [ite_eq_right hij, ha i j (le_of_not_gt hij), mul_zero]

theorem result : claim := by
  intro α h0 h1 h2 n hn
  obtain ⟨ha, hs⟩ := carleman_structure α n h0 h1
  have hsne : ∀ i j : Fin n, j.val = i.val + 1 →
      (carleman α n - 1) i j ≠ 0 := by
    intro i j hij
    rw [hs i j hij]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i.val)) h2
  refine ⟨chain_exists α n hn ha hsne, ?_⟩
  intro w hw
  obtain ⟨hu, hi⟩ := krylov_inverse α n hn w hw
  refine ⟨hu, ?_⟩
  intro k j _
  rw [hi]
  exact path_expansion α n hn ha k.val j


end

end D5.S3.StatisticalMechanics.CarlemanJordanChainInverse
