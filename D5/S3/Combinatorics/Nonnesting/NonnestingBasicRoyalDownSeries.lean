/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownSeries
   mirror-E: none(waiver:royal-downstep-series)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Derives the weighted-downstep Dyck generating-function equation. -/
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownCount
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownSeries

open DyckStep NonnestingBasicRoyalDownRuns PowerSeries NonnestingBasicRoyalDownCount

theorem downSeries_quadratic :
    let downSeries : PowerSeries ℤ :=
      PowerSeries.mk fun n => (downWeight n : ℤ)
    1 - (1 + X) * downSeries + 2 * X * downSeries ^ 2 = 0 := by
  classical
  let SplitPairs (n : ℕ) : Type :=
    {uv : DyckWord × DyckWord // uv.1.semilength + uv.2.semilength = n}
  let downSeries : PowerSeries ℤ :=
    PowerSeries.mk fun n => (downWeight n : ℤ)
  letI (n : ℕ) : Fintype (SplitPairs n) := by
    let T := Σ i : Fin (n + 1),
      {u : DyckWord // u.semilength = i.val} ×
        {v : DyckWord // v.semilength = n - i.val}
    let f : SplitPairs n → T := fun x => by
      have hi : x.1.1.semilength < n + 1 := by
        have h := x.2; omega
      exact ⟨⟨x.1.1.semilength, hi⟩,
        ⟨⟨x.1.1, rfl⟩, ⟨x.1.2, by
          change x.1.2.semilength = n - x.1.1.semilength; have h := x.2
          omega⟩⟩⟩
    have hf : Function.Injective f := by
      intro x y h; apply Subtype.ext; apply Prod.ext
      · exact congrArg (fun z : T => z.2.1.1) h
      · exact congrArg (fun z : T => z.2.2.1) h
    letI : Finite (SplitPairs n) := Finite.of_injective f hf
    exact Fintype.ofFinite (SplitPairs n)
  have downPairs_append (s t : List DyckStep) :
      downPairs (s ++ t) = downPairs s + downPairs t +
        if s.getLast? = some D ∧ t.head? = some D then 1 else 0 := by
    induction s with
    | nil => simp [downPairs]
    | cons a s ih =>
      cases s with
      | nil =>
        cases t with
        | nil => cases a <;> simp [downPairs]
        | cons b t =>
          cases a <;> cases b <;> simp [downPairs] <;> omega
      | cons b s =>
        change (if a = D ∧ b = D then 1 else 0) + downPairs ((b :: s) ++ t) =
          ((if a = D ∧ b = D then 1 else 0) + downPairs (b :: s)) + downPairs t +
            if (a :: b :: s).getLast? = some D ∧ t.head? = some D then 1 else 0
        rw [ih]; have hlast : (a :: b :: s).getLast? = (b :: s).getLast? := rfl; rw [hlast]; omega
  have downPairs_dyck_add (p q : DyckWord) :
      downPairs (p + q).toList = downPairs p.toList + downPairs q.toList := by
    rw [show (p + q).toList = p.toList ++ q.toList from rfl, downPairs_append]
    by_cases hp : p = 0
    · subst p
      simp [show (0 : DyckWord).toList = [] from rfl, downPairs]
    by_cases hq : q = 0
    · subst q
      simp [show (0 : DyckWord).toList = [] from rfl, downPairs]
    have hhead : q.toList.head? = some U := by
      rw [List.head?_eq_some_head (DyckWord.toList_ne_nil.mpr hq)]
      exact congrArg some (DyckWord.head_eq_U q (DyckWord.toList_ne_nil.mpr hq))
    simp [hhead]
  have downPairs_nest (p : DyckWord) :
      downPairs p.nest.toList = downPairs p.toList + if p = 0 then 0 else 1 := by
    rw [show p.nest.toList = [U] ++ p.toList ++ [D] from rfl]
    by_cases hp : p = 0
    · subst p
      simp [show (0 : DyckWord).toList = [] from rfl, downPairs]
    have hfirst : downPairs (U :: (p.toList ++ [D])) =
        downPairs (p.toList ++ [D]) := by
      cases hlist : p.toList with
      | nil => exact False.elim ((DyckWord.toList_ne_nil.mpr hp) hlist)
      | cons s t =>
        have hs : s = U := by
          simpa [hlist] using
            (DyckWord.head_eq_U p (DyckWord.toList_ne_nil.mpr hp))
        subst s; simp [downPairs]
    rw [show [U] ++ p.toList ++ [D] = U :: (p.toList ++ [D]) from rfl, hfirst]
    rw [downPairs_append]
    have hlast : p.toList.getLast? = some D := by
      rw [List.getLast?_eq_getLast_of_ne_nil (DyckWord.toList_ne_nil.mpr hp)]
      exact congrArg some (DyckWord.getLast_eq_D p (DyckWord.toList_ne_nil.mpr hp))
    simp [downPairs, hlast, hp]
  have downWeight_first_return (n : ℕ) :
      downWeight (n + 1) =
        ∑ x : SplitPairs n,
          (if x.1.1 = 0 then 1 else 2) *
            2 ^ downPairs x.1.1.toList * 2 ^ downPairs x.1.2.toList := by
    let S := {p : DyckWord // p.semilength = n + 1}; let e : S ≃ SplitPairs n :=
      { toFun := fun p => by
          have hp : p.1 ≠ 0 := by
            intro h; have hn := p.2; simp [h] at hn
          have hlen := p.1.semilength_insidePart_add_semilength_outsidePart_add_one hp
          exact ⟨(p.1.insidePart, p.1.outsidePart), by
            change p.1.insidePart.semilength + p.1.outsidePart.semilength = n; rw [p.2] at hlen
            omega⟩
        invFun := fun x =>
          ⟨x.1.1.nest + x.1.2, by
            simp only [DyckWord.semilength_add, DyckWord.semilength_nest]; have h := x.2
            omega⟩
        left_inv := by
          intro p; apply Subtype.ext
          have hp : p.1 ≠ 0 := by
            intro h; have hn := p.2; simp [h] at hn
          exact p.1.nest_insidePart_add_outsidePart hp
        right_inv := by
          intro x; apply Subtype.ext
          apply Prod.ext <;> (simp) }
    change (∑ p : S, 2 ^ downPairs p.1.toList) = _
    rw [← Equiv.sum_comp e.symm (fun p : S => 2 ^ downPairs p.1.toList)]; apply Fintype.sum_congr
    intro x; change 2 ^ downPairs (x.1.1.nest + x.1.2).toList = _
    rw [downPairs_dyck_add, downPairs_nest, pow_add]
    by_cases h : x.1.1 = 0
    · simp [h]
    · simp [h, pow_succ] <;> ac_rfl
  have downWeight_convolution (n : ℕ) :
      downWeight (n + 1) =
        ∑ i : Fin (n + 1), (if i.val = 0 then 1 else 2) *
          downWeight i.val * downWeight (n - i.val) := by
    let f : SplitPairs n → Fin (n + 1) := fun x =>
      ⟨x.1.1.semilength, by have h := x.2; omega⟩
    let fiber (i : Fin (n + 1)) := {x : SplitPairs n // f x = i}
    letI (i : Fin (n + 1)) : Fintype (fiber i) := Fintype.ofFinite (fiber i)
    let weight : SplitPairs n → ℕ := fun x =>
      (if x.1.1 = 0 then 1 else 2) *
        2 ^ downPairs x.1.1.toList * 2 ^ downPairs x.1.2.toList
    have hzero (p : DyckWord) : p = 0 ↔ p.semilength = 0 := by
      constructor
      · intro h
        simp [h]
      · intro h
        have hl := p.two_mul_semilength_eq_length
        rw [h] at hl; apply DyckWord.toList_eq_nil.mp; exact List.length_eq_zero_iff.mp (by omega)
    have hfiber (i : Fin (n + 1)) :
        (∑ x : fiber i, weight x.1) =
          (if i.val = 0 then 1 else 2) *
            downWeight i.val * downWeight (n - i.val) := by
      let U := {u : DyckWord // u.semilength = i.val}
      let V := {v : DyckWord // v.semilength = n - i.val}; let e : fiber i ≃ U × V :=
        { toFun := fun x =>
            (⟨x.1.1.1, by
              have h := congrArg Fin.val x.2
              exact h⟩,
              ⟨x.1.1.2, by
                have h := congrArg Fin.val x.2; change x.1.1.1.semilength = i.val at h
                have hs := x.1.2; change x.1.1.1.semilength + x.1.1.2.semilength = n at hs
                omega⟩)
          invFun := fun uv =>
            ⟨⟨(uv.1.1, uv.2.1), by
              change uv.1.1.semilength + uv.2.1.semilength = n; have hu := uv.1.2; have hv := uv.2.2
              omega⟩, by
              apply Fin.ext; exact uv.1.2⟩
          left_inv := by
            intro x; apply Subtype.ext; apply Subtype.ext; rfl
          right_inv := by
            intro uv
            apply Prod.ext <;> apply Subtype.ext <;> rfl }
      rw [← Equiv.sum_comp e.symm (fun x : fiber i => weight x.1)]
      change (∑ uv : U × V,
        (if uv.1.1 = 0 then 1 else 2) *
          2 ^ downPairs uv.1.1.toList * 2 ^ downPairs uv.2.1.toList) = _
      rw [Fintype.sum_prod_type]
      have hiff (u : U) : u.1 = 0 ↔ i.val = 0 := by
        rw [hzero u.1, u.2]
      simp_rw [hiff]
      simp only [downWeight, Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
    rw [downWeight_first_return]; change (∑ x : SplitPairs n, weight x) = _
    rw [← Equiv.sum_comp (Equiv.sigmaFiberEquiv f)
      (fun x : SplitPairs n => weight x)]
    rw [Fintype.sum_sigma]; exact Fintype.sum_congr _ _ hfiber
  let A : PowerSeries ℤ := downSeries
  have h0 : downWeight 0 = 1 := by
    haveI : Unique {p : DyckWord // p.semilength = 0} :=
      ⟨⟨0, rfl⟩, by
        intro p; apply Subtype.ext; have hl := p.1.two_mul_semilength_eq_length
        rw [p.2] at hl; apply DyckWord.toList_eq_nil.mp
        exact List.length_eq_zero_iff.mp (by omega)⟩
    have hd : (default : {p : DyckWord // p.semilength = 0}).1 = 0 := by
      have h := Subsingleton.elim
        (default : {p : DyckWord // p.semilength = 0})
        (⟨0, rfl⟩ : {p : DyckWord // p.semilength = 0})
      exact congrArg Subtype.val h
    simp [downWeight, hd, downPairs]
  have hconv (k : ℕ) :
      coeff k (A * A) =
        ∑ i : Fin (k + 1),
          (downWeight i.val : ℤ) * (downWeight (k - i.val) : ℤ) := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_fin_eq_sum_range]; apply Finset.sum_congr rfl; intro i hi
    simp [Finset.mem_range.mp hi, A, downSeries]
  have hrec (k : ℕ) :
      (downWeight (k + 1) : ℤ) =
        2 * coeff k (A * A) - (downWeight k : ℤ) := by
    have hnat := downWeight_convolution k; have hz : (downWeight (k + 1) : ℤ) =
        ∑ i : Fin (k + 1), (if i.val = 0 then (1 : ℤ) else 2) *
          (downWeight i.val : ℤ) * (downWeight (k - i.val) : ℤ) := by
      exact_mod_cast hnat
    rw [hz, hconv]; rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ]; rw [h0]; simp only [Nat.cast_one, one_mul]
    have hne (i : Fin k) : i.val + 1 ≠ 0 := by omega
    simp only [if_true]; simp
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]; ring
  have hpoly : 1 - (1 + X) * A + 2 * X * A ^ 2 =
      1 - A - X ^ 1 * A + X ^ 1 * (A * A) + X ^ 1 * (A * A) := by ring
  change 1 - (1 + X) * A + 2 * X * A ^ 2 = 0; rw [hpoly]; apply PowerSeries.ext; intro n
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one,
    map_zero]
  by_cases hn : n = 0
  · subst n
    simp [A, downSeries, h0]
  have hpos : 1 ≤ n := by omega
  have hrec' := hrec (n - 1)
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at hrec'
  have hcoeff (m : ℕ) : coeff m A = (downWeight m : ℤ) := by
    simp [A, downSeries]
  simp only [if_pos hpos, if_neg hn, hcoeff, zero_sub]; rw [hrec']; ring
end D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownSeries

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingBasicRoyalDownSeries.downSeries_quadratic
