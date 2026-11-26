/- GID: D5/S3/Analytic/Probability/BernoulliParityFamilyMoments
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/BernoulliParityFamilyMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fair rank and disjoint biased supports characterize joint independence of affine parities. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Structural factorization of the moments of a finite family of binary parity rows. -/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace D5.S3.Analytic.Probability.BernoulliParityFamilyMoments

variable {I J : Type*} [Fintype J]

/-- The product of the coordinate biases on the support of a parity row. -/
private noncomputable def moment (q : J → ℝ) (r : J → ZMod 2) : ℝ :=
  ∏ j, if r j = 0 then 1 else q j

private theorem moment_eq_zero_iff (q : J → ℝ) (r : J → ZMod 2) :
    moment q r = 0 ↔ ∃ j : {j // q j = 0}, r j.val ≠ 0 := by
  simp only [moment, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hr : r j = 0
    · simp [hr] at hj
    · exact ⟨⟨j, by simpa [hr] using hj⟩, hr⟩
  · rintro ⟨j, hj⟩
    exact ⟨j.val, by simp [hj, j.property]⟩

private theorem zmodTwo_eq_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  ((by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a).resolve_left ha

private theorem linearIndependent_iff_nonempty_sum_ne_zero
    {T M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (v : T → M) :
    LinearIndependent (ZMod 2) v ↔
      ∀ S : Finset T, S.Nonempty → (∑ i ∈ S, v i) ≠ 0 := by
  rw [linearIndependent_iff']
  constructor
  · intro h S ⟨i, hi⟩ hsum
    exact one_ne_zero (h S (fun _ => 1) (by simpa using hsum) i hi)
  · classical
    intro h S c hsum i hi
    by_contra hc
    have hfiltered : (∑ j ∈ S.filter (fun j => c j ≠ 0), v j) =
        ∑ j ∈ S, c j • v j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : c j = 0
      · simp [hj]
      · simp [zmodTwo_eq_one hj]
    exact h _ ⟨i, Finset.mem_filter.mpr ⟨hi, hc⟩⟩ (hfiltered.trans hsum)

private theorem moment_mul_lt_moment_add_of_overlap
    (q : J → ℝ) (hq₀ : ∀ k, 0 ≤ q k) (hq₁ : ∀ k, q k < 1)
    (r s : J → ZMod 2)
    (hr : ¬∃ k : {k // q k = 0}, r k.val ≠ 0)
    (hs : ¬∃ k : {k // q k = 0}, s k.val ≠ 0)
    {k : J} (hrk : r k ≠ 0) (hsk : s k ≠ 0) :
    moment q r * moment q s < moment q (r + s) := by
  let weight (a : ZMod 2) (j : J) : ℝ := if a = 0 then 1 else q j
  have weight_pos (t : J → ZMod 2)
      (ht : ¬∃ j : {j // q j = 0}, t j.val ≠ 0) (j : J) :
      0 < weight (t j) j := by
    by_cases hz : t j = 0
    · simp [weight, hz]
    · rw [show weight (t j) j = q j by simp [weight, hz]]
      exact lt_of_le_of_ne (hq₀ j) (fun h => ht ⟨⟨j, h.symm⟩, hz⟩)
  have column_lt (j : J) (hrj : r j ≠ 0) (hsj : s j ≠ 0) :
      weight (r j) j * weight (s j) j < weight (r j + s j) j := by
    have hpos : 0 < q j := by simpa [weight, hrj] using weight_pos r hr j
    have hcancel : r j + s j = 0 := by
      rw [zmodTwo_eq_one hrj, zmodTwo_eq_one hsj, ZModModule.add_self]
    simp only [weight, hrj, hsj, hcancel, ite_false, ite_true]
    calc
      q j * q j < 1 * q j := mul_lt_mul_of_pos_right (hq₁ j) hpos
      _ < 1 := by simpa using hq₁ j
  change (∏ j, weight (r j) j) * (∏ j, weight (s j) j) < ∏ j, weight (r j + s j) j
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_lt_prod₀ (fun j _ => mul_pos (weight_pos r hr j) (weight_pos s hs j))
    (fun j _ => ?_) ⟨k, Finset.mem_univ k, column_lt k hrk hsk⟩
  by_cases hrj : r j = 0
  · simp [weight, hrj]
  by_cases hsj : s j = 0
  · simp [weight, hsj]
  exact (column_lt j hrj hsj).le

private theorem moment_sum_of_disjoint (q : J → ℝ) (rows : I → J → ZMod 2) (S : Finset I)
    (h : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ k, rows i k = 0 ∨ rows j k = 0) :
    moment q (∑ i ∈ S, rows i) = ∏ i ∈ S, moment q (rows i) := by
  simp only [moment, Finset.sum_apply]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hactive : ∃ i ∈ S, rows i k ≠ 0
  · obtain ⟨i, hi, hik⟩ := hactive
    have hzero (j : I) (hj : j ∈ S) (hji : j ≠ i) : rows j k = 0 :=
      (h j hj i hi hji k).resolve_right hik
    rw [Finset.sum_eq_single_of_mem i hi hzero,
      Finset.prod_eq_single_of_mem i hi (fun j hj hji => by simp [hzero j hj hji])]
  · have hzero (i : I) (hi : i ∈ S) : rows i k = 0 :=
      not_ne_iff.mp (fun hik => hactive ⟨i, hi, hik⟩)
    rw [Finset.sum_eq_zero hzero, ite_eq_left rfl]
    exact (Finset.prod_eq_one fun i hi => ite_eq_left (hzero i hi)).symm

set_option linter.unusedFintypeInType false in
/-- All subset moments factor exactly when the fair restrictions of the rows that hit fair
coordinates are linearly independent and the other rows have pairwise disjoint supports. -/
private theorem moment_factorization_iff [Fintype I] (q : J → ℝ)
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (rows : I → J → ZMod 2) :
    let fair := {j : J // q j = 0}
    let hits (i : I) := ∃ j : fair, rows i j.val ≠ 0
    let touched := {i : I // hits i}
    (∀ S : Finset I, moment q (∑ i ∈ S, rows i) = ∏ i ∈ S, moment q (rows i)) ↔
      (LinearIndependent (ZMod 2) (fun (i : touched) (j : fair) => rows i.val j.val) ∧
        ∀ i j, i ≠ j → ¬hits i → ¬hits j → ∀ k, rows i k = 0 ∨ rows j k = 0) := by
  classical
  dsimp only
  let fair := {j : J // q j = 0}
  let hits (i : I) := ∃ j : fair, rows i j.val ≠ 0
  let touched := {i : I // hits i}
  let restrict (i : touched) (j : fair) := rows i.val j.val
  change _ ↔ LinearIndependent (ZMod 2) restrict ∧
    ∀ i j, i ≠ j → ¬hits i → ¬hits j → ∀ k, rows i k = 0 ∨ rows j k = 0
  rw [linearIndependent_iff_nonempty_sum_ne_zero]
  have product_zero {S : Finset I} {i : I} (hi : i ∈ S) (hh : hits i) :
      (∏ i ∈ S, moment q (rows i)) = 0 :=
    Finset.prod_eq_zero hi ((moment_eq_zero_iff q (rows i)).2 hh)
  constructor
  · intro h
    constructor
    · intro T ⟨i, hi⟩
      let S := T.map (Function.Embedding.subtype hits)
      have hiS : i.val ∈ S := Finset.mem_map.mpr ⟨i, hi, rfl⟩
      have hz : moment q (∑ a ∈ S, rows a) = 0 := (h S).trans (product_zero hiS i.property)
      obtain ⟨k, hk⟩ := (moment_eq_zero_iff q _).1 hz
      intro hsum
      apply hk
      have hcoord := congrFun hsum k
      simpa [S, restrict, Finset.sum_map] using hcoord
    · intro i j hij hi hj k
      by_contra hoverlap
      rw [not_or] at hoverlap
      have hlt := moment_mul_lt_moment_add_of_overlap q hq₀ hq₁
        (rows i) (rows j) hi hj hoverlap.1 hoverlap.2
      have hpair : moment q (rows i + rows j) = moment q (rows i) * moment q (rows j) := by
        simpa [Finset.sum_insert, Finset.prod_insert, hij] using h {i, j}
      exact hlt.ne hpair.symm
  · rintro ⟨hind, hdisjoint⟩ S
    by_cases ht : ∃ i ∈ S, hits i
    · obtain ⟨i, hi, hhit⟩ := ht
      rw [product_zero hi hhit, moment_eq_zero_iff]
      let T := S.subtype hits
      have hT : T.Nonempty := ⟨⟨i, hhit⟩, Finset.mem_subtype.mpr hi⟩
      by_contra hzero
      apply hind T hT
      funext k
      have hz : (∑ a ∈ S, rows a) k.val = 0 :=
        not_ne_iff.mp (fun hk => hzero ⟨k, hk⟩)
      have hfilter : (∑ a ∈ S.filter hits, rows a k.val) = ∑ a ∈ S, rows a k.val := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : hits a
        · exact ite_eq_left ha
        · rw [ite_eq_right ha]
          exact (not_ne_iff.mp (fun hk => ha ⟨k, hk⟩)).symm
      calc
        (∑ a ∈ T, restrict a) k = ∑ a ∈ S.filter hits, rows a k.val := by
          simp only [Finset.sum_apply]
          rw [← Finset.subtype_map hits, Finset.sum_map]
          rfl
        _ = 0 := hfilter.trans (by simpa only [Finset.sum_apply] using hz)
    · apply moment_sum_of_disjoint q rows S
      intro i hi j hj hij
      exact hdisjoint i j hij (fun hh => ht ⟨i, hi, hh⟩) (fun hh => ht ⟨j, hj, hh⟩)
private def bitSign (b : Bool) : ℝ := if b then -1 else 1

open Classical in
private theorem sign_moments_determine_law {I : Type*} [Fintype I]
    (μ ν : (I → Bool) → ℝ)
    (h : ∀ S : Finset I,
      (∑ x, μ x * ∏ i ∈ S, bitSign (x i)) = ∑ x, ν x * ∏ i ∈ S, bitSign (x i)) :
    μ = ν := by
  have hkernel (x v : I → Bool) :
      (∏ i, (1 + bitSign (v i) * bitSign (x i))) =
        if x = v then (2 : ℝ) ^ Fintype.card I else 0 := by
    by_cases heq : x = v
    · subst x
      rw [ite_eq_left rfl]
      have hs (i : I) : 1 + bitSign (v i) * bitSign (v i) = 2 := by
        cases v i <;> norm_num [bitSign]
      simp_rw [hs, Finset.prod_const, Finset.card_univ]
    · rw [ite_eq_right heq]
      obtain ⟨i, hi⟩ := not_forall.mp (fun hv => heq (funext hv))
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      cases hx : x i <;> cases hv : v i <;> simp_all [bitSign]
  have expand (m : (I → Bool) → ℝ) (v : I → Bool) :
      (∑ x, m x * ∏ i, (1 + bitSign (v i) * bitSign (x i))) =
        ∑ S : Finset I, (∏ i ∈ S, bitSign (v i)) *
          (∑ x, m x * ∏ i ∈ S, bitSign (x i)) := by
    simp_rw [Finset.prod_one_add, Finset.powerset_univ, Finset.prod_mul_distrib,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_congr rfl
    intro x _
    ring
  funext v
  have heq :
      (∑ x, μ x * ∏ i, (1 + bitSign (v i) * bitSign (x i))) =
        ∑ x, ν x * ∏ i, (1 + bitSign (v i) * bitSign (x i)) := by
    rw [expand μ v, expand ν v]
    simp_rw [h]
  simp only [hkernel, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at heq
  exact (mul_right_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))) heq

open Classical in
private theorem sum_mass_mul_readout {Y V : Type*} [Fintype Y] [Fintype V] [DecidableEq V]
    (w : Y → ℝ) (read : Y → V) (f : V → ℝ) :
    (∑ x, w x * f (read x)) =
      ∑ v, (∑ x ∈ Finset.univ.filter (fun x => read x = v), w x) * f v := by
  calc
    _ = ∑ v, ∑ x ∈ Finset.univ.filter (fun x => read x = v), w x * f (read x) :=
      (Finset.sum_fiberwise Finset.univ read _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]

open Classical in
private theorem joint_mass_factors_iff_mixed_moments {Y I : Type*} [Fintype Y] [Fintype I]
    (w : Y → ℝ) (z : Y → I → Bool) (hnorm : ∑ x, w x = 1) :
    let μ (u : I → Bool) := ∑ x ∈ Finset.univ.filter (fun x => z x = u), w x
    let m (i : I) (b : Bool) := ∑ x ∈ Finset.univ.filter (fun x => z x i = b), w x
    (∀ u, μ u = ∏ i, m i (u i)) ↔
      ∀ S : Finset I,
        (∑ x, w x * ∏ i ∈ S, bitSign (z x i)) =
          ∏ i ∈ S, (∑ x, w x * bitSign (z x i)) := by
  intro μ m
  let ν (u : I → Bool) := ∏ i, m i (u i)
  have hμ (S : Finset I) :
      (∑ x, w x * ∏ i ∈ S, bitSign (z x i)) =
        ∑ u, μ u * ∏ i ∈ S, bitSign (u i) :=
    sum_mass_mul_readout w z (fun u => ∏ i ∈ S, bitSign (u i))
  have hm (i : I) :
      (∑ b : Bool, m i b * bitSign b) = ∑ x, w x * bitSign (z x i) :=
    (sum_mass_mul_readout w (fun x => z x i) bitSign).symm
  have htotal (i : I) : ∑ b : Bool, m i b = 1 := by
    change (∑ b : Bool, ∑ x ∈ Finset.univ.filter (fun x => z x i = b), w x) = 1
    rw [Finset.sum_fiberwise, hnorm]
  have hν (S : Finset I) :
      (∑ u, ν u * ∏ i ∈ S, bitSign (u i)) =
        ∏ i ∈ S, (∑ x, w x * bitSign (z x i)) := by
    have hf (u : I → Bool) :
        (∏ i ∈ S, bitSign (u i)) = ∏ i, if i ∈ S then bitSign (u i) else 1 := by
      rw [← Finset.prod_filter]
      simp
    change (∑ u : I → Bool, (∏ i, m i (u i)) * ∏ i ∈ S, bitSign (u i)) = _
    simp_rw [hf, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun i (b : Bool) => m i b * (if i ∈ S then bitSign b else 1))]
    have hlocal (i : I) :
        (∑ b : Bool, m i b * (if i ∈ S then bitSign b else 1)) =
          if i ∈ S then (∑ x, w x * bitSign (z x i)) else 1 := by
      by_cases hi : i ∈ S
      · simpa only [ite_eq_left hi] using hm i
      · simpa only [ite_eq_right hi, mul_one] using htotal i
    simp_rw [hlocal, ← Finset.prod_filter]
    simp
  constructor
  · intro hj S
    rw [hμ, ← hν]
    exact Finset.sum_congr rfl fun u _ =>
      congrArg (fun mass => mass * ∏ i ∈ S, bitSign (u i)) (hj u)
  · intro hmom
    have heq : μ = ν := by
      apply sign_moments_determine_law
      intro S
      rw [← hμ S, hν S]
      exact hmom S
    exact congrFun heq

private abbrev binarySign : AddChar (ZMod 2) ℝ :=
  AddChar.zmodChar 2 (ζ := (-1 : ℝ)) (by simp)

private def bitValue (b : Bool) : ZMod 2 := if b then 1 else 0

private def bernoulliMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

private theorem binarySign_one : binarySign (1 : ZMod 2) = -1 := by
  have hval : (1 : ZMod 2).val = 1 := rfl
  norm_num [binarySign, AddChar.zmodChar_apply, hval]

private theorem bitSign_parity (a : ZMod 2) :
    bitSign (decide (a = 1)) = binarySign a := by
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) a with rfl | rfl
  · norm_num [bitSign]
  · simp [bitSign, binarySign_one]

private theorem binarySign_sum {α : Type*} (s : Finset α) (r : α → ZMod 2) :
    binarySign (∑ i ∈ s, r i) = ∏ i ∈ s, binarySign (r i) := by
  change (binarySign.toAddMonoidHom (∑ i ∈ s, r i)).toMul =
    ∏ i ∈ s, (binarySign.toAddMonoidHom (r i)).toMul
  rw [map_sum, toMul_sum]

open Classical in
private theorem expected_parity_sign {V : Type*} [Fintype V]
    (p : V → ℝ) (r : V → ZMod 2) :
    (∑ x : V → Bool, (∏ j, bernoulliMass (p j) (x j)) *
      binarySign (r ⬝ᵥ fun j => bitValue (x j))) =
    moment (fun j => 1 - 2 * p j) r := by
  have hchar (x : V → Bool) :
      binarySign (r ⬝ᵥ fun j => bitValue (x j)) =
        ∏ j, binarySign (r j * bitValue (x j)) :=
    binarySign_sum Finset.univ _
  simp_rw [hchar, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j (b : Bool) =>
    bernoulliMass (p j) b * binarySign (r j * bitValue b))]
  refine Finset.prod_congr rfl fun j _ => ?_
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [huniv]
  rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (r j) with h | h <;>
    simp [h, bernoulliMass, bitValue, binarySign_one] <;> ring

open Classical in
/-- A finite family of affine parity outputs on independent Bernoulli inputs
is jointly independent exactly when the nonzero restrictions to fair inputs
are linearly independent and the other supports are pairwise disjoint. -/
theorem bernoulli_parity_family_independent_iff {U V : Type*} [Fintype U] [Fintype V]
    (p : V → ℝ) (rows : U → V → ZMod 2) (offset : U → ZMod 2)
    (hp : ∀ j, 0 < p j ∧ p j ≤ 1 / 2) :
    let q (j : V) := 1 - 2 * p j
    let fair := {j : V // q j = 0}
    let hits (i : U) := ∃ j : fair, rows i j.val ≠ 0
    let touched := {i : U // hits i}
    let w (x : V → Bool) := ∏ j, bernoulliMass (p j) (x j)
    let z (x : V → Bool) (i : U) :=
      decide (offset i + (rows i ⬝ᵥ fun j => bitValue (x j)) = 1)
    let μ (u : U → Bool) := ∑ x ∈ Finset.univ.filter (fun x => z x = u), w x
    let m (i : U) (b : Bool) := ∑ x ∈ Finset.univ.filter (fun x => z x i = b), w x
    (∀ u, μ u = ∏ i, m i (u i)) ↔
      (LinearIndependent (ZMod 2) (fun (i : touched) (j : fair) => rows i.val j.val) ∧
        ∀ i j, i ≠ j → ¬hits i → ¬hits j → ∀ k, rows i k = 0 ∨ rows j k = 0) := by
  intro q fair hits touched w z μ m
  have hnorm : ∑ x, w x = 1 := by
    change (∑ x : V → Bool, ∏ j, bernoulliMass (p j) (x j)) = 1
    rw [← Fintype.prod_sum (fun j => bernoulliMass (p j))]
    have hcoord (j : V) : (∑ b : Bool, bernoulliMass (p j) b) = 1 := by
      have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
      rw [huniv]
      simp [bernoulliMass]
    simp only [hcoord, Finset.prod_const_one]
  have hq₀ (j : V) : 0 ≤ q j := by
    dsimp [q]
    linarith [(hp j).2]
  have hq₁ (j : V) : q j < 1 := by
    dsimp [q]
    linarith [(hp j).1]
  have hmom := joint_mass_factors_iff_mixed_moments w z hnorm
  have hstruct := moment_factorization_iff q hq₀ hq₁ rows
  dsimp only at hmom
  dsimp only at hstruct
  rw [hmom, ← hstruct]
  have hmix (S : Finset U) :
      (∑ x, w x * ∏ i ∈ S, bitSign (z x i)) =
        (∏ i ∈ S, binarySign (offset i)) * moment q (∑ i ∈ S, rows i) := by
    calc
      _ = ∑ x, (∏ i ∈ S, binarySign (offset i)) *
          (w x * binarySign ((∑ i ∈ S, rows i) ⬝ᵥ fun j => bitValue (x j))) := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [z, bitSign_parity, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]
        rw [sum_dotProduct, binarySign_sum]
        ring
      _ = _ := by
        rw [← Finset.mul_sum]
        exact congrArg (fun v => (∏ i ∈ S, binarySign (offset i)) * v)
          (expected_parity_sign p (∑ i ∈ S, rows i))
  have hone (i : U) : (∑ x, w x * bitSign (z x i)) =
      binarySign (offset i) * moment q (rows i) := by
    simpa using hmix {i}
  have hfactor (S : Finset U) : (∏ i ∈ S, binarySign (offset i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (offset i) with h | h <;>
      simp [h, binarySign_one]
  simp only [hmix, hone, Finset.prod_mul_distrib]
  exact forall_congr' fun S => mul_right_inj' (hfactor S)

end D5.S3.Analytic.Probability.BernoulliParityFamilyMoments
