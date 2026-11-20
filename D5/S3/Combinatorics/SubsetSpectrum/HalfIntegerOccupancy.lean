/- GID: D5/S3/Combinatorics/SubsetSpectrum/HalfIntegerOccupancy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/HalfIntegerOccupancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity limits and attains integer grid coverage by ternary occupancies of half-integer weights. -/

import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

open Finset

namespace D5.S3.Combinatorics.SubsetSpectrum.HalfIntegerOccupancy

private def wordCode : (h : ℕ) → (Fin h → Fin 3) ≃ Fin (3^h)
  | 0 =>
    { toFun := fun _ => ⟨0, by decide⟩
      invFun := fun _ i => i.elim0
      left_inv := fun _ => funext fun i => i.elim0
      right_inv := fun k => Fin.ext (by have hk : k.val < 1 := k.isLt; omega) }
  | h + 1 =>
    (Fin.consEquiv (fun _ : Fin (h + 1) => Fin 3)).symm.trans <|
    (Equiv.prodComm (Fin 3) (Fin h → Fin 3)).trans <|
    ((wordCode h).prodCongr (Equiv.refl (Fin 3))).trans <|
    finProdFinEquiv.trans (finCongr (pow_succ 3 h).symm)

private theorem wordCode_val_succ {h : ℕ} (f : Fin (h+1) → Fin 3) :
    (wordCode (h+1) f).val = (f 0).val + 3 * (wordCode h (Fin.tail f)).val := rfl

private theorem wordCode_parity (h : ℕ) (f : Fin h → Fin 3) :
    (wordCode h f).val % 2 = (∑ i, (f i).val) % 2 := by
  induction h with
  | zero =>
    simp [wordCode]
  | succ h ih =>
    rw [wordCode_val_succ, Fin.sum_univ_succ]
    have ht := ih (Fin.tail f)
    change (wordCode h (Fin.tail f)).val % 2 = (∑ i, (Fin.tail f i).val) % 2 at ht
    change ((f 0).val + 3*(wordCode h (Fin.tail f)).val) % 2 =
      ((f 0).val + ∑ i, (Fin.tail f i).val) % 2
    omega

private def halfEquiv (N : ℕ) :
    {j : Fin N // j.val % 2 = 0} ≃ Fin ((N + 1) / 2) where
  toFun j := ⟨j.val.val / 2, by have := j.val.isLt; omega⟩
  invFun k := ⟨⟨2*k.val, by have := k.isLt; omega⟩, by change (2*k.val)%2 = 0; omega⟩
  left_inv j := Subtype.ext (Fin.ext (by change 2 * (j.val.val / 2) = j.val.val; have := j.property; omega))
  right_inv k := Fin.ext (by change 2*k.val / 2 = k.val; omega)

private theorem card_even_ternary_words (h : ℕ) :
    Fintype.card {f : Fin h → Fin 3 // (∑ i, (f i).val) % 2 = 0} = (3^h + 1)/2 := by
  classical
  let e : {f : Fin h → Fin 3 // (∑ i, (f i).val) % 2 = 0} ≃
      {j : Fin (3^h) // j.val % 2 = 0} := (wordCode h).subtypeEquiv
    (fun f => by exact (congrArg (fun n : ℕ => n = 0) (wordCode_parity h f)).symm.to_iff)
  simpa using Fintype.card_congr (e.trans (halfEquiv (3^h)))

/-- When h doubled pair weights are odd, integer grid levels use only the even-sum ternary
words on those h pairs. The t remaining pair occupancies can vary freely. -/
theorem mixed_half_weights_bound {h t levels : ℕ}
    (oddTwice : Fin h → ℤ) (integer : Fin t → ℤ)
    (odd : ∀ i, Odd (oddTwice i))
    (x : Fin levels → Fin h → Fin 3) (y : Fin levels → Fin t → Fin 3)
    (calibrated : ∀ k, (∑ i, ((x k i).val : ℤ) * oddTwice i) +
      2 * (∑ i, ((y k i).val : ℤ) * integer i) = 2 * (k.val : ℤ)) :
    levels ≤ ((3^h + 1)/2) * 3^t := by
  classical
  have parity (k : Fin levels) : (∑ i, (x k i).val) % 2 = 0 := by
    have hc := congrArg (fun z : ℤ => (z : ZMod 2)) (calibrated k)
    push_cast at hc
    have ho (i : Fin h) : (oddTwice i : ZMod 2) = 1 := (odd i).intCast_zmod_two
    have twoZero : (2 : ZMod 2) = 0 := by decide
    have sumZero : ((∑ i, (x k i).val : ℕ) : ZMod 2) = 0 := by
      push_cast
      simpa only [ho, mul_one, twoZero, zero_mul, add_zero] using hc
    exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ 2).mp sumZero)
  let code (k : Fin levels) :
      ({f : Fin h → Fin 3 // (∑ i, (f i).val) % 2 = 0} × (Fin t → Fin 3)) :=
    (⟨x k, parity k⟩, y k)
  have inj : Function.Injective code := by
    intro k l same
    have hx : x k = x l := congrArg (fun v => v.1.val) same
    have hy : y k = y l := congrArg Prod.snd same
    have eq := calibrated k
    rw [hx, hy, calibrated l] at eq
    apply Fin.ext
    omega
  simpa [Fintype.card_prod, card_even_ternary_words, Fintype.card_fun] using
    Fintype.card_le_of_injective code inj

private theorem wordCode_weighted (h : ℕ) (f : Fin h → Fin 3) :
    (wordCode h f).val = ∑ i, (f i).val * 3^i.val := by
  induction h with
  | zero => simp [wordCode]
  | succ h ih =>
    rw [wordCode_val_succ, Fin.sum_univ_succ, ih, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, Nat.mul_one]
    apply congrArg ((f 0).val + ·)
    apply Finset.sum_congr rfl
    intro i _
    change 3 * ((f i.succ).val * 3^i.val) = (f i.succ).val * 3^(i.val+1)
    rw [pow_succ]
    ac_rfl

/-- The count bound is attained by odd doubled weights in powers of three and integer
weights starting one unit beyond the range covered by the half-integer weights. -/
private theorem mixed_half_weights_attain (h t : ℕ) :
    ∀ k < ((3^h + 1)/2)*3^t,
      ∃ (x : Fin h → Fin 3) (y : Fin t → Fin 3),
        (∑ i, (x i).val * 3^i.val) +
          2 * (∑ i, (y i).val * (((3^h + 1)/2)*3^i.val)) = 2*k := by
  intro k hk
  let width := (3^h + 1)/2
  have powPos : 0 < 3^h := pow_pos (by decide) _
  have widthPos : 0 < width := by dsimp [width]; omega
  have restBound : 2*(k % width) < 3^h := by
    have rep := Nat.mod_lt k widthPos
    dsimp [width] at rep ⊢
    omega
  have quotientBound : k / width < 3^t := by
    apply (Nat.div_lt_iff_lt_mul widthPos).mpr
    simpa only [Nat.mul_comm] using hk
  let x := (wordCode h).symm ⟨2*(k % width), restBound⟩
  let y := (wordCode t).symm ⟨k/width, quotientBound⟩
  refine ⟨x, y, ?_⟩
  have hx : ∑ i, (x i).val * 3^i.val = 2*(k % width) := by
    rw [← wordCode_weighted]
    simp [x]
  have hy : ∑ i, (y i).val * 3^i.val = k/width := by
    rw [← wordCode_weighted]
    simp [y]
  have hFactor : (∑ i, (y i).val * (((3^h + 1)/2)*3^i.val)) =
      width * (∑ i, (y i).val * 3^i.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [width]
    ac_rfl
  rw [hx, hFactor, hy, ← Nat.mul_add]
  exact congrArg (2 * ·) (Nat.mod_add_div k width)

private theorem sum_powers (h : ℕ) :
    (∑ i : Fin h, 3^i.val) * 2 + 1 = 3^h := by
  rw [Fin.sum_univ_eq_sum_range]
  exact geom_sum_mul_add (R := ℕ) 2 h

private theorem mixed_normalized_denominator (h t : ℕ) (even : Even h) :
    let width := (3^h + 1)/2
    let total := (∑ i : Fin h, 3^i.val) + 2*(∑ i : Fin t, width*3^i.val)
    total + 1 = width*3^t ∧ Even total := by
  dsimp only
  let width := (3^h + 1)/2
  let halfMass := ∑ i : Fin h, 3^i.val
  let integerMass := ∑ i : Fin t, 3^i.val
  have hp := sum_powers h
  have ht := sum_powers t
  change halfMass * 2 + 1 = 3^h at hp
  change integerMass * 2 + 1 = 3^t at ht
  have hw : width = halfMass + 1 := by dsimp only [width]; omega
  rw [← Finset.mul_sum]
  change halfMass + 2*(width*integerMass) + 1 = width*3^t ∧
    Even (halfMass + 2*(width*integerMass))
  constructor
  · rw [← ht, Nat.mul_add, Nat.mul_one, hw]
    ring
  · have h3 : (3 : ZMod 2) = 1 := by decide
    have castHalf : (halfMass : ZMod 2) = 0 := by
      dsimp only [halfMass]
      push_cast
      simp [h3, even.natCast_zmod_two]
    apply ZMod.natCast_eq_zero_iff_even.mp
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [castHalf, h2]

/-- The count bound is attained by an integer grid when the number of half-integer pairs
is even. The doubled half-integer weights and integer weights are specified explicitly. -/
theorem mixed_half_weights_sharp (h t : ℕ) (even : Even h) :
    let width := (3 ^ h + 1) / 2
    let total := (∑ i : Fin h, 3 ^ i.val) + 2 * (∑ i : Fin t, width * 3 ^ i.val)
    total + 1 = width * 3 ^ t ∧ Even total ∧
      ∀ k ≤ total, ∃ (x : Fin h → Fin 3) (y : Fin t → Fin 3),
        (∑ i, (x i).val * 3 ^ i.val) +
          2 * (∑ i, (y i).val * (width * 3 ^ i.val)) = 2 * k := by
  dsimp only
  obtain ⟨htotal, hevenTotal⟩ := mixed_normalized_denominator h t even
  refine ⟨htotal, hevenTotal, fun k hk => ?_⟩
  exact mixed_half_weights_attain h t k (htotal ▸ Nat.lt_succ_of_le hk)

end D5.S3.Combinatorics.SubsetSpectrum.HalfIntegerOccupancy
