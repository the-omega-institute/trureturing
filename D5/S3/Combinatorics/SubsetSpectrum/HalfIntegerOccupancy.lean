/- GID: D5/S3/Combinatorics/SubsetSpectrum/HalfIntegerOccupancy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/HalfIntegerOccupancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity limits and attains integer grid coverage by ternary occupancies of half-integer weights. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

open Finset

namespace D5.S3.Combinatorics.SubsetSpectrum.HalfIntegerOccupancy

private theorem wordCode_parity (h : ℕ) (f : Fin h → Fin 3) :
    (finFunctionFinEquiv f).val % 2 = (∑ i, (f i).val) % 2 := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ 2).mp
  rw [finFunctionFinEquiv_apply]
  have three : (3 : ZMod 2) = 1 := by decide
  push_cast
  simp [three]

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
      {j : Fin (3^h) // j.val % 2 = 0} := (finFunctionFinEquiv (m := 3) (n := h)).subtypeEquiv
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

end D5.S3.Combinatorics.SubsetSpectrum.HalfIntegerOccupancy
