/- GID: D5/S3/Factorization/CompleteMappingEvenProduct
   generality: G
   mirror-B: D5/B/S3/Factorization/CompleteMappingEvenProduct
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: An explicit complete mapping of ZMod 2 times ZMod (2*m) for every positive m. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.CompleteMappingEvenProduct

private def upperHalf (m : ℕ) (k : ZMod (2 * m)) : ZMod 2 :=
  if k.val < m then 0 else 1

private lemma eq_of_upperHalf_eq_of_add_self_eq (m : ℕ) (hm : 0 < m)
    {a b : ZMod (2 * m)} (hh : upperHalf m a = upperHalf m b)
    (hd : a + a = b + b) : a = b := by
  letI : NeZero (2 * m) := ⟨by omega⟩
  have ha2 : a.val < 2 * m := ZMod.val_lt a
  have hb2 : b.val < 2 * m := ZMod.val_lt b
  have hd' : ((a.val + a.val : ℕ) : ZMod (2 * m)) =
      ((b.val + b.val : ℕ) : ZMod (2 * m)) := by
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using hd
  have hmod : a.val % m = b.val % m := by
    have hdouble : 2 * a.val ≡ 2 * b.val [MOD 2 * m] := by
      simpa only [two_mul] using
        (ZMod.natCast_eq_natCast_iff (a.val + a.val)
          (b.val + b.val) (2 * m)).mp hd'
    exact Nat.ModEq.mul_left_cancel' (by decide : 2 ≠ 0) hdouble
  by_cases ha : a.val < m
  · have hb : b.val < m := by
      by_contra h
      have h01 : (0 : ZMod 2) = 1 := by
        simpa [upperHalf, ha, h] using hh
      norm_num at h01
    apply ZMod.val_injective (2 * m)
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
    omega
  · have hb : ¬b.val < m := by
      intro h
      have h10 : (1 : ZMod 2) = 0 := by
        simpa [upperHalf, ha, h] using hh
      norm_num at h10
    apply ZMod.val_injective (2 * m)
    have ha' : a.val % m = a.val - m := by
      rw [Nat.mod_eq_sub_mod (by omega : m ≤ a.val),
        Nat.mod_eq_of_lt (by omega : a.val - m < m)]
    have hb' : b.val % m = b.val - m := by
      rw [Nat.mod_eq_sub_mod (by omega : m ≤ b.val),
        Nat.mod_eq_of_lt (by omega : b.val - m < m)]
    rw [ha', hb'] at hmod
    omega

private lemma parity_of_double_sub_eq (m : ℕ) (hm : 0 < m)
    (e f : ZMod 2) (k l : ZMod (2 * m))
    (h : k + k - (e.val : ZMod (2 * m)) =
      l + l - (f.val : ZMod (2 * m))) : e = f := by
  letI : NeZero (2 * m) := ⟨by omega⟩
  have hdiv : 2 ∣ 2 * m := ⟨m, by ring⟩
  have hc := congrArg (ZMod.castHom hdiv (ZMod 2)) h
  simp only [map_sub, map_add, ZMod.castHom_apply,
    ZMod.cast_natCast hdiv, CharTwo.add_self_eq_zero, zero_sub, neg_inj] at hc
  simpa only [ZMod.natCast_zmod_val] using hc

private def coordinateEquiv (m : ℕ) :
    (ZMod 2 × ZMod (2 * m)) ≃ (ZMod 2 × ZMod (2 * m)) where
  toFun x := (x.1, x.2 + (x.1.val : ZMod (2 * m)))
  invFun x := (x.1, x.2 - (x.1.val : ZMod (2 * m)))
  left_inv := by
    intro x
    ext <;> simp
  right_inv := by
    intro x
    ext <;> simp

/-- The explicit column permutation; its shifted second coordinate also records
which half of `ZMod (2*m)` is used by the symbol permutation. -/
def theta (m : ℕ) (x : ZMod 2 × ZMod (2 * m)) :
    ZMod 2 × ZMod (2 * m) :=
  let k := x.2 + (x.1.val : ZMod (2 * m))
  (x.1 + upperHalf m k, k)

private def symbol (m : ℕ) (x : ZMod 2 × ZMod (2 * m)) :
    ZMod 2 × ZMod (2 * m) :=
  (upperHalf m x.2, x.2 + x.2 - (x.1.val : ZMod (2 * m)))

/-- Every `ZMod 2 × ZMod (2*m)` with `m > 0` has the explicit complete mapping
`theta`: both its column and sum-symbol maps are permutations. -/
theorem theta_complete (m : ℕ) (hm : 0 < m) :
    Function.Bijective (theta m) ∧
      Function.Bijective (fun x : ZMod 2 × ZMod (2 * m) => x + theta m x) := by
  letI : NeZero (2 * m) := ⟨by omega⟩
  have hcolumn : Function.Injective
      (fun p : ZMod 2 × ZMod (2 * m) => (p.1 + upperHalf m p.2, p.2)) := by
    intro x y h
    rcases x with ⟨e, k⟩
    rcases y with ⟨f, l⟩
    have hk : k = l := congrArg Prod.snd h
    subst l
    have he : e + upperHalf m k = f + upperHalf m k := congrArg Prod.fst h
    exact Prod.ext (add_right_cancel he) rfl
  have htheta : Function.Injective (theta m) := by
    intro x y h
    apply (coordinateEquiv m).injective
    exact hcolumn h
  have hsymbol : Function.Injective (symbol m) := by
    intro x y h
    rcases x with ⟨e, k⟩
    rcases y with ⟨f, l⟩
    have hh : upperHalf m k = upperHalf m l := congrArg Prod.fst h
    have hs : k + k - (e.val : ZMod (2 * m)) =
        l + l - (f.val : ZMod (2 * m)) := congrArg Prod.snd h
    have he : e = f := parity_of_double_sub_eq m hm e f k l hs
    have hd : k + k = l + l := by
      exact sub_left_inj.mp (by simpa only [he] using hs)
    exact Prod.ext he (eq_of_upperHalf_eq_of_add_self_eq m hm hh hd)
  have hsum_formula (x : ZMod 2 × ZMod (2 * m)) :
      x + theta m x = symbol m (coordinateEquiv m x) := by
    rcases x with ⟨e, j⟩
    apply Prod.ext
    · simp [theta, symbol, coordinateEquiv, CharTwo.add_cancel_left]
    · dsimp [theta, symbol, coordinateEquiv]
      abel
  have hsum : Function.Injective
      (fun x : ZMod 2 × ZMod (2 * m) => x + theta m x) := by
    intro x y h
    apply (coordinateEquiv m).injective
    apply hsymbol
    rw [← hsum_formula x, ← hsum_formula y]
    exact h
  exact ⟨htheta.bijective_of_finite, hsum.bijective_of_finite⟩

end D5.S3.Factorization.CompleteMappingEvenProduct
