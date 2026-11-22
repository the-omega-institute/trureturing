/- GID: D5/S3/Arith/Additive/BenfieldLippard/EvenBound
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/BenfieldLippard/EvenBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fermat divisibility bounds the number of gaps from below at prime-minus-one exponents. -/

import D5.S3.Arith.Additive.BenfieldLippard.Stabilization
import Mathlib.FieldTheory.Finite.Basic

namespace BenfieldLippard

private theorem dvd_small_offset {p s : ℕ} (hp : p.Prime)
    (hs : s ∈ offsets (p - 1)) (hb : s < p ^ (p - 1) - 1) : p ∣ s := by
  let : Fact p.Prime := ⟨hp⟩
  change s ∈ AddSubmonoid.closure (generators (p - 1)) at hs
  induction hs using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    have hap : a < p := by
      by_contra! h
      exact hb.not_ge (Nat.sub_le_sub_right (Nat.pow_le_pow_left h (p - 1)) 1)
    have hcast : (a : ZMod p) ≠ 0 := by
      intro h
      have := Nat.le_of_dvd ha ((ZMod.natCast_eq_zero_iff _ _).mp h)
      omega
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub (Nat.one_le_pow _ _ ha), Nat.cast_pow, Nat.cast_one,
      ZMod.pow_card_sub_one_eq_one hcast, sub_self]
  | zero => exact dvd_zero p
  | add x y _ _ hx hy =>
    exact dvd_add (hx (by omega)) (hy (by omega))

theorem even_lower {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) :
    p ^ (p - 1) ≤ 2 * (gaps (p - 1)).ncard := by
  classical
  let M := p ^ (p - 2)
  have hM : p ≤ M := by
    simpa [M] using Nat.pow_le_pow_right hp.pos (show 1 ≤ p - 2 by omega)
  have hpow : p ^ (p - 1) = p * M := by
    have e : p - 1 = (p - 2) + 1 := by omega
    rw [e, pow_succ, Nat.mul_comm]
  let value : Fin (M - 1) × Fin (p - 1) → ℕ := fun x ↦ p * x.1.val + (x.2.val + 1)
  have rem (x : Fin (M - 1) × Fin (p - 1)) : value x % p = x.2.val + 1 := by
    have hx := x.2.isLt
    simp [value, Nat.mod_eq_of_lt (show x.2.val + 1 < p by omega)]
  have isGap (x : Fin (M - 1) × Fin (p - 1)) : value x ∈ gaps (p - 1) := by
    have hpos : 0 < value x := by simp [value]
    have hlt : value x < p ^ (p - 1) - 1 := by
      have hx := x.1.isLt
      have hy := x.2.isLt
      have ha : p * x.1.val + (x.2.val + 1) < p * (x.1.val + 1) := by
        rw [Nat.mul_succ]
        omega
      have hb : p * (x.1.val + 1) ≤ p * (M - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hc : p * (M - 1) + p = p * M := by
        rw [← Nat.mul_succ]
        exact congrArg (p * ·) (by omega)
      rw [hpow]
      change p * x.1.val + (x.2.val + 1) < p * M - 1
      omega
    refine ⟨hpos, fun hs ↦ ?_⟩
    have hdiv := Nat.mod_eq_zero_of_dvd (dvd_small_offset hp hs hlt)
    rw [rem] at hdiv
    omega
  let f : Fin (M - 1) × Fin (p - 1) → gaps (p - 1) := fun x ↦ ⟨value x, isGap x⟩
  have hf : Function.Injective f := by
    intro x y he
    have hv : value x = value y := congrArg Subtype.val he
    have hrem : x.2.val + 1 = y.2.val + 1 := (rem x).symm.trans ((congrArg (· % p) hv).trans (rem y))
    have hhigh : p * x.1.val = p * y.1.val := by
      change p * x.1.val + (x.2.val + 1) = p * y.1.val + (y.2.val + 1) at hv
      omega
    exact Prod.ext (Fin.ext (Nat.eq_of_mul_eq_mul_left hp.pos hhigh)) (Fin.ext (by omega))
  let := (stabilization (p - 1) (by omega)).1.fintype
  have hc : (M - 1) * (p - 1) ≤ (gaps (p - 1)).ncard := by
    simpa using Fintype.card_le_of_injective f hf
  have inequality : p * M ≤ 2 * ((M - 1) * (p - 1)) := by
    have hm : M - 1 + 1 = M := by omega
    have hq : p - 1 + 1 = p := by omega
    have hi := Nat.mul_le_mul_left (M - 1) (show 3 ≤ p - 1 by omega)
    have hj := Nat.mul_le_mul_right (p - 1) (show 3 ≤ M - 1 by omega)
    nlinarith
  rw [hpow]
  exact inequality.trans (Nat.mul_le_mul_left 2 hc)

end BenfieldLippard
