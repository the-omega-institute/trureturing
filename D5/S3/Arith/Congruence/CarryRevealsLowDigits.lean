/- GID: D5/S3/Arith/Congruence/CarryRevealsLowDigits
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/CarryRevealsLowDigits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reading one p-adic digit along p^k translation steps recovers all lower digits through the first carry. -/

import Mathlib.NumberTheory.Padics.RingHoms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.CarryRevealsLowDigits

variable {p : ℕ} [hp : Fact p.Prime]

/-- The digit `d_k(x) = ⌊[q_{k+1}(x)] / p^k⌋` of a `p`-adic integer, read from its residue modulo
`p^{k+1}`. -/
noncomputable def highDigit (k : ℕ) (x : ℤ_[p]) : ℕ :=
  (PadicInt.toZModPow (k + 1) x).val / p ^ k

/-- The fixed protocol `W_{k,N}(x) = (d_k(x), d_k(x + 1), …, d_k(x + N))`. -/
noncomputable def digitProtocol (k N : ℕ) (x : ℤ_[p]) : Fin (N + 1) → ℕ :=
  fun n => highDigit k (x + (((n : ℕ) : ℕ) : ℤ_[p]))

/-- **A carry reveals the missing low digits.** Write the residue of `x` modulo `p^{k+1}` as
`b p^k + r` with `b < p`, `r < p^k`. For `0 ≤ n ≤ p^k - 1` the digit after `n` steps is
`(b + ⌊(r + n)/p^k⌋) mod p`; the reading changes for the first time at `n = p^k - r` when
`r > 0` and never when `r = 0`; hence the `p^k` readings `W_{k,p^k-1}` identify exactly the
residue modulo `p^{k+1}`. For `k ≥ 1` this horizon is sharp: the readings of `0` and `1` agree
under every shorter protocol `W_{k,N}`, `N < p^k - 1`. -/
theorem carry_reveals_low_digits (k : ℕ) (x y : ℤ_[p]) :
    (∀ n, n ≤ p ^ k - 1 →
      highDigit k (x + ((n : ℕ) : ℤ_[p])) =
        ((PadicInt.toZModPow (k + 1) x).val / p ^ k +
          ((PadicInt.toZModPow (k + 1) x).val % p ^ k + n) / p ^ k) % p) ∧
    ((PadicInt.toZModPow (k + 1) x).val % p ^ k = 0 →
      ∀ n, 1 ≤ n → n ≤ p ^ k - 1 → highDigit k (x + ((n : ℕ) : ℤ_[p])) = highDigit k x) ∧
    (0 < (PadicInt.toZModPow (k + 1) x).val % p ^ k →
      highDigit k (x + ((p ^ k - (PadicInt.toZModPow (k + 1) x).val % p ^ k : ℕ) : ℤ_[p])) ≠
          highDigit k x ∧
        ∀ n, 1 ≤ n → n < p ^ k - (PadicInt.toZModPow (k + 1) x).val % p ^ k →
          highDigit k (x + ((n : ℕ) : ℤ_[p])) = highDigit k x) ∧
    (digitProtocol k (p ^ k - 1) x = digitProtocol k (p ^ k - 1) y ↔
      PadicInt.toZModPow (k + 1) x = PadicInt.toZModPow (k + 1) y) ∧
    ∀ N, 1 ≤ k → N < p ^ k - 1 →
      digitProtocol k N (0 : ℤ_[p]) = digitProtocol k N (1 : ℤ_[p]) ∧
        PadicInt.toZModPow (k + 1) (0 : ℤ_[p]) ≠ PadicInt.toZModPow (k + 1) (1 : ℤ_[p]) := by
  classical
  -- the horizon `p^k - 1` is sharp: `0` and `1` agree on every shorter protocol
  have hsharp : ∀ N, 1 ≤ k → N < p ^ k - 1 →
      digitProtocol k N (0 : ℤ_[p]) = digitProtocol k N (1 : ℤ_[p]) ∧
        PadicInt.toZModPow (k + 1) (0 : ℤ_[p]) ≠ PadicInt.toZModPow (k + 1) (1 : ℤ_[p]) := by
    intro N hk hN
    have hp2 : 2 ≤ p := hp.out.two_le
    have hPk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hPk1 : p ^ k < p ^ (k + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    constructor
    · funext n
      have hn : (n : ℕ) ≤ N := Nat.lt_succ_iff.mp n.2
      simp only [digitProtocol, highDigit, map_add, map_natCast, map_zero, map_one, zero_add]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
        show ((1 : ZMod (p ^ (k + 1))) + ((n : ℕ) : ZMod (p ^ (k + 1)))) =
          (((1 + (n : ℕ) : ℕ)) : ZMod (p ^ (k + 1))) by push_cast; ring,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega),
        Nat.div_eq_of_lt (by omega)]
    · rw [map_zero, map_one]
      intro h
      have hone : p ^ (k + 1) = 1 := ZMod.one_eq_zero_iff.mp h.symm
      omega

  have hp2 : 2 ≤ p := hp.out.two_le
  set P := p ^ k with hP
  have hPpos : 0 < P := pow_pos (by omega) k
  have hmod : p ^ (k + 1) = P * p := pow_succ p k
  -- the residue of a translate
  have hval : ∀ (z : ℤ_[p]) (n : ℕ), (PadicInt.toZModPow (k + 1) (z + ((n : ℕ) : ℤ_[p]))).val =
      ((PadicInt.toZModPow (k + 1) z).val + n) % p ^ (k + 1) := by
    intro z n
    rw [map_add, map_natCast, ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
  -- the carry formula
  have hcarry : ∀ (z : ℤ_[p]) (n : ℕ), n ≤ P - 1 →
      highDigit k (z + ((n : ℕ) : ℤ_[p])) =
        ((PadicInt.toZModPow (k + 1) z).val / P + ((PadicInt.toZModPow (k + 1) z).val % P + n) / P)
          % p := by
    intro z n _
    unfold highDigit
    rw [hval]
    generalize (PadicInt.toZModPow (k + 1) z).val = v
    have hdiv : (v + n) % p ^ (k + 1) / P = (v + n) / P % p := by
      rw [hmod, Nat.mod_mul_right_div_self]
    rw [hdiv]
    congr 1
    conv_lhs => rw [← Nat.div_add_mod v P]
    rw [show P * (v / P) + v % P + n = (v % P + n) + (v / P) * P by ring,
      Nat.add_mul_div_right _ _ hPpos]
    ring
  -- the current digit and its range
  have hdigit : ∀ z : ℤ_[p], highDigit k z = (PadicInt.toZModPow (k + 1) z).val / P := fun z => rfl
  have hb_lt : ∀ z : ℤ_[p], (PadicInt.toZModPow (k + 1) z).val / P < p := by
    intro z
    have hlt : (PadicInt.toZModPow (k + 1) z).val < P * p :=
      (ZMod.val_lt (PadicInt.toZModPow (k + 1) z)).trans_eq hmod
    exact Nat.div_lt_of_lt_mul hlt
  -- no change before the carry, a change at the carry
  have hbefore : ∀ (z : ℤ_[p]) (n : ℕ), n ≤ P - 1 →
      (PadicInt.toZModPow (k + 1) z).val % P + n < P →
        highDigit k (z + ((n : ℕ) : ℤ_[p])) = highDigit k z := by
    intro z n hn hlt
    rw [hcarry z n hn, Nat.div_eq_of_lt hlt, add_zero, Nat.mod_eq_of_lt (hb_lt z), hdigit]
  have hat : ∀ z : ℤ_[p], 0 < (PadicInt.toZModPow (k + 1) z).val % P →
      highDigit k (z + ((P - (PadicInt.toZModPow (k + 1) z).val % P : ℕ) : ℤ_[p])) ≠ highDigit k z := by
    intro z hr
    have hrP := Nat.mod_lt (PadicInt.toZModPow (k + 1) z).val hPpos
    rw [hcarry z _ (by omega), show (PadicInt.toZModPow (k + 1) z).val % P +
        (P - (PadicInt.toZModPow (k + 1) z).val % P) = P by omega, Nat.div_self hPpos, hdigit]
    have hb := hb_lt z
    intro h
    rcases Nat.lt_or_ge ((PadicInt.toZModPow (k + 1) z).val / P + 1) p with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at h
      omega
    · have h2 : (PadicInt.toZModPow (k + 1) z).val / P + 1 = p := by omega
      rw [h2, Nat.mod_self] at h
      omega
  refine ⟨fun n hn => hcarry x n hn, fun hr n _ hn => hbefore x n hn (by omega),
    fun hr => ⟨hat x hr, fun n _ hn => hbefore x n (by omega) (by omega)⟩, ?_, hsharp⟩
  constructor
  · intro hW
    have hread : ∀ n, n ≤ P - 1 → highDigit k (x + ((n : ℕ) : ℤ_[p])) = highDigit k (y + ((n : ℕ) : ℤ_[p])) := by
      intro n hn
      have := congrFun hW ⟨n, by omega⟩
      simpa [digitProtocol] using this
    have hb : (PadicInt.toZModPow (k + 1) x).val / P = (PadicInt.toZModPow (k + 1) y).val / P := by
      have := hread 0 (Nat.zero_le _)
      simpa [hdigit] using this
    -- the first carry times agree, so the low remainders agree
    have hr : (PadicInt.toZModPow (k + 1) x).val % P = (PadicInt.toZModPow (k + 1) y).val % P := by
      set rx := (PadicInt.toZModPow (k + 1) x).val % P
      set ry := (PadicInt.toZModPow (k + 1) y).val % P
      have hrx : rx < P := Nat.mod_lt _ hPpos
      have hry : ry < P := Nat.mod_lt _ hPpos
      have hbx : highDigit k x = highDigit k y := by rw [hdigit, hdigit, hb]
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · -- `y` carries first, at `P - ry`
        have hy := hat y (by omega)
        have hx := hbefore x (P - ry) (by omega) (by omega)
        rw [hread (P - ry) (by omega)] at hx
        exact hy (hx.trans hbx)
      · have hx := hat x (by omega)
        have hy := hbefore y (P - rx) (by omega) (by omega)
        rw [← hread (P - rx) (by omega)] at hy
        exact hx (hy.trans hbx.symm)
    apply ZMod.val_injective
    rw [← Nat.div_add_mod (PadicInt.toZModPow (k + 1) x).val P,
      ← Nat.div_add_mod (PadicInt.toZModPow (k + 1) y).val P, hb, hr]
  · intro hq
    funext n
    simp only [digitProtocol, highDigit, map_add, hq]

#print axioms carry_reveals_low_digits

end D5.S3.Arith.Congruence.CarryRevealsLowDigits
