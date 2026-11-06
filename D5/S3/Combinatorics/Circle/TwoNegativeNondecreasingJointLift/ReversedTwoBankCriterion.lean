import Mathlib

/-!
Source-only candidate: UNCOMPILED. No elaboration, kernel, axiom-closure,
official, or physical-source acceptance is claimed.

This file supplies only the reversed two-bank integer arithmetic. Its future
physical consumer must independently establish the actualSource table, binary
mask realization with distinct physical labels, the smaller-negative reduction,
and the equivalence with one shared old permutation and literal fresh insertion.

The interval witness is not asserted unique. The fresh branches force the
second mask y to be full or empty; the first mask x remains variable.
-/

set_option autoImplicit false

namespace ReversedTwoBankCriterion

private def interval (p d : ℤ) : Prop :=
  ∃ u : ℤ, 0 ≤ u ∧ d ≤ (2 * p + 1) * u ∧ (4 * p + 1) * u ≤ 2 * d

private theorem bounded_mask_iff (p L : ℤ) (hp : 2 ≤ p) (hL : 2 * p ≤ L) :
    let T := 2 * p * L
    let H := T - 1
    let N := 2 * T - 1
    let Q := T + p
    let C := T - L - 1
    let E := 2 * T - L - 1
    (∃ x y : ℤ, ∃ e : Bool,
      let P := (2 * p + 1) * x + (2 * L + 1) * y
      let G := P + 2 * p * x
      0 ≤ x ∧ x < L ∧ 0 ≤ y ∧ y < p ∧ C ≤ P ∧ P ≤ H ∧
        E ≤ G + (if e then Q else 0) ∧ G + (if e then Q else 0) ≤ N) ↔
      interval p (L - p) ∨ interval p (L - 2 * p) := by
  let T : ℤ := 2 * p * L
  let H : ℤ := T - 1
  let N : ℤ := 2 * T - 1
  let Q : ℤ := T + p
  let C : ℤ := T - L - 1
  let E : ℤ := 2 * T - L - 1
  change
    (∃ x y : ℤ, ∃ e : Bool,
      let P := (2 * p + 1) * x + (2 * L + 1) * y
      let G := P + 2 * p * x
      0 ≤ x ∧ x < L ∧ 0 ≤ y ∧ y < p ∧ C ≤ P ∧ P ≤ H ∧
        E ≤ G + (if e then Q else 0) ∧ G + (if e then Q else 0) ≤ N) ↔
      interval p (L - p) ∨ interval p (L - 2 * p)
  have hL0 : 0 ≤ L := by omega
  constructor
  · rintro ⟨x, y, e, hx0, hxL, hy0, hyp, hOldLo, hOldHi, hNewLo, hNewHi⟩
    let P : ℤ := (2 * p + 1) * x + (2 * L + 1) * y
    change C ≤ P at hOldLo
    change P ≤ H at hOldHi
    cases e with
    | false =>
      have hNewLo : E ≤ P + 2 * p * x := by simpa using hNewLo
      let W : ℤ := L - 2 * p
      let u : ℤ := L - 1 - x
      let z : ℤ := H - P
      have hu0 : 0 ≤ u := by dsimp only [u]; omega
      have huL : u < L := by dsimp only [u]; omega
      have hz0 : 0 ≤ z := by dsimp only [z]; omega
      have hcut : z + 2 * p * u ≤ W := by
        dsimp only [z, u, W, H, E, T] at hNewLo ⊢
        nlinarith only [hNewLo]
      have hid : (2 * L + 1) * y = (2 * p + 1) * u - W - z := by
        dsimp only [P, u, W, z, H, T]
        ring
      have hbound : (2 * L + 1) * y ≤ u := by
        nlinarith only [hid, hcut, hz0]
      have hsmall : (2 * L + 1) * y < 2 * L + 1 := by
        linarith only [hbound, huL, hL0]
      have hyzero : y = 0 := by
        by_contra hne
        have hy1 : 1 ≤ y := by omega
        have hmul := mul_le_mul_of_nonneg_left hy1
          (show 0 ≤ 2 * L + 1 by omega)
        nlinarith only [hmul, hsmall]
      rw [hyzero, mul_zero] at hid
      right
      change interval p W
      refine ⟨u, hu0, ?_, ?_⟩
      · nlinarith only [hid, hz0]
      · nlinarith only [hid, hcut]
    | true =>
      have hNewHi : P + 2 * p * x + Q ≤ N := by simpa using hNewHi
      let W : ℤ := L - p
      let z : ℤ := P - C
      let v : ℤ := p - 1 - y
      have hz0 : 0 ≤ z := by dsimp only [z]; omega
      have hv0 : 0 ≤ v := by dsimp only [v]; omega
      have hcut : z + 2 * p * x ≤ W := by
        dsimp only [z, W, C, N, Q, T] at hNewHi ⊢
        nlinarith only [hNewHi]
      have hid : (2 * L + 1) * v = (2 * p + 1) * x - W - z := by
        dsimp only [P, v, W, z, C, T]
        ring
      have hbound : (2 * L + 1) * v ≤ x := by
        nlinarith only [hid, hcut, hz0]
      have hsmall : (2 * L + 1) * v < 2 * L + 1 := by
        linarith only [hbound, hxL, hL0]
      -- Integer forcing: v = 0 is exactly y = p - 1.
      have hvzero : v = 0 := by
        by_contra hne
        have hv1 : 1 ≤ v := by omega
        have hmul := mul_le_mul_of_nonneg_left hv1
          (show 0 ≤ 2 * L + 1 by omega)
        nlinarith only [hmul, hsmall]
      rw [hvzero, mul_zero] at hid
      left
      change interval p W
      refine ⟨x, hx0, ?_, ?_⟩
      · nlinarith only [hid, hz0]
      · nlinarith only [hid, hcut]
  · rintro (h | h)
    · rcases h with ⟨u, hu0, hlo, hhi⟩
      let W : ℤ := L - p
      let z : ℤ := (2 * p + 1) * u - W
      have hz0 : 0 ≤ z := by dsimp only [z, W]; linarith only [hlo]
      have hcut : z + 2 * p * u ≤ W := by
        dsimp only [z, W]
        nlinarith only [hhi]
      have hpu0 : 0 ≤ 2 * p * u := mul_nonneg (by omega) hu0
      have htwo : 2 * u ≤ (4 * p + 1) * u :=
        mul_le_mul_of_nonneg_right (by omega) hu0
      have huL : u < L := by linarith only [htwo, hhi, hp]
      have hP : (2 * p + 1) * u + (2 * L + 1) * (p - 1) = C + z := by
        dsimp only [C, T, z, W]
        ring
      refine ⟨u, p - 1, true, hu0, huL, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · change C ≤ (2 * p + 1) * u + (2 * L + 1) * (p - 1)
        rw [hP]
        linarith only [hz0]
      · change (2 * p + 1) * u + (2 * L + 1) * (p - 1) ≤ H
        rw [hP]
        dsimp only [C, H, T]
        dsimp only [W] at hcut
        nlinarith only [hcut, hpu0, hp]
      · change E ≤ ((2 * p + 1) * u + (2 * L + 1) * (p - 1)) + 2 * p * u + Q
        rw [hP]
        dsimp only [E, C, Q, T]
        nlinarith only [hz0, hpu0, hp]
      · change ((2 * p + 1) * u + (2 * L + 1) * (p - 1)) + 2 * p * u + Q ≤ N
        rw [hP]
        dsimp only [C, Q, N, T]
        dsimp only [W] at hcut
        nlinarith only [hcut]
    · rcases h with ⟨u, hu0, hlo, hhi⟩
      let W : ℤ := L - 2 * p
      let z : ℤ := (2 * p + 1) * u - W
      have hz0 : 0 ≤ z := by dsimp only [z, W]; linarith only [hlo]
      have hcut : z + 2 * p * u ≤ W := by
        dsimp only [z, W]
        nlinarith only [hhi]
      have hpu0 : 0 ≤ 2 * p * u := mul_nonneg (by omega) hu0
      have htwo : 2 * u ≤ (4 * p + 1) * u :=
        mul_le_mul_of_nonneg_right (by omega) hu0
      have huL : u < L := by linarith only [htwo, hhi, hp]
      have hP : (2 * p + 1) * (L - 1 - u) + (2 * L + 1) * 0 = H - z := by
        dsimp only [H, T, z, W]
        ring
      refine ⟨L - 1 - u, 0, false, by omega, by omega, by omega, by omega,
        ?_, ?_, ?_, ?_⟩
      · change C ≤ (2 * p + 1) * (L - 1 - u) + (2 * L + 1) * 0
        rw [hP]
        dsimp only [C, H, T]
        dsimp only [W] at hcut
        nlinarith only [hcut, hpu0, hp]
      · change (2 * p + 1) * (L - 1 - u) + (2 * L + 1) * 0 ≤ H
        rw [hP]
        linarith only [hz0]
      · change E ≤ ((2 * p + 1) * (L - 1 - u) + (2 * L + 1) * 0) +
          2 * p * (L - 1 - u) + 0
        rw [add_zero, hP]
        dsimp only [E, H, T]
        dsimp only [W] at hcut
        nlinarith only [hcut]
      · change ((2 * p + 1) * (L - 1 - u) + (2 * L + 1) * 0) +
          2 * p * (L - 1 - u) + 0 ≤ N
        rw [add_zero, hP]
        dsimp only [H, N, T]
        nlinarith only [hz0, hpu0, hp]

private theorem interval_of_large (p d : ℤ) (hp : 2 ≤ p)
    (hd : (2 * p + 1) * (4 * p + 1) ≤ d) : interval p d := by
  let m : ℤ := 2 * p + 1
  let c : ℤ := 4 * p + 1
  let q : ℤ := d / m
  let s : ℤ := d % m
  have hm : 0 < m := by dsimp only [m]; omega
  have hs0 : 0 ≤ s := Int.emod_nonneg d (ne_of_gt hm)
  have hsm : s < m := Int.emod_lt_of_pos d hm
  have hdiv : m * q + s = d := Int.mul_ediv_add_emod d m
  have hcq : c ≤ q := by
    change c ≤ d / m
    apply (Int.le_ediv_iff_mul_le hm).2
    dsimp only [c, m]
    nlinarith only [hd]
  have hq0 : 0 ≤ q := by dsimp only [c] at hcq; omega
  refine ⟨q + 1, by omega, ?_, ?_⟩
  · change d ≤ m * (q + 1)
    nlinarith only [hdiv, hsm]
  · have hdiv' : (2 * p + 1) * q + s = d := hdiv
    have hcq' : 4 * p + 1 ≤ q := hcq
    nlinarith only [hdiv', hcq', hs0]

private theorem intervals_empty_of_wedge (p K : ℤ) (hp : 2 ≤ p)
    (hK2 : 2 ≤ K) (hKp : K ≤ p) :
    ¬ (interval p (2 * p * K - p) ∨ interval p (2 * p * K - 2 * p)) := by
  rintro (h | h)
  · rcases h with ⟨u, _hu0, hlo, hhi⟩
    have hKu : K ≤ u := by
      by_contra hnot
      have huK : u ≤ K - 1 := by omega
      have hmul := mul_le_mul_of_nonneg_left huK
        (show 0 ≤ 2 * p + 1 by omega)
      nlinarith only [hlo, hmul, hKp]
    have hmul := mul_le_mul_of_nonneg_left hKu
      (show 0 ≤ 4 * p + 1 by omega)
    nlinarith only [hmul, hhi, hp, hK2]
  · rcases h with ⟨u, _hu0, hlo, hhi⟩
    have hKu : K - 1 ≤ u := by
      by_contra hnot
      have huK : u ≤ K - 2 := by omega
      have hmul := mul_le_mul_of_nonneg_left huK
        (show 0 ≤ 2 * p + 1 by omega)
      nlinarith only [hlo, hmul, hKp, hp]
    have hmul := mul_le_mul_of_nonneg_left hKu
      (show 0 ≤ 4 * p + 1 by omega)
    nlinarith only [hmul, hhi, hK2]

private theorem dyadic_factorization (a b : ℕ) (hb : 2 ≤ b) (hba : b < a) :
    (2 : ℤ) ^ (a - 1) = 2 * (2 : ℤ) ^ (b - 1) * (2 : ℤ) ^ (a - b - 1) := by
  have he : a - 1 = ((b - 1) + (a - b - 1)) + 1 := by omega
  rw [he, pow_succ, pow_add]
  ring

private theorem dyadic_square_scale (b k : ℕ) (hb : 2 ≤ b) :
    (2 : ℤ) ^ (2 * b + k - 1) =
      (2 : ℤ) ^ (k + 1) * ((2 : ℤ) ^ (b - 1)) ^ 2 := by
  have he : 2 * b + k - 1 = ((b - 1) + (b - 1)) + (k + 1) := by omega
  rw [he, pow_add, pow_add]
  ring

private theorem dyadic_clock (a b : ℕ) (hb : 2 ≤ b) (hba : b < a) :
    (interval ((2 : ℤ) ^ (b - 1))
        ((2 : ℤ) ^ (a - 1) - (2 : ℤ) ^ (b - 1)) ∨
      interval ((2 : ℤ) ^ (b - 1))
        ((2 : ℤ) ^ (a - 1) - 2 * (2 : ℤ) ^ (b - 1))) ↔
      a = b + 1 ∨ 2 * b < a := by
  let p : ℤ := (2 : ℤ) ^ (b - 1)
  let L : ℤ := (2 : ℤ) ^ (a - 1)
  change (interval p (L - p) ∨ interval p (L - 2 * p)) ↔
    a = b + 1 ∨ 2 * b < a
  have hp : 2 ≤ p := by
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (show 1 ≤ b - 1 by omega)
    simpa only [p, pow_one] using hpow
  constructor
  · intro h
    by_contra hnot
    have haLo : b + 2 ≤ a := by omega
    have haHi : a ≤ 2 * b := by omega
    let K : ℤ := (2 : ℤ) ^ (a - b - 1)
    have hK2 : 2 ≤ K := by
      have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show 1 ≤ a - b - 1 by omega)
      simpa only [K, pow_one] using hpow
    have hKp : K ≤ p :=
      pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show a - b - 1 ≤ b - 1 by omega)
    have hfactor : L = 2 * p * K := dyadic_factorization a b hb hba
    rw [hfactor] at h
    exact intervals_empty_of_wedge p K hp hK2 hKp h
  · rintro (ha | ha)
    · right
      have hL2 : L = 2 * p := by
        dsimp only [L]
        rw [ha, show b + 1 - 1 = (b - 1) + 1 by omega, pow_succ]
        dsimp only [p]
        ring
      rw [hL2, sub_self]
      exact ⟨0, by norm_num, by norm_num, by norm_num⟩
    · by_cases ha1 : a = 2 * b + 1
      · left
        have hL4 : L = 4 * p ^ 2 := by
          dsimp only [L]
          rw [ha1, dyadic_square_scale b 1 hb]
          norm_num [p]
        rw [hL4]
        refine ⟨2 * p - 1, by omega, ?_, ?_⟩ <;> nlinarith only [hp]
      · by_cases ha2 : a = 2 * b + 2
        · right
          have hL8 : L = 8 * p ^ 2 := by
            dsimp only [L]
            rw [ha2, dyadic_square_scale b 2 hb]
            norm_num [p]
          rw [hL8]
          refine ⟨4 * p - 2, by omega, ?_, ?_⟩ <;> nlinarith only [hp]
        · left
          have ha3 : 2 * b + 3 ≤ a := by omega
          have hscale : (2 : ℤ) ^ (2 * b + 3 - 1) = 16 * p ^ 2 := by
            rw [dyadic_square_scale b 3 hb]
            norm_num [p]
          have hL16 : 16 * p ^ 2 ≤ L := by
            calc
              16 * p ^ 2 = (2 : ℤ) ^ (2 * b + 3 - 1) := hscale.symm
              _ ≤ L := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
                (show 2 * b + 3 - 1 ≤ a - 1 by omega)
          apply interval_of_large p (L - p) hp
          have hsurplus : 0 ≤ (p - 1) * (8 * p + 1) :=
            mul_nonneg (by omega) (by omega)
          nlinarith only [hL16, hsurplus]

/- The exact arithmetic consumer retains the complete scalar existential.
   All preceding private helpers occur on its proof dependency path. -/
private theorem dyadic_bounded_mask_iff (a b : ℕ) (hb : 2 ≤ b) (hba : b < a) :
    let p : ℤ := (2 : ℤ) ^ (b - 1)
    let L : ℤ := (2 : ℤ) ^ (a - 1)
    let T := 2 * p * L
    let H := T - 1
    let N := 2 * T - 1
    let Q := T + p
    let C := T - L - 1
    let E := 2 * T - L - 1
    (∃ x y : ℤ, ∃ e : Bool,
      let P := (2 * p + 1) * x + (2 * L + 1) * y
      let G := P + 2 * p * x
      0 ≤ x ∧ x < L ∧ 0 ≤ y ∧ y < p ∧ C ≤ P ∧ P ≤ H ∧
        E ≤ G + (if e then Q else 0) ∧ G + (if e then Q else 0) ≤ N) ↔
      a = b + 1 ∨ 2 * b < a := by
  let p : ℤ := (2 : ℤ) ^ (b - 1)
  let L : ℤ := (2 : ℤ) ^ (a - 1)
  have hp : 2 ≤ p := by
    have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (show 1 ≤ b - 1 by omega)
    simpa only [p, pow_one] using hpow
  have hL : 2 * p ≤ L := by
    calc
      2 * p = (2 : ℤ) ^ ((b - 1) + 1) := by
        dsimp only [p]
        rw [pow_succ]
        ring
      _ ≤ L := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show (b - 1) + 1 ≤ a - 1 by omega)
  exact (bounded_mask_iff p L hp hL).trans (dyadic_clock a b hb hba)

end ReversedTwoBankCriterion
