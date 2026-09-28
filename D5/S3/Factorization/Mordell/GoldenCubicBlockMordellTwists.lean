/- GID: D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists
   generality: I
   mirror-B: D5/B/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists
   mirror-E: none(waiver:symbolic-elliptic-point-construction)
   anchors: []
   utility: none
   digest: Cubic-block layers yield distinct twists and infinite-order points. -/

import D5.S3.Arith.Primes.GoldenCubicBlockRanks
import D5.S3.Factorization.GoldenCubicBlockNoncube
import D5.S3.Factorization.MordellTwoAdicNonTorsion
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Localization.Rat
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists

open D5.S1.Scale
open D5.S3.Factorization.MordellTwoAdicNonTorsion

/-- The positive actual cubic Lucas block. -/
def block (j : ℕ) : ℕ := (goldenLucas (3 ^ j) ^ 2 + 3).toNat

/-- The cubic part of a block, with each prime exponent divided by three. -/
def cubePartRoot (j : ℕ) : ℕ := Nat.floorRoot 3 (block j)

/-- The cubefree factor of a block. -/
def cubefreePart (j : ℕ) : ℕ := block j / cubePartRoot j ^ 3

/-- An integral affine Mordell point whose rational group order is infinite. -/
def InfiniteOrderPoint (b X Y : ℤ) : Prop :=
  ∃ h : (mordellCurve b).Nonsingular (X : ℚ) (Y : ℚ),
    ¬ IsOfFinAddOrder (.some (X : ℚ) (Y : ℚ) h : (mordellCurve b).Point)

/-- On every actual layer, both canonical cubic twists and both unfactored
models carry the displayed infinite-order integral points. Distinct layers
have distinct cubic-twist parameters in `ℚˣ/(ℚˣ)^3`. -/
theorem actual_cubic_twists (j : ℕ) (hj : 1 ≤ j) :
    (mordellCurve (-3 * (cubefreePart j : ℤ) ^ 2)).IsElliptic ∧
    (mordellCurve (125 * (cubefreePart j : ℤ) ^ 2)).IsElliptic ∧
    (mordellCurve (-3 * (block j : ℤ) ^ 2)).IsElliptic ∧
    (mordellCurve (125 * (block j : ℤ) ^ 2)).IsElliptic ∧
    InfiniteOrderPoint (-3 * (cubefreePart j : ℤ) ^ 2)
      ((cubefreePart j : ℤ) * cubePartRoot j)
      ((cubefreePart j : ℤ) * goldenLucas (3 ^ j)) ∧
    InfiniteOrderPoint (125 * (cubefreePart j : ℤ) ^ 2)
      (5 * (cubefreePart j : ℤ) * cubePartRoot j)
      (25 * (cubefreePart j : ℤ) * Nat.fib (3 ^ j)) ∧
    InfiniteOrderPoint (-3 * (block j : ℤ) ^ 2)
      (block j : ℤ) ((block j : ℤ) * goldenLucas (3 ^ j)) ∧
    InfiniteOrderPoint (125 * (block j : ℤ) ^ 2)
      (5 * (block j : ℤ)) (25 * (block j : ℤ) * Nat.fib (3 ^ j)) ∧
    ∀ i : ℕ, 1 ≤ i → i ≠ j →
      (¬∃ q : ℚ, (cubefreePart i : ℚ) = q ^ 3 * (cubefreePart j : ℚ)) ∧
      (¬∃ q : ℚ,
        ((-3 : ℚ) * (cubefreePart i : ℚ) ^ 2) /
          ((-3 : ℚ) * (cubefreePart j : ℚ) ^ 2) = q ^ 6) ∧
      (¬∃ q : ℚ,
        ((125 : ℚ) * (cubefreePart i : ℚ) ^ 2) /
          ((125 : ℚ) * (cubefreePart j : ℚ) ^ 2) = q ^ 6) := by
  let x : ℤ := goldenLucas (3 ^ j)
  let f : ℤ := Nat.fib (3 ^ j)
  let B : ℕ → ℕ := block
  let c : ℕ → ℕ := cubePartRoot
  let d : ℕ → ℕ := cubefreePart
  have hBcast (k : ℕ) : (B k : ℤ) = goldenLucas (3 ^ k) ^ 2 + 3 := by
    dsimp [B, block]
    exact Int.natCast_toNat_eq_self.mpr
      (by nlinarith [sq_nonneg (goldenLucas (3 ^ k))])
  have hfactor (k : ℕ) : B k = d k * (c k) ^ 3 := by
    exact (Nat.div_mul_cancel (show (c k) ^ 3 ∣ B k from Nat.floorRoot_pow_dvd)).symm
  have hB0 (k : ℕ) : B k ≠ 0 := by
    intro hz
    have hcast := hBcast k
    rw [hz] at hcast
    have hzero : (0 : ℤ) = goldenLucas (3 ^ k) ^ 2 + 3 := by
      simpa using hcast
    nlinarith [sq_nonneg (goldenLucas (3 ^ k))]
  have hd0 (k : ℕ) : d k ≠ 0 := by
    intro hz
    have h := hfactor k
    rw [hz] at h
    exact hB0 k (by simpa using h)
  have point_order (b X Y : ℤ) (hEq : Y ^ 2 = X ^ 3 + b)
      (hXodd : ¬ (2 : ℤ) ∣ X) (hYeven : (2 : ℤ) ∣ Y) (hY0 : Y ≠ 0) :
      InfiniteOrderPoint b X Y := by
    have hX0 : X ≠ 0 := by
      intro hz
      apply hXodd
      rw [hz]
      exact dvd_zero _
    have hns : (mordellCurve b).Nonsingular (X : ℚ) (Y : ℚ) := by
      apply ((mordellCurve b).nonsingular_iff' _ _).2
      constructor
      · apply ((mordellCurve b).equation_iff _ _).2
        have hEqQ : (Y : ℚ) ^ 2 = (X : ℚ) ^ 3 + (b : ℚ) := by exact_mod_cast hEq
        simpa [mordellCurve] using hEqQ
      · right
        have hY0Q : (Y : ℚ) ≠ 0 := by exact_mod_cast hY0
        simpa [mordellCurve] using
          (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) hY0Q)
    have hXval : padicValRat 2 (X : ℚ) = 0 := by
      rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hXodd]
      norm_num
    have hYdiv : (2 : ℤ) ^ 1 ∣ Y := by simpa using hYeven
    have hYvalInt : 1 ≤ padicValInt 2 Y :=
      ((padicValInt_dvd_iff_of_ne_one (by decide : 2 ≠ 1) 1 Y).mp hYdiv).resolve_left hY0
    have hYval : 0 < padicValRat 2 (Y : ℚ) := by
      rw [padicValRat.of_int]
      have hYpos : 0 < padicValInt 2 Y := by omega
      exact_mod_cast hYpos
    refine ⟨hns, ?_⟩
    exact infinite_add_order_of_unit_x_positive_two_adic_y b hns
      (by exact_mod_cast hX0) hXval hYval
  have paired (D C : ℤ) (hD : 0 < D)
      (hDc : x ^ 2 + 3 = D * C ^ 3) :
      InfiniteOrderPoint (-3 * D ^ 2) (D * C) (D * x) ∧
      InfiniteOrderPoint (125 * D ^ 2) (5 * D * C) (25 * D * f) := by
    let Bint : ℤ := x ^ 2 + 3
    have hx72 : (x : ZMod 72) = 4 := (golden_cubic_lucas_block j hj).1
    have hxmod : x % 72 = 4 := (ZMod.intCast_eq_intCast_iff' x 4 72).mp hx72
    have hxEven : (2 : ℤ) ∣ x := by omega
    have hx0 : x ≠ 0 := by omega
    have hf4 : ((Nat.fib (3 ^ j) : ℕ) : ZMod 4) = 2 :=
      (golden_cubic_fibonacci_block j hj).1
    have hfmod : Nat.fib (3 ^ j) % 4 = 2 :=
      (ZMod.natCast_eq_natCast_iff' (Nat.fib (3 ^ j)) 2 4).mp hf4
    have hfEvenNat : 2 ∣ Nat.fib (3 ^ j) := by omega
    have hfEven : (2 : ℤ) ∣ f := by
      change (2 : ℤ) ∣ (Nat.fib (3 ^ j) : ℤ)
      exact_mod_cast hfEvenNat
    have hf0Nat : Nat.fib (3 ^ j) ≠ 0 := by omega
    have hf0 : f ≠ 0 := by
      change (Nat.fib (3 ^ j) : ℤ) ≠ 0
      exact_mod_cast hf0Nat
    have hBodd : ¬ (2 : ℤ) ∣ Bint := by
      obtain ⟨k, hk⟩ := hxEven
      have hBform : Bint = 2 * (2 * k ^ 2 + 1) + 1 := by
        dsimp [Bint]
        rw [hk]
        ring
      rw [hBform]
      omega
    have hdOdd : ¬ (2 : ℤ) ∣ D := by
      intro hdiv
      apply hBodd
      change (2 : ℤ) ∣ x ^ 2 + 3
      rw [hDc]
      exact dvd_mul_of_dvd_left hdiv _
    have hcOdd : ¬ (2 : ℤ) ∣ C := by
      intro hdiv
      apply hBodd
      change (2 : ℤ) ∣ x ^ 2 + 3
      rw [hDc]
      have hpow : (2 : ℤ) ∣ C ^ 3 := dvd_trans hdiv (dvd_pow_self C (by omega))
      exact dvd_mul_of_dvd_right hpow _
    have hdmod : D % 2 = 1 := by omega
    have hcmod : C % 2 = 1 := by omega
    have hdcOdd : ¬ (2 : ℤ) ∣ D * C := by
      intro hdiv
      have hmod : (D * C) % 2 = 0 := Int.emod_eq_zero_of_dvd hdiv
      rw [Int.mul_emod, hdmod, hcmod] at hmod
      norm_num at hmod
    have h5dcOdd : ¬ (2 : ℤ) ∣ 5 * D * C := by
      intro hdiv
      have hmod : (5 * D * C) % 2 = 0 := Int.emod_eq_zero_of_dvd hdiv
      have hdcmod : (D * C) % 2 = 1 := by omega
      rw [show 5 * D * C = 5 * (D * C) by ring, Int.mul_emod, hdcmod] at hmod
      norm_num at hmod
    have hminusEven : (2 : ℤ) ∣ D * x := dvd_mul_of_dvd_right hxEven _
    have hplusEven : (2 : ℤ) ∣ 25 * D * f := dvd_mul_of_dvd_right hfEven _
    have hodd : Odd (3 ^ j) := (by decide : Odd (3 : ℕ)).pow
    have hdisc := golden_lucas_discriminant (3 ^ j)
    rw [hodd.neg_one_pow] at hdisc
    have hF : 5 * f ^ 2 = Bint + 1 := by
      dsimp [f, Bint, x]
      nlinarith [hdisc]
    have hminusEq : (D * x) ^ 2 = (D * C) ^ 3 + (-3 * D ^ 2) := by
      calc
        (D * x) ^ 2 = D ^ 2 * x ^ 2 := by ring
        _ = D ^ 2 * (Bint - 3) := by dsimp [Bint]; ring
        _ = (D * C) ^ 3 + (-3 * D ^ 2) := by
          change Bint = D * C ^ 3 at hDc
          rw [hDc]
          ring
    have hplusEq : (25 * D * f) ^ 2 = (5 * D * C) ^ 3 + 125 * D ^ 2 := by
      calc
        (25 * D * f) ^ 2 = 125 * D ^ 2 * (5 * f ^ 2) := by ring
        _ = 125 * D ^ 2 * (Bint + 1) := by rw [hF]
        _ = (5 * D * C) ^ 3 + 125 * D ^ 2 := by
          change Bint = D * C ^ 3 at hDc
          rw [hDc]
          ring
    exact ⟨point_order (-3 * D ^ 2) (D * C) (D * x) hminusEq hdcOdd hminusEven
        (mul_ne_zero (ne_of_gt hD) hx0),
      point_order (125 * D ^ 2) (5 * D * C) (25 * D * f)
        hplusEq h5dcOdd hplusEven
        (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hD)) hf0)⟩
  have hdpos : (0 : ℤ) < d j := by
    exact_mod_cast (Nat.pos_of_ne_zero (hd0 j))
  have hBpos : (0 : ℤ) < B j := by
    rw [hBcast j]
    nlinarith [sq_nonneg x]
  have hactualFactor : x ^ 2 + 3 = (d j : ℤ) * (c j : ℤ) ^ 3 := by
    rw [← hBcast j]
    exact_mod_cast hfactor j
  have hscaled := paired (d j : ℤ) (c j : ℤ) hdpos hactualFactor
  have hunscaled := paired (B j : ℤ) 1 hBpos (by simp [hBcast j, x])
  have curve_elliptic (b : ℤ) (hb : b ≠ 0) : (mordellCurve b).IsElliptic := by
    have hdisc : (mordellCurve b).Δ = -432 * (b : ℚ) ^ 2 := by
      simp [mordellCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    constructor
    rw [hdisc]
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    exact isUnit_iff_ne_zero.mpr
      (mul_ne_zero (by norm_num : (-432 : ℚ) ≠ 0) (pow_ne_zero _ hbq))
  have hdi : (d j : ℤ) ≠ 0 := ne_of_gt hdpos
  have hminusElliptic : (mordellCurve (-3 * (d j : ℤ) ^ 2)).IsElliptic :=
    curve_elliptic _ (mul_ne_zero (by norm_num) (pow_ne_zero _ hdi))
  have hplusElliptic : (mordellCurve (125 * (d j : ℤ) ^ 2)).IsElliptic :=
    curve_elliptic _ (mul_ne_zero (by norm_num) (pow_ne_zero _ hdi))
  have hBi : (B j : ℤ) ≠ 0 := ne_of_gt hBpos
  have hminusUnscaledElliptic : (mordellCurve (-3 * (B j : ℤ) ^ 2)).IsElliptic :=
    curve_elliptic _ (mul_ne_zero (by norm_num) (pow_ne_zero _ hBi))
  have hplusUnscaledElliptic : (mordellCurve (125 * (B j : ℤ) ^ 2)).IsElliptic :=
    curve_elliptic _ (mul_ne_zero (by norm_num) (pow_ne_zero _ hBi))
  have hclass (i : ℕ) (hi : 1 ≤ i) (hij : i ≠ j) :
      ¬∃ q : ℚ, (d i : ℚ) = q ^ 3 * (d j : ℚ) := by
    have hsep : ∀ p : ℕ, p.Prime → p ∣ d i → ¬p ∣ d j := by
      intro p hp hpi hpj
      have hpBiNat : p ∣ B i := by
        rw [hfactor i]
        exact dvd_mul_of_dvd_left hpi _
      have hpBjNat : p ∣ B j := by
        rw [hfactor j]
        exact dvd_mul_of_dvd_left hpj _
      have hpBi : (p : ℤ) ∣ goldenLucas (3 ^ i) ^ 2 + 3 := by
        rw [← hBcast i]
        exact_mod_cast hpBiNat
      have hpBj : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3 := by
        rw [← hBcast j]
        exact_mod_cast hpBjNat
      have hri := (D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_b_prime_rank
        i p hi hp hpBi).1
      have hrj := (D5.S3.Arith.Primes.GoldenCubicBlockRanks.cubic_block_b_prime_rank
        j p hj hp hpBj).1
      have hpow : 3 ^ (i + 1) = 3 ^ (j + 1) := by omega
      have hindex : i + 1 = j + 1 :=
        (pow_right_injective₀ (by decide : 0 < (3 : ℕ))
          (by decide : (3 : ℕ) ≠ 1)) hpow
      exact hij (by omega)
    have hfac (k p : ℕ) : (d k).factorization p = (B k).factorization p % 3 := by
      have hcdvd : (c k) ^ 3 ∣ B k := Nat.floorRoot_pow_dvd
      have hdiv := congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_div hcdvd)
      have hcpow : ((c k) ^ 3).factorization p =
          3 * ((B k).factorization p / 3) := by
        simp [Nat.factorization_pow, c, cubePartRoot, B, Nat.factorization_floorRoot]
      change (d k).factorization p = (B k).factorization p -
        ((c k) ^ 3).factorization p at hdiv
      rw [hcpow] at hdiv
      omega
    have hNotCube : ¬∃ t : ℕ, t ^ 3 = B i := by
      intro ⟨t, ht⟩
      apply D5.S3.Factorization.GoldenCubicBlockNoncube.golden_cubic_block_not_cube i hi
      refine ⟨(t : ℤ), ?_⟩
      rw [← hBcast i]
      exact_mod_cast ht
    have hdNotOne : d i ≠ 1 := by
      intro hd1
      apply hNotCube
      refine ⟨c i, ?_⟩
      rw [hfactor i, hd1]
      simp
    obtain ⟨p, hp, hpi⟩ := Nat.exists_prime_and_dvd hdNotOne
    have hpj : ¬p ∣ d j := hsep p hp hpi
    have hviPos : 0 < (d i).factorization p :=
      hp.factorization_pos_of_dvd (hd0 i) hpi
    have hviLt : (d i).factorization p < 3 := by
      rw [hfac]
      exact Nat.mod_lt _ (by decide)
    have hvjZero : (d j).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hpj
    rintro ⟨q, hq⟩
    have hdiQ : (d i : ℚ) ≠ 0 := by exact_mod_cast hd0 i
    have hdjQ : (d j : ℚ) ≠ 0 := by exact_mod_cast hd0 j
    have hq0 : q ≠ 0 := by
      intro hz
      have hdiZero : (d i : ℚ) = 0 := by simpa [hz] using hq
      exact hdiQ hdiZero
    letI : Fact p.Prime := ⟨hp⟩
    have hvi : padicValRat p (d i : ℚ) = ((d i).factorization p : ℤ) := by
      rw [padicValRat.of_nat, ← Nat.factorization_def (d i) hp]
    have hvj : padicValRat p (d j : ℚ) = ((d j).factorization p : ℤ) := by
      rw [padicValRat.of_nat, ← Nat.factorization_def (d j) hp]
    have hval := congrArg (padicValRat p) hq
    rw [padicValRat.mul (pow_ne_zero _ hq0) hdjQ,
      padicValRat.pow, hvi, hvj, hvjZero] at hval
    omega
  have not_sixth_of_not_cube (a b : ℕ) (hb : b ≠ 0)
      (hnot : ¬∃ q : ℚ, (a : ℚ) = q ^ 3 * (b : ℚ)) :
      ¬∃ q : ℚ, ((a : ℚ) ^ 2) / ((b : ℚ) ^ 2) = q ^ 6 := by
    rintro ⟨q, hq⟩
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have hsq : ((a : ℚ) / (b : ℚ)) ^ 2 = (q ^ 3) ^ 2 := by
      rw [div_pow]
      calc
        (a : ℚ) ^ 2 / (b : ℚ) ^ 2 = q ^ 6 := hq
        _ = (q ^ 3) ^ 2 := by ring
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with heq | heq
    · apply hnot
      refine ⟨q, ?_⟩
      simpa [mul_comm] using (div_eq_iff hbq).mp heq
    · apply hnot
      refine ⟨-q, ?_⟩
      have heq' : (a : ℚ) / (b : ℚ) = (-q) ^ 3 := by
        calc
          _ = -(q ^ 3) := heq
          _ = (-q) ^ 3 := by ring
      simpa [mul_comm] using (div_eq_iff hbq).mp heq'
  have hclasses (i : ℕ) (hi : 1 ≤ i) (hij : i ≠ j) :
      (¬∃ q : ℚ, (d i : ℚ) = q ^ 3 * (d j : ℚ)) ∧
      (¬∃ q : ℚ,
        ((-3 : ℚ) * (d i : ℚ) ^ 2) /
          ((-3 : ℚ) * (d j : ℚ) ^ 2) = q ^ 6) ∧
      (¬∃ q : ℚ,
        ((125 : ℚ) * (d i : ℚ) ^ 2) /
          ((125 : ℚ) * (d j : ℚ) ^ 2) = q ^ 6) := by
    have hnot := hclass i hi hij
    have hsix := not_sixth_of_not_cube (d i) (d j) (hd0 j) hnot
    have hminus : ¬∃ q : ℚ,
        ((-3 : ℚ) * (d i : ℚ) ^ 2) /
          ((-3 : ℚ) * (d j : ℚ) ^ 2) = q ^ 6 := by
      rintro ⟨q, hq⟩
      apply hsix
      refine ⟨q, ?_⟩
      have hdjQ : (d j : ℚ) ≠ 0 := by exact_mod_cast hd0 j
      field_simp at hq ⊢
      nlinarith [hq]
    have hplus : ¬∃ q : ℚ,
        ((125 : ℚ) * (d i : ℚ) ^ 2) /
          ((125 : ℚ) * (d j : ℚ) ^ 2) = q ^ 6 := by
      rintro ⟨q, hq⟩
      apply hsix
      refine ⟨q, ?_⟩
      have hdjQ : (d j : ℚ) ≠ 0 := by exact_mod_cast hd0 j
      field_simp at hq ⊢
      nlinarith [hq]
    exact ⟨hnot, hminus, hplus⟩
  exact ⟨hminusElliptic, hplusElliptic,
    hminusUnscaledElliptic, hplusUnscaledElliptic,
    hscaled.1, hscaled.2,
    by simpa [B, x] using hunscaled.1,
    by simpa [B, f] using hunscaled.2,
    hclasses⟩

#print axioms actual_cubic_twists

end D5.S3.Factorization.Mordell.GoldenCubicBlockMordellTwists
