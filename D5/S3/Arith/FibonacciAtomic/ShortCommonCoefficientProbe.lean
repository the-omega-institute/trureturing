/- GID: D5/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ShortCommonCoefficientProbe
   mirror-E: none(waiver:uniform-bounded-coefficient-pairs)
   anchors: [D5/S3/Analytic/GoldenEulerBetaZeckendorf]
   utility: none
   digest: Every modular coefficient pair has a positive bounded Zeckendorf representative. -/

import D5.S3.Analytic.GoldenEulerBetaZeckendorf
import Mathlib.Algebra.Order.Round
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe

open D5.S3.Analytic.GoldenEulerBetaZeckendorf

noncomputable section

/-- First Fibonacci number strictly larger than twice the modulus. -/
def firstIndex (H : Nat) : Nat := Nat.find (show ∃ j, 2 * H < Nat.fib j from by
  refine ⟨2 * H + 5, ?_⟩
  have h := Nat.le_fib_self (n := 2 * H + 5) (by omega)
  omega)

/-- The same positive integer realizes both prescribed coefficients; its
bound uses the first Fibonacci number above twice the modulus. -/
theorem bounded_coefficient_pair (H : Nat) (hH : 2 ≤ H) :
    let j := firstIndex H
    let q := Nat.fib j
    5 ≤ j ∧ 2 * H < q ∧ q < 4 * H ∧
      ∀ A B : ZMod H, ∃ n : Nat,
        H ≤ n ∧ n < H * (q + 1) ∧
        (n : ZMod H) = B ∧ (shiftedFibSum n : ZMod H) = A := by
  classical
  let j := firstIndex H
  let q := Nat.fib j
  have hjq : 2 * H < q := by
    change 2 * H < Nat.fib (firstIndex H)
    unfold firstIndex
    exact Nat.find_spec (p := fun k : Nat => 2 * H < Nat.fib k) _
  have hmin : ∀ k < j, Nat.fib k ≤ 2 * H := by
    intro k hk
    exact Nat.le_of_not_gt (Nat.find_min (p := fun k : Nat => 2 * H < Nat.fib k) _ hk)
  have hj5 : 5 ≤ j := by
    by_contra hn
    have hj4 : j ≤ 4 := by omega
    have hf := Nat.fib_mono hj4
    norm_num at hf
    omega
  have hjprev : Nat.fib (j - 1) ≤ 2 * H := hmin _ (by omega)
  have hstrict : Nat.fib (j - 2) < Nat.fib (j - 1) :=
    (Nat.fib_lt_fib (by omega)).2 (by omega)
  have hrec : q = Nat.fib (j - 1) + Nat.fib (j - 2) := by
    dsimp [q]
    calc
      Nat.fib j = Nat.fib ((j - 2) + 2) := congrArg Nat.fib (by omega)
      _ = Nat.fib (j - 1) + Nat.fib (j - 2) := by
        rw [Nat.fib_add_two, show j - 2 + 1 = j - 1 by omega]
        exact Nat.add_comm _ _
  have hq4 : q < 4 * H := by omega
  refine ⟨hj5, hjq, hq4, ?_⟩
  let φ := Real.goldenRatio
  let α := φ⁻¹
  have hφ : 0 < φ := Real.goldenRatio_pos
  have hφ1 : 1 < φ := Real.one_lt_goldenRatio
  have hφsq : φ ^ 2 = φ + 1 := Real.goldenRatio_sq
  have hφhalf : (3 / 2 : Real) < φ := by nlinarith
  have hupper : ∀ k : Nat, (Nat.fib (k + 2) : Real) < φ ^ (k + 2) / 2 := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => norm_num [Nat.fib]; nlinarith
    | one =>
      norm_num [Nat.fib]
      rw [pow_succ, hφsq]
      nlinarith
    | more k ih₀ ih₁ =>
      have hp : φ ^ (k + 4) = φ ^ (k + 3) + φ ^ (k + 2) := by
        have hx := Real.goldenRatio_pow_sub_goldenRatio_pow (k + 2)
        rw [show k + 2 + 2 = k + 4 by omega,
          show k + 2 + 1 = k + 3 by omega] at hx
        linarith only [hx]
      rw [show k + 2 + 2 = (k + 2) + 2 by omega, Nat.fib_add_two, Nat.cast_add]
      rw [show k + 2 + 2 = k + 4 by omega, hp]
      have h₁ : (Nat.fib (k + 2 + 1) : Real) < φ ^ (k + 3) / 2 := by
        simpa [Nat.add_assoc] using ih₁
      linarith
  have hqR : 0 < (q : Real) := by exact_mod_cast (show 0 < q by omega)
  have hsmall : (q : Real) * α ^ j < 1 / 2 := by
    have hu := hupper (j - 2)
    rw [show j - 2 + 2 = j by omega] at hu
    have hm := mul_lt_mul_of_pos_right hu (inv_pos.mpr (pow_pos hφ j))
    have heq : φ ^ j / 2 * (φ ^ j)⁻¹ = (1 / 2 : Real) := by
      field_simp
    rw [heq] at hm
    simpa [q, α, inv_pow] using hm
  let p := Nat.fib (j - 1)
  have hcop : IsCoprime (p : Int) (q : Int) := by
    apply Nat.Coprime.isCoprime
    simpa [p, q, show j - 1 + 1 = j by omega] using Nat.fib_coprime_fib_succ (j - 1)
  have herr : |(q : Real) * α - p| = α ^ j := by
    have hg := Real.goldenConj_mul_fib_succ_add_fib (j - 1)
    rw [show j - 1 + 1 = j by omega] at hg
    have heq : (q : Real) * α - p = -Real.goldenConj ^ j := by
      dsimp [q, p, α, φ]
      rw [Real.inv_goldenRatio]
      linarith
    rw [heq, abs_neg, abs_pow]
    congr 1
    dsimp [α, φ]
    rw [abs_of_neg Real.goldenConj_neg, Real.inv_goldenRatio]
  have happ : |α - (p : Real) / q| < 1 / (2 * (q : Real) ^ 2) := by
    have heq : α - (p : Real) / q = ((q : Real) * α - p) / q := by
      field_simp
    rw [heq, abs_div, abs_of_pos hqR, herr]
    apply (div_lt_iff₀ hqR).2
    rw [show 1 / (2 * (q : Real) ^ 2) * q = 1 / (2 * (q : Real)) by field_simp]
    apply (lt_div_iff₀ (by positivity : 0 < 2 * (q : Real))).2
    nlinarith only [hsmall]
  intro A B
  let : NeZero H := ⟨by omega⟩
  let a := A.val
  let b := B.val
  have ha : a < H := ZMod.val_lt A
  have hb : b < H := ZMod.val_lt B
  let θ : Real := ((b : Real) + 1) * α / H
  let x : Real := ((a : Real) + 1 / 2) / H
  let k : Int := round ((q : Real) * (x - θ))
  obtain ⟨r, s, hrs⟩ := hcop
  let d : Int := (k * r - 1) / q
  let t : Int := (k * r - 1) % q + 1
  have hqI : 0 < (q : Int) := by exact_mod_cast hqR
  have ht0 : 0 < t := by
    dsimp [t]
    have he := Int.emod_nonneg (k * r - 1) hqI.ne'
    omega
  have htq : t ≤ q := by
    dsimp [t]
    have he := Int.emod_lt_of_pos (k * r - 1) hqI
    omega
  have ht : t = k * r - (q : Int) * d := by
    have hd := Int.emod_add_mul_ediv (k * r - 1) (q : Int)
    dsimp [t, d]
    nlinarith
  let z : Int := -(k * s) - (p : Int) * d
  have htz : t * (p : Int) = k + (q : Int) * z := by
    dsimp [z]
    rw [ht]
    nlinarith [congrArg (fun v : Int => k * v) hrs]
  have htzR : (t : Real) * p = (k : Real) + (q : Real) * z := by
    exact_mod_cast htz
  have hgrid : |x - (θ + (t : Real) * p / q - z)| ≤ 1 / (2 * (q : Real)) := by
    have hrnd := abs_sub_round ((q : Real) * (x - θ))
    have heq : x - (θ + (t : Real) * p / q - z) =
        ((q : Real) * (x - θ) - k) / q := by
      apply (eq_div_iff hqR.ne').2
      field_simp at *
      nlinarith [htzR]
    rw [heq, abs_div, abs_of_pos hqR]
    apply (div_le_iff₀ hqR).2
    dsimp [k] at *
    convert hrnd using 1
    field_simp
  have htR : 0 < (t : Real) := by exact_mod_cast ht0
  have htqR : (t : Real) ≤ q := by exact_mod_cast htq
  have hpert : |(t : Real) * (α - (p : Real) / q)| < 1 / (2 * (q : Real)) := by
    rw [abs_mul, abs_of_pos htR]
    calc
      (t : Real) * |α - (p : Real) / q| <
          (t : Real) * (1 / (2 * (q : Real) ^ 2)) := mul_lt_mul_of_pos_left happ htR
      _ ≤ (q : Real) * (1 / (2 * (q : Real) ^ 2)) :=
        mul_le_mul_of_nonneg_right htqR (by positivity)
      _ = 1 / (2 * (q : Real)) := by field_simp
  have hdist : |x - (θ + (t : Real) * α - z)| < 1 / (q : Real) := by
    have htriangle := abs_add_le
      (x - (θ + (t : Real) * p / q - z))
      (-((t : Real) * (α - (p : Real) / q)))
    have heq : x - (θ + (t : Real) * α - z) =
        (x - (θ + (t : Real) * p / q - z)) -
        (t : Real) * (α - (p : Real) / q) := by ring
    rw [heq]
    rw [abs_neg] at htriangle
    calc
      |(x - (θ + (t : Real) * p / q - z)) - (t : Real) * (α - (p : Real) / q)|
          ≤ |x - (θ + (t : Real) * p / q - z)| +
            |(t : Real) * (α - (p : Real) / q)| := by
              simpa only [sub_eq_add_neg] using htriangle
      _ < 1 / (2 * (q : Real)) + 1 / (2 * (q : Real)) :=
        add_lt_add_of_le_of_lt hgrid hpert
      _ = 1 / (q : Real) := by ring
  have hHR : 0 < (H : Real) := by exact_mod_cast (show 0 < H by omega)
  have hqHR : 2 * (H : Real) < q := by exact_mod_cast hjq
  have hradius : 1 / (q : Real) < 1 / (2 * (H : Real)) :=
    one_div_lt_one_div_of_lt (by positivity) hqHR
  have hball := abs_lt.mp (hdist.trans hradius)
  let n := b + H * t.toNat
  have hnlo : H ≤ n := by
    have htNat : 1 ≤ t.toNat := by omega
    dsimp [n]
    nlinarith
  have hnhi : n < H * (q + 1) := by
    have htNat : t.toNat ≤ q := by omega
    dsimp [n]
    nlinarith
  have hnR : (n : Real) = (b : Real) + (H : Real) * t := by
    dsimp [n]
    have htcast : (t.toNat : Real) = (t : Real) := by
      exact_mod_cast Int.toNat_of_nonneg ht0.le
    rw [Nat.cast_add, Nat.cast_mul, htcast]
  have hfloor : ⌊((n + 1 : Nat) : Real) / φ⌋ = (a : Int) + (H : Int) * z := by
    apply Int.floor_eq_iff.mpr
    have hx : (H : Real) * x = (a : Real) + 1 / 2 := by
      dsimp [x]
      field_simp
    have hθ : (H : Real) * θ = ((b : Real) + 1) * α := by
      dsimp [θ]
      field_simp
    have hnval : ((n + 1 : Nat) : Real) / φ =
        (H : Real) * (θ + (t : Real) * α - z) + (H : Real) * z := by
      rw [Nat.cast_add, Nat.cast_one, hnR]
      dsimp [α] at hθ ⊢
      rw [div_eq_mul_inv]
      linear_combination -hθ
    rw [hnval]
    push_cast
    have hleft := mul_lt_mul_of_pos_left hball.1 hHR
    have hright := mul_lt_mul_of_pos_left hball.2 hHR
    have hh : (H : Real) * (1 / (2 * (H : Real))) = 1 / 2 := by field_simp
    constructor <;> nlinarith only [hleft, hright, hx, hh]
  refine ⟨n, hnlo, hnhi, ?_, ?_⟩
  · dsimp [n]
    simp [b]
  · have hs := floor_succ_div_golden_eq_shifted (n := n) (by omega)
    change ⌊((n + 1 : Nat) : Real) / φ⌋ = _ at hs
    have hi : (shiftedFibSum n : Int) = (a : Int) + (H : Int) * z := hs.symm.trans hfloor
    have hc := congrArg (fun v : Int => (v : ZMod H)) hi
    simpa [a] using hc

#print axioms bounded_coefficient_pair

end
end D5.S3.Arith.FibonacciAtomic.ShortCommonCoefficientProbe
