/- GID: D5/S3/Arith/FibonacciAtomic/UnitShiftNormBudget
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/UnitShiftNormBudget
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual coordinate gcd normalization gives cubic shift costs and joint growth budgets. -/

import D5.S1.Scale.Fibonacci
import D5.S1.Scale.Embedding
import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.UnitShiftNormBudget

open Filter
open D5.S0.Carrier
open D5.S1.Scale
open GraftAffineClosure (quantity)

local notation "φ" => Real.goldenRatio
local notation "ψ" => Real.goldenConj

/-- Absorb the unit bit and translate along the kernel of the quantity. -/
def shiftedComposition (j g : ℕ) (r : ℤ) : GoldenInt :=
  ⟨g * (Nat.fib (j - 1) : ℤ) + 3 * r - 1,
    g * (Nat.fib j : ℤ) + 1 - 2 * r⟩

/-- The source quantity includes its unit bit. -/
def sourceQuantity (j g : ℕ) : ℕ :=
  g * quantity (Nat.fib (j - 1), Nat.fib j) + 1

/-- Divide the source quantity by the actual gcd of the translated coordinates. -/
noncomputable def primitiveQuantity (j g : ℕ) (r : ℤ) : ℝ :=
  sourceQuantity j g / (Int.gcd (shiftedComposition j g r).a
    (shiftedComposition j g r).b : ℝ)

/-- Normalize the actual golden norm by the square of the coordinate gcd. -/
noncomputable def primitiveNorm (j g : ℕ) (r : ℤ) : ℝ :=
  |(norm (shiftedComposition j g r) : ℝ)| /
    (Int.gcd (shiftedComposition j g r).a (shiftedComposition j g r).b : ℝ) ^ 2

private theorem polynomial_ne_zero (g r s : ℤ) (hg : 2 ≤ g)
    (hs : s = 1 ∨ s = -1) : r ^ 2 - 3 * r + 1 + g ^ 2 * s ≠ 0 := by
  intro hz
  rcases hs with rfl | rfl
  · nlinarith [sq_nonneg (2 * r - 3), sq_nonneg (g - 2)]
  · have hlo : 2 * g < |2 * r - 3| := by
      nlinarith [sq_abs (2 * r - 3), abs_nonneg (2 * r - 3)]
    have hhi : |2 * r - 3| < 2 * g + 1 := by
      nlinarith [sq_abs (2 * r - 3), abs_nonneg (2 * r - 3)]
    omega


private theorem gcd_bound (A B g r : ℤ) (hg : 2 ≤ g)
    (hQ : A ^ 2 + A * B - B ^ 2 = 1 ∨ A ^ 2 + A * B - B ^ 2 = -1) :
    (Int.gcd (g * A + 3 * r - 1) (g * B + 1 - 2 * r) : ℝ) ≤
      ((g : ℝ) ^ 2 + 1) * (1 + |(r : ℝ)|) ^ 2 := by
  let a := g * A + 3 * r - 1
  let b := g * B + 1 - 2 * r
  let d := Int.gcd a b
  let P := r ^ 2 - 3 * r + 1 + g ^ 2 * (A ^ 2 + A * B - B ^ 2)
  have hP : P ≠ 0 := polynomial_ne_zero g r _ hg hQ
  have identity : P = a * (a + b - 4 * r + 1) + b * (-b - 7 * r + 3) := by
    dsimp [P, a, b]; ring
  have divides : (d : ℤ) ∣ P := by
    rw [identity]
    exact dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left a b) _)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right a b) _)
  have hdP : (d : ℝ) ≤ |(P : ℝ)| := by
    have hn := Int.natAbs_le_of_dvd_ne_zero divides hP
    simpa only [Int.natAbs_natCast, Nat.cast_natAbs, Int.cast_abs] using
      (show ((d : ℤ).natAbs : ℝ) ≤ (P.natAbs : ℝ) by exact_mod_cast hn)
  have gtwo : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have Qreal : (A : ℝ) ^ 2 + A * B - B ^ 2 = 1 ∨
      (A : ℝ) ^ 2 + A * B - B ^ 2 = -1 := by exact_mod_cast hQ
  have hpoly : |(P : ℝ)| ≤ (r : ℝ) ^ 2 + 3 * |(r : ℝ)| + 1 + (g : ℝ) ^ 2 := by
    dsimp [P]
    push_cast
    rcases Qreal with h | h <;> rw [h] <;> apply abs_le.mpr <;>
      constructor <;> nlinarith [le_abs_self (r : ℝ), neg_le_abs (r : ℝ),
        sq_nonneg (r : ℝ), sq_nonneg (g : ℝ)]
  have hlast : (r : ℝ) ^ 2 + 3 * |(r : ℝ)| + 1 + (g : ℝ) ^ 2 ≤
      ((g : ℝ) ^ 2 + 1) * (1 + |(r : ℝ)|) ^ 2 := by
    have gs : (4 : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
    nlinarith [sq_abs (r : ℝ), abs_nonneg (r : ℝ),
      mul_nonneg (show 0 ≤ (g : ℝ) ^ 2 by positivity) (sq_nonneg |(r : ℝ)|),
      mul_nonneg (show 0 ≤ 2 * (g : ℝ) ^ 2 - 1 by linarith) (abs_nonneg (r : ℝ))]
  exact hdP.trans (hpoly.trans hlast)

private theorem norm_lower (A B g r : ℤ)
    (hw : g * ((A : ℝ) + B * ψ) ∈ Set.Ioo (-1) (φ - 1))
    (ha : 0 ≤ g * A + 3 * r - 1) (hb : 0 ≤ g * B + 1 - 2 * r)
    (hN : 0 < g * (2 * A + 3 * B) + 1) :
    (g * (2 * (A : ℝ) + 3 * B) + 1) * (1 + |(r : ℝ)|) / 4 <
      |(norm (⟨g * A + 3 * r - 1, g * B + 1 - 2 * r⟩ : GoldenInt) : ℝ)| := by
  let y : GoldenInt := ⟨g * A + 3 * r - 1, g * B + 1 - 2 * r⟩
  let N : ℝ := g * (2 * (A : ℝ) + 3 * B) + 1
  let w : ℝ := g * ((A : ℝ) + B * ψ)
  have ph : (3 / 2 : ℝ) < φ := by
    nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
  have minus : embedding (conj y) = w - φ + (r : ℝ) * (2 * φ + 1) := by
    simp only [embedding_apply, conj, y]
    push_cast
    dsimp [w]
    rw [← Real.one_sub_goldenConj]
    ring
  have conjugate : (1 + |(r : ℝ)|) / 2 < |embedding (conj y)| := by
    rw [minus]
    by_cases hr : r ≤ 0
    · have hrR : (r : ℝ) ≤ 0 := by exact_mod_cast hr
      rw [abs_of_nonpos hrR]
      have wupper : w < φ - 1 := hw.2
      have hnegative : w - φ + (r : ℝ) * (2 * φ + 1) < 0 := by
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hrR (by linarith : 0 ≤ 2 * φ + 1)]
      rw [abs_of_neg hnegative]
      nlinarith [mul_nonneg (neg_nonneg.mpr hrR) (show 0 ≤ φ by linarith)]
    · have hrR : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
      rw [abs_of_nonneg (by linarith : 0 ≤ (r : ℝ))]
      have wlower : -1 < w := hw.1
      have hpositive : 0 < w - φ + (r : ℝ) * (2 * φ + 1) := by
        nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) - 1 by linarith)
          (show 0 ≤ φ by linarith)]
      rw [abs_of_pos hpositive]
      nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) - 1 by linarith)
        (show 0 ≤ 2 * φ - 1 / 2 by linarith)]
  have apositive : (0 : ℝ) ≤ y.a := by exact_mod_cast ha
  have bpositive : (0 : ℝ) ≤ y.b := by exact_mod_cast hb
  have quantity_y : N = 2 * (y.a : ℝ) + 3 * y.b := by
    dsimp [N, y]; push_cast; ring
  have Npositive : 0 < N := by dsimp only [N]; exact_mod_cast hN
  have plus : N / 2 ≤ embedding y := by
    rw [embedding_apply, quantity_y]
    nlinarith [mul_nonneg bpositive (show 0 ≤ φ - 3 / 2 by linarith)]
  rw [← abs_embedding_mul_abs_conj y,
    abs_of_pos (lt_of_lt_of_le (by linarith : 0 < N / 2) plus)]
  have prod := mul_lt_mul_of_pos_left conjugate (lt_of_lt_of_le
    (by linarith : 0 < N / 2) plus)
  have small := mul_le_mul_of_nonneg_right plus
    (show 0 ≤ (1 + |(r : ℝ)|) / 2 by positivity)
  calc
    _ = (N / 2) * ((1 + |(r : ℝ)|) / 2) := by dsimp only [N]; ring
    _ ≤ embedding y * ((1 + |(r : ℝ)|) / 2) := small
    _ < embedding y * |embedding (conj y)| := prod


private theorem source_bounds (j g : ℕ) (r : ℤ) (hj : 3 ≤ j) (hg : 2 ≤ g)
    (hw : (g : ℝ) * ((Nat.fib (j - 1) : ℝ) + Nat.fib j * ψ) ∈
      Set.Ioo (-1) (φ - 1))
    (ha : 0 ≤ (shiftedComposition j g r).a)
    (hb : 0 ≤ (shiftedComposition j g r).b) :
    1 ≤ (sourceQuantity j g : ℝ) ∧
    0 < Int.gcd (shiftedComposition j g r).a (shiftedComposition j g r).b ∧
    (Int.gcd (shiftedComposition j g r).a (shiftedComposition j g r).b : ℝ) ≤
      ((g : ℝ) ^ 2 + 1) * (1 + |(r : ℝ)|) ^ 2 ∧
    (sourceQuantity j g : ℝ) * (1 + |(r : ℝ)|) / 4 <
      |(norm (shiftedComposition j g r) : ℝ)| := by
  have positive : 0 < sourceQuantity j g := by unfold sourceQuantity; omega
  have coords : phi ^ j =
      (⟨(Nat.fib (j - 1) : ℤ), (Nat.fib j : ℤ)⟩ : GoldenInt) := by
    simpa only [show j - 1 + 1 = j by omega] using golden_phi_pow_eq_fib_pair (j - 1)
  have Q : (Nat.fib (j - 1) : ℤ) ^ 2 + Nat.fib (j - 1) * Nat.fib j -
      (Nat.fib j : ℤ) ^ 2 = (-1 : ℤ) ^ j := by
    have h := norm_phi_pow j
    rw [coords] at h
    simpa only [D5.S0.Carrier.norm, pow_two] using h
  have signs : (-1 : ℤ) ^ j = 1 ∨ (-1 : ℤ) ^ j = -1 := by
    rcases Nat.even_or_odd j with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  have Nidentity : ((sourceQuantity j g : ℕ) : ℤ) =
      2 * (shiftedComposition j g r).a + 3 * (shiftedComposition j g r).b := by
    simp only [sourceQuantity, shiftedComposition, quantity]
    push_cast; ring
  have gcdpositive : 0 < Int.gcd (shiftedComposition j g r).a
      (shiftedComposition j g r).b := by
    apply Nat.pos_of_ne_zero
    intro hz
    obtain ⟨hza, hzb⟩ := Int.gcd_eq_zero_iff.mp hz
    rw [hza, hzb] at Nidentity
    have : (sourceQuantity j g : ℤ) = 0 := by simpa using Nidentity
    exact (show (sourceQuantity j g : ℤ) ≠ 0 by exact_mod_cast positive.ne') this
  refine ⟨by exact_mod_cast positive, gcdpositive, ?_, ?_⟩
  · exact gcd_bound _ _ g r (by exact_mod_cast hg) (Q ▸ signs)
  · have lower := norm_lower (Nat.fib (j - 1)) (Nat.fib j) g r hw ha hb (by
      simpa only [sourceQuantity, quantity, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast] using
        (show 0 < (sourceQuantity j g : ℤ) by exact_mod_cast positive))
    simpa only [sourceQuantity, quantity, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, Int.cast_natCast, shiftedComposition] using lower

private theorem cubic_bound (j g : ℕ) (r : ℤ)
    (hN : 1 ≤ (sourceQuantity j g : ℝ))
    (hd : 0 < Int.gcd (shiftedComposition j g r).a (shiftedComposition j g r).b)
    (hdb : (Int.gcd (shiftedComposition j g r).a (shiftedComposition j g r).b : ℝ) ≤
      ((g : ℝ) ^ 2 + 1) * (1 + |(r : ℝ)|) ^ 2)
    (hQ : (sourceQuantity j g : ℝ) * (1 + |(r : ℝ)|) / 4 <
      |(norm (shiftedComposition j g r) : ℝ)|) :
    (sourceQuantity j g : ℝ) /
      (4 * ((g : ℝ) ^ 2 + 1) ^ 2 * (1 + |(r : ℝ)|) ^ 3) < primitiveNorm j g r := by
  let N : ℝ := sourceQuantity j g
  let d : ℝ := Int.gcd (shiftedComposition j g r).a (shiftedComposition j g r).b
  let C : ℝ := (g : ℝ) ^ 2 + 1
  let R : ℝ := 1 + |(r : ℝ)|
  have dp : 0 < d := by dsimp only [d]; exact_mod_cast hd
  have Cp : 0 < C := by dsimp [C]; positivity
  have Rp : 0 < R := by dsimp [R]; positivity
  have dsq : d ^ 2 ≤ C ^ 2 * R ^ 4 := by
    calc
      d ^ 2 ≤ (C * R ^ 2) ^ 2 := by gcongr
      _ = C ^ 2 * R ^ 4 := by ring
  unfold primitiveNorm
  apply (div_lt_div_iff₀ (by positivity) (by positivity : 0 < d ^ 2)).mpr
  calc
    N * d ^ 2 ≤ N * (C ^ 2 * R ^ 4) := mul_le_mul_of_nonneg_left dsq (by dsimp [N]; linarith)
    _ = (N * R / 4) * (4 * C ^ 2 * R ^ 3) := by ring
    _ < |(norm (shiftedComposition j g r) : ℝ)| * (4 * C ^ 2 * R ^ 3) :=
      mul_lt_mul_of_pos_right hQ (by positivity)


private theorem power_bounds (N G R d D α β : ℝ)
    (hN : 1 ≤ N) (hG : 2 ≤ G) (hR : 1 ≤ R) (hd : 0 < d)
    (hdb : d ≤ (G ^ 2 + 1) * R ^ 2)
    (hD : N / (4 * (G ^ 2 + 1) ^ 2 * R ^ 3) < D)
    (hβ : 0 ≤ β) (hg : G ≤ N ^ α) (hr : R - 1 ≤ N ^ β) :
    N ^ (1 - 4 * α - 3 * β) / 50 < D ∧ N ^ (1 - 2 * α - 2 * β) / 5 ≤ N / d := by
  have Np : 0 < N := by linarith
  have Gp : 0 < G := by linarith
  have Rp : 0 < R := by linarith
  have ap : 0 < N ^ α := Real.rpow_pos_of_pos Np α
  have bp : 0 < N ^ β := Real.rpow_pos_of_pos Np β
  have b1 : 1 ≤ N ^ β := Real.one_le_rpow hN hβ
  have Rb : R ≤ 2 * N ^ β := by linarith
  have Gb : G ^ 2 + 1 ≤ (5 / 4 : ℝ) * (N ^ α) ^ 2 := by nlinarith
  have exponent (a b : ℝ) (m n : ℕ) :
      (N ^ a) ^ m * (N ^ b) ^ n = N ^ ((m : ℝ) * a + (n : ℝ) * b) := by
    rw [Real.rpow_add Np, mul_comm (m : ℝ) a, mul_comm (n : ℝ) b,
      Real.rpow_mul_natCast Np.le, Real.rpow_mul_natCast Np.le]
  have denominator : 4 * (G ^ 2 + 1) ^ 2 * R ^ 3 ≤ 50 * N ^ (4 * α + 3 * β) := by
    calc
      4 * (G ^ 2 + 1) ^ 2 * R ^ 3 ≤
          4 * ((5 / 4 : ℝ) * (N ^ α) ^ 2) ^ 2 * (2 * N ^ β) ^ 3 := by gcongr
      _ = 50 * ((N ^ α) ^ 4 * (N ^ β) ^ 3) := by ring
      _ = 50 * N ^ (4 * α + 3 * β) := by rw [exponent α β 4 3]; norm_num
  have dbudget : d ≤ 5 * N ^ (2 * α + 2 * β) := by
    calc
      d ≤ (G ^ 2 + 1) * R ^ 2 := hdb
      _ ≤ ((5 / 4 : ℝ) * (N ^ α) ^ 2) * (2 * N ^ β) ^ 2 := by gcongr
      _ = 5 * ((N ^ α) ^ 2 * (N ^ β) ^ 2) := by ring
      _ = 5 * N ^ (2 * α + 2 * β) := by rw [exponent α β 2 2]; norm_num
  have quotient (k t : ℝ) : N ^ (1 - t) / k = N / (k * N ^ t) := by
    rw [Real.rpow_sub Np, Real.rpow_one]; ring
  constructor
  · rw [show 1 - 4 * α - 3 * β = 1 - (4 * α + 3 * β) by ring, quotient]
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left Np.le (by positivity) denominator) hD
  · rw [show 1 - 2 * α - 2 * β = 1 - (2 * α + 2 * β) by ring, quotient]
    exact div_le_div_of_nonneg_left Np.le hd dbudget

private theorem logarithmic_tail (ε δ ω : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hω : 0 < ω) :
    ∃ T : ℝ, ∀ N D U : ℝ, T ≤ N → N ^ ε / 50 < D → N ^ δ / 5 ≤ U → U ≤ N →
      (Real.log (Real.log (Real.log U))) ^ ω < Real.log (Real.log (2 + D)) := by
  have ht : Tendsto (fun N : ℝ => Real.log (Real.log N)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hs := ((isLittleO_log_rpow_rpow_atTop ω (by norm_num : 0 < (1 : ℝ))).comp_tendsto ht).bound
    (by norm_num : 0 < (1 / 4 : ℝ))
  simp only [Function.comp_apply, Real.rpow_one] at hs
  have event : ∀ᶠ N : ℝ in Filter.atTop, ∀ D U : ℝ,
      N ^ ε / 50 < D → N ^ δ / 5 ≤ U → U ≤ N →
      (Real.log (Real.log (Real.log U))) ^ ω < Real.log (Real.log (2 + D)) := by
    filter_upwards [hs, Filter.eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_gt_atTop (max 0 (2 * Real.log 50 / ε)),
      ht.eventually_gt_atTop (max 1 (-2 * Real.log (ε / 2))),
      (tendsto_rpow_atTop hδ).eventually_ge_atTop (5 * Real.exp (Real.exp 1))]
      with N hsmall Np hln hll hUbig
    intro D U hD hU hUN
    have lnpos : 0 < Real.log N := lt_of_le_of_lt (le_max_left _ _) hln
    have lnlarge : 2 * Real.log 50 / ε < Real.log N := lt_of_le_of_lt (le_max_right _ _) hln
    have llpos : 0 < Real.log (Real.log N) := by
      have := lt_of_le_of_lt (le_max_left _ _) hll; linarith
    have lllarge : -2 * Real.log (ε / 2) < Real.log (Real.log N) :=
      lt_of_le_of_lt (le_max_right _ _) hll
    have Up : 0 < U := lt_of_lt_of_le (Real.exp_pos _) (show Real.exp (Real.exp 1) ≤ U by linarith)
    have logU : Real.exp 1 ≤ Real.log U := by
      have := Real.log_le_log (Real.exp_pos (Real.exp 1))
        (show Real.exp (Real.exp 1) ≤ U by linarith)
      simpa only [Real.log_exp] using this
    have loglogU : 1 ≤ Real.log (Real.log U) := by
      have := Real.log_le_log (Real.exp_pos 1) logU
      simpa only [Real.log_exp] using this
    have tripleU : 0 ≤ Real.log (Real.log (Real.log U)) := Real.log_nonneg loglogU
    have logUp : 0 < Real.log U := lt_of_lt_of_le (Real.exp_pos 1) logU
    have llUp : 0 < Real.log (Real.log U) := by linarith
    have triplele : Real.log (Real.log (Real.log U)) ≤ Real.log (Real.log (Real.log N)) :=
      Real.log_le_log llUp (Real.log_le_log logUp (Real.log_le_log Up hUN))
    have rhs : (Real.log (Real.log (Real.log U))) ^ ω ≤ Real.log (Real.log N) / 4 := by
      have small : (Real.log (Real.log (Real.log N))) ^ ω ≤ Real.log (Real.log N) / 4 := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (tripleU.trans triplele) ω),
          abs_of_pos llpos, div_eq_mul_inv, one_mul, mul_comm] using hsmall
      exact (Real.rpow_le_rpow tripleU triplele hω.le).trans small
    have Dp : 0 < D := lt_trans (by positivity : 0 < N ^ ε / 50) hD
    have logD : ε * Real.log N - Real.log 50 < Real.log (2 + D) := by
      calc
        _ = Real.log (N ^ ε / 50) := by
          rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow Np]
        _ < Real.log (2 + D) := Real.log_lt_log (by positivity) (by linarith)
    have inner : (ε / 2) * Real.log N < Real.log (2 + D) := by
      have := (div_lt_iff₀ hε).mp lnlarge
      nlinarith
    have lower : Real.log (Real.log N) + Real.log (ε / 2) < Real.log (Real.log (2 + D)) := by
      calc
        _ = Real.log ((ε / 2) * Real.log N) := by
          rw [Real.log_mul (by positivity) lnpos.ne']; ring
        _ < _ := Real.log_lt_log (by positivity) inner
    linarith
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp event
  exact ⟨T, fun N D U hTN => hT N hTN D U⟩

/-- Actual nonnegative shifts obey a cubic cost and joint multiplier/shift power budgets. -/
private theorem pointwise (j g : ℕ) (r : ℤ) (hj : 3 ≤ j) (hg : 2 ≤ g)
    (hw : (g : ℝ) * ((Nat.fib (j - 1) : ℝ) + Nat.fib j * ψ) ∈
      Set.Ioo (-1) (φ - 1))
    (ha : 0 ≤ (shiftedComposition j g r).a)
    (hb : 0 ≤ (shiftedComposition j g r).b) :
    (sourceQuantity j g : ℝ) /
      (4 * ((g : ℝ) ^ 2 + 1) ^ 2 * (1 + |(r : ℝ)|) ^ 3) < primitiveNorm j g r ∧
    ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → 4 * α + 3 * β < 1 →
      (g : ℝ) ≤ (sourceQuantity j g : ℝ) ^ α →
      |(r : ℝ)| ≤ (sourceQuantity j g : ℝ) ^ β →
      (sourceQuantity j g : ℝ) ^ (1 - 4 * α - 3 * β) / 50 < primitiveNorm j g r ∧
      (sourceQuantity j g : ℝ) ^ (1 - 2 * α - 2 * β) / 5 ≤ primitiveQuantity j g r := by
  obtain ⟨hN, hd, hdb, hQ⟩ := source_bounds j g r hj hg hw ha hb
  have cubic := cubic_bound j g r hN hd hdb hQ
  refine ⟨cubic, ?_⟩
  intro α β _ hβ _ hgrowth hr
  exact power_bounds _ _ _ _ _ α β hN (by exact_mod_cast hg)
    (by have := abs_nonneg (r : ℝ); linarith) (by exact_mod_cast hd)
    hdb cubic hβ hgrowth (by simpa only [add_sub_cancel_left] using hr)


/-- Cubic costs, joint power budgets, and a source-independent logarithmic threshold. -/
theorem result :
    (∀ (j g : ℕ) (r : ℤ), 3 ≤ j → 2 ≤ g →
      (g : ℝ) * ((Nat.fib (j - 1) : ℝ) + Nat.fib j * ψ) ∈ Set.Ioo (-1) (φ - 1) →
      0 ≤ (shiftedComposition j g r).a → 0 ≤ (shiftedComposition j g r).b →
      (sourceQuantity j g : ℝ) /
        (4 * ((g : ℝ) ^ 2 + 1) ^ 2 * (1 + |(r : ℝ)|) ^ 3) < primitiveNorm j g r ∧
      ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → 4 * α + 3 * β < 1 →
        (g : ℝ) ≤ (sourceQuantity j g : ℝ) ^ α →
        |(r : ℝ)| ≤ (sourceQuantity j g : ℝ) ^ β →
        (sourceQuantity j g : ℝ) ^ (1 - 4 * α - 3 * β) / 50 < primitiveNorm j g r ∧
        (sourceQuantity j g : ℝ) ^ (1 - 2 * α - 2 * β) / 5 ≤ primitiveQuantity j g r) ∧
    (∀ α β : ℝ, 0 ≤ α → 0 ≤ β → 4 * α + 3 * β < 1 →
      ∀ M : ℝ, ∃ T : ℝ, ∀ (j g : ℕ) (r : ℤ), 3 ≤ j → 2 ≤ g →
        (g : ℝ) * ((Nat.fib (j - 1) : ℝ) + Nat.fib j * ψ) ∈ Set.Ioo (-1) (φ - 1) →
        0 ≤ (shiftedComposition j g r).a → 0 ≤ (shiftedComposition j g r).b →
        (g : ℝ) ≤ (sourceQuantity j g : ℝ) ^ α →
        |(r : ℝ)| ≤ (sourceQuantity j g : ℝ) ^ β → T ≤ (sourceQuantity j g : ℝ) →
        M ≤ primitiveQuantity j g r) ∧
    (∀ α β : ℝ, 0 ≤ α → 0 ≤ β → 4 * α + 3 * β < 1 →
      ∀ ω : ℝ, 0 < ω → ω < 1 / 2 → ∃ T : ℝ, ∀ (j g : ℕ) (r : ℤ),
        3 ≤ j → 2 ≤ g →
        (g : ℝ) * ((Nat.fib (j - 1) : ℝ) + Nat.fib j * ψ) ∈ Set.Ioo (-1) (φ - 1) →
        0 ≤ (shiftedComposition j g r).a → 0 ≤ (shiftedComposition j g r).b →
        (g : ℝ) ≤ (sourceQuantity j g : ℝ) ^ α →
        |(r : ℝ)| ≤ (sourceQuantity j g : ℝ) ^ β → T ≤ (sourceQuantity j g : ℝ) →
        (Real.log (Real.log (Real.log (primitiveQuantity j g r)))) ^ ω <
          Real.log (Real.log (2 + primitiveNorm j g r))) := by
  refine ⟨pointwise, ?_, ?_⟩
  · intro α β hα hβ hsum M
    have δpositive : 0 < 1 - 2 * α - 2 * β := by linarith
    obtain ⟨T, hT⟩ := eventually_atTop.mp
      ((tendsto_rpow_atTop δpositive).eventually_ge_atTop (5 * M))
    refine ⟨T, ?_⟩
    intro j g r hj hg hw ha hb hgrowth hr hTN
    have lower := ((pointwise j g r hj hg hw ha hb).2 α β hα hβ hsum hgrowth hr).2
    have atThreshold := hT (sourceQuantity j g : ℝ) hTN
    exact (show M ≤ (sourceQuantity j g : ℝ) ^ (1 - 2 * α - 2 * β) / 5 by linarith).trans lower
  · intro α β hα hβ hsum ω hω _
    obtain ⟨T, hT⟩ := logarithmic_tail (1 - 4 * α - 3 * β) (1 - 2 * α - 2 * β) ω
      (by linarith) (by linarith) hω
    refine ⟨T, ?_⟩
    intro j g r hj hg hw ha hb hgrowth hr hTN
    obtain ⟨hN, hd, _, _⟩ := source_bounds j g r hj hg hw ha hb
    obtain ⟨hD, hU⟩ := (pointwise j g r hj hg hw ha hb).2 α β hα hβ hsum hgrowth hr
    have upper : primitiveQuantity j g r ≤ (sourceQuantity j g : ℝ) := by
      unfold primitiveQuantity
      exact div_le_self (by positivity) (by exact_mod_cast hd)
    exact hT _ _ _ hTN hD hU upper

end D5.S3.Arith.FibonacciAtomic.UnitShiftNormBudget
