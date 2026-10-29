/- GID: D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/PeriodicShorteningArithmetic
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Same-phase cross-modulus charges for periodic shortening. -/
import D5.S3.Combinatorics.Circle.GeometricSourceRelocation
import D5.S3.Combinatorics.Circle.TwoRunSource
import D5.S3.Combinatorics.Circle.ZeroSumSubsets
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Actual cross-modulus periodic charges -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
open SourceWidth
open scoped BigOperators

def geom (d r : ℕ) : ℕ := ((2 ^ d) ^ r - 1) / (2 ^ d - 1)

theorem geom_sum (d r : ℕ) (hd : 1 ≤ d) :
    (geom d r : ℤ) = ∑ j ∈ Finset.range r, ((2 : ℤ) ^ d) ^ j := by
  have h := GeometricSourceRelocation.geometric_quotient r d hd
  exact_mod_cast h

theorem geom_mul (d r : ℕ) (hd : 1 ≤ d) :
    ((2 : ℤ) ^ d - 1) * (geom d r : ℤ) = ((2 : ℤ) ^ d) ^ r - 1 := by
  rw [geom_sum d r hd, mul_comm]
  exact geom_sum_mul _ _

theorem geom_succ (d r : ℕ) (hd : 1 ≤ d) :
    (geom d (r + 1) : ℤ) = (geom d r : ℤ) + ((2 : ℤ) ^ d) ^ r := by
  simp only [geom_sum d _ hd, Finset.sum_range_succ]

/-- The charge belongs to the same physical phase as both source values. -/
def charge (d w : ℕ) (i : Fin d) : ℤ :=
  let z := (w : ℤ) / (2 : ℤ) ^ (d - 1 - i.val)
  z / 2 + z % 2

set_option maxHeartbeats 2000000 in
theorem digit_data (d w : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (i : Fin d) :
    0 ≤ charge d w i ∧
    actualSource d w i = (2 : ℤ) ^ i.val * w - ((2 : ℤ) ^ d - 1) * charge d w i ∧
    actualSource (d + 1) w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
      2 * actualSource d w i - charge d w i := by
  let s : ℤ := 2 ^ i.val
  let b : ℤ := 2 ^ (d - 1 - i.val)
  let z : ℤ := (w : ℤ) / b
  let l : ℤ := z / 2
  let c : ℤ := z % 2
  let v : ℤ := (w : ℤ) % b
  have hs : 1 ≤ s := one_le_pow₀ (by norm_num)
  have hb : 1 ≤ b := one_le_pow₀ (by norm_num)
  have hsb : s * b = (2 : ℤ) ^ (d - 1) := by
    dsimp [s, b]
    rw [← pow_add, show i.val + (d - 1 - i.val) = d - 1 by omega]
  have hq : (2 : ℤ) ^ d = 2 * s * b := by
    rw [mul_assoc, hsb, ← pow_succ', show d - 1 + 1 = d by omega]
  have hw' : (w : ℤ) < s * b := by
    rw [hsb]
    have hp : 1 ≤ (2 : ℕ) ^ (d - 1) := Nat.one_le_two_pow
    exact_mod_cast (show w < 2 ^ (d - 1) by omega)
  have hz : 0 ≤ z := Int.ediv_nonneg (Int.natCast_nonneg _) (by omega)
  have hl : 0 ≤ l := Int.ediv_nonneg hz (by norm_num)
  have hc : c = 0 ∨ c = 1 := by
    have := Int.emod_nonneg z (by norm_num : (2 : ℤ) ≠ 0)
    have := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 2)
    dsimp [c]; omega
  have hv : 0 ≤ v ∧ v < b :=
    ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have hwz : (w : ℤ) = b * z + v := by
    have := Int.emod_add_mul_ediv (w : ℤ) b
    dsimp [z, v]; nlinarith
  have hzl : z = 2 * l + c := by
    have := Int.emod_add_mul_ediv z 2
    dsimp [l, c]; omega
  have hc0 : 0 ≤ c := by omega
  have hzs : z < s := by nlinarith
  have hls : l < s := by omega
  have he : charge d w i = l + c := rfl
  let a := s * (w : ℤ) - (2 * s * b - 1) * (l + c)
  let y := 2 * s * (w : ℤ) - (4 * s * b - 1) * (l + c)
  have ha : a = s * v - s * b * c + l + c := by
    dsimp [a]; rw [hwz, hzl]; ring
  have hy : y = 2 * s * v - 2 * s * b * c + l + c := by
    dsimp [y]; rw [hwz, hzl]; ring
  have hNa : modulus d / 2 = s * b - 1 := by
    rw [modulus, hq]; ring_nf; omega
  have hNy : modulus (d + 1) / 2 = 2 * s * b - 1 := by
    rw [modulus, pow_succ, hq]; ring_nf; omega
  have harange : -(modulus d / 2) ≤ a ∧ a ≤ modulus d / 2 := by
    rw [hNa, ha]
    rcases hc with hc | hc <;> rw [hc] <;> constructor <;>
      nlinarith [mul_nonneg (by omega : 0 ≤ s) hv.1, mul_le_mul_of_nonneg_left (show v ≤ b - 1 by omega) (by omega : 0 ≤ s)]
  have hyrange : -(modulus (d + 1) / 2) ≤ y ∧ y ≤ modulus (d + 1) / 2 := by
    rw [hNy, hy]
    rcases hc with hc | hc <;> rw [hc] <;> constructor <;>
      nlinarith [mul_nonneg (by omega : 0 ≤ s) hv.1, mul_le_mul_of_nonneg_left (show v ≤ b - 1 by omega) (by omega : 0 ≤ s)]
  obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd d (by omega)
  obtain ⟨hN', ho'⟩ := TwoRunSource.modulus_positive_odd (d + 1) (by omega)
  have haeq : actualSource d w i = a := by
    apply centered_unique hN ho (centered_bounds hN ho _) harange
    rw [centered_mod]
    change (s * (w : ℤ)) % modulus d = a % modulus d
    have heq : a = s * (w : ℤ) - modulus d * (l + c) := by dsimp [a]; rw [modulus, hq]
    rw [heq, Int.sub_mul_emod_self_left]
  have hyeq : actualSource (d + 1) w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ = y := by
    apply centered_unique hN' ho' (centered_bounds hN' ho' _) hyrange
    rw [centered_mod]
    change ((2 : ℤ) ^ (i.val + 1) * w) % modulus (d + 1) = y % modulus (d + 1)
    have heq : y = 2 * s * (w : ℤ) - modulus (d + 1) * (l + c) := by
      dsimp [y]; rw [modulus, pow_succ, hq]; ring
    rw [heq, Int.sub_mul_emod_self_left, pow_succ]
    dsimp [s]; congr 1 <;> ring
  refine ⟨by rw [he]; rcases hc with h | h <;> omega, ?_, ?_⟩
  · rw [haeq, he, hq]
  · rw [haeq, hyeq, he]; dsimp [a, y]; ring


/-- Total charge in the native old-source phase. -/
theorem charge_sum (d w : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) :
    (∑ i : Fin d, charge d w i) = (w : ℤ) := by
  let q : ℤ := 2 ^ d
  let a := actualSource d w
  let e := charge d w
  have hq : 4 ≤ q := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hd
    norm_num at this; exact this
  have hdigit := digit_data d w hd hw
  have hasum : (∑ i : Fin d, a i) = 0 :=
    (ZeroSumSubsets.source_cycle (by omega : 0 < d) w).2.1
  have hpow : (∑ i : Fin d, (2 : ℤ) ^ i.val) = q - 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    have h := geom_sum_mul (2 : ℤ) d
    norm_num at h
    exact h
  have heq : (∑ i : Fin d, a i) =
      (∑ i : Fin d, (2 : ℤ) ^ i.val) * w - (q - 1) * ∑ i : Fin d, e i := by
    calc
      _ = ∑ i : Fin d, ((2 : ℤ) ^ i.val * w - (q - 1) * e i) :=
        Finset.sum_congr rfl (fun i _ => (hdigit i).2.1)
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hasum, hpow] at heq
  nlinarith


theorem geom_mono (d : ℕ) (hd : 1 ≤ d) {r m : ℕ} (hr : r ≤ m) :
    (geom d r : ℤ) ≤ (geom d m : ℤ) := by
  have hq : (2 : ℤ) ≤ 2 ^ d := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hd
    norm_num at this; exact this
  have hp := pow_le_pow_right₀ (by omega : (1 : ℤ) ≤ 2 ^ d) hr
  have h1 := geom_mul d r hd
  have h2 := geom_mul d m hd
  nlinarith

set_option maxHeartbeats 2000000 in
/-- Exact physical exponents and their nonnegative charges across all repeated blocks. -/
theorem periodic_source_equations
    (d w m : ℕ) (hd : 2 ≤ d) (hw : w ≤ 2 ^ (d - 1) - 1) (hm : 2 ≤ m) :
    let q : ℤ := 2 ^ d
    let G : ℤ := geom d m
    let H : ℤ := geom d (m - 1)
    let R : ℤ := q ^ (m - 1)
    let a : Fin d → ℤ := actualSource d w
    let e : Fin d → ℤ := charge d w
    let f : ℕ → Fin d → ℤ := fun r i => 2 ^ i.val * w * (geom d r : ℤ) + e i
    (∀ i, 0 ≤ e i ∧ a i = 2 ^ i.val * w - (q - 1) * e i ∧
      actualSource (d + 1) w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ = 2 * a i - e i) ∧
    (∑ i, e i) = w ∧
    actualSource (d * m + 1) (w * geom d m) ⟨0, by omega⟩ = (w * geom d m : ℕ) ∧
    actualSource (d + 1) w ⟨0, by omega⟩ = (w : ℤ) ∧
    (∀ r < m, ∀ i : Fin d, ∀ hp : r * d + i.val + 1 < d * m + 1,
      actualSource (d * m + 1) (w * geom d m) ⟨r * d + i.val + 1, hp⟩ =
        2 * G * a i - f r i) ∧
    (∀ r < m, (∑ i, f r i) = (w : ℤ) * q ^ r) ∧
    (∀ i : Fin d, ∀ hp : (m - 1) * d + i.val + 1 < d * m + 1,
      actualSource (d * m + 1) (w * geom d m) ⟨(m - 1) * d + i.val + 1, hp⟩ =
        R * actualSource (d + 1) w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ + H * a i) := by
  classical
  dsimp only
  let q : ℤ := 2 ^ d
  let G : ℤ := geom d m
  let a := actualSource d w
  let e := charge d w
  let f := fun r (i : Fin d) => (2 : ℤ) ^ i.val * w * (geom d r : ℤ) + e i
  have hd1 : 1 ≤ d := by omega
  have hq : 4 ≤ q := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hd
    norm_num at this; exact this
  have hqpow : q = 2 * (2 : ℤ) ^ (d - 1) := by
    dsimp [q]; conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
    ring
  have hB : modulus d / 2 = (2 : ℤ) ^ (d - 1) - 1 := by
    change (q - 1) / 2 = _
    rw [hqpow]; omega
  have hhalf : 2 * (modulus d / 2) = q - 2 := by rw [hB, hqpow]; ring
  have hN : modulus (d * m + 1) = 2 * q ^ m - 1 := by
    dsimp [modulus, q]; rw [pow_succ, pow_mul]; ring
  have hC : modulus (d * m + 1) / 2 = (q - 1) * G := by
    rw [hN]; have := geom_mul d m hd1; change (q - 1) * G = q ^ m - 1 at this
    omega
  have hG : 1 ≤ G := by
    have hx := geom_mono d hd1 (show 1 ≤ m by omega)
    have he : geom d 1 = 1 := by
      simp only [geom, pow_one]
      exact Nat.div_self (by have := Nat.one_lt_two_pow (by omega : d ≠ 0); omega)
    rw [he] at hx; exact hx
  have hw0 : 0 ≤ (w : ℤ) := Int.natCast_nonneg _
  have hwB : (w : ℤ) ≤ modulus d / 2 := by
    rw [hB]
    have hh : (w : ℤ) + 1 ≤ (2 : ℤ) ^ (d - 1) := by
      exact_mod_cast (show w + 1 ≤ 2 ^ (d - 1) by have := Nat.one_le_two_pow (n := d - 1); omega)
    omega
  have hdigit := digit_data d w hd hw
  have hpow : (∑ i : Fin d, (2 : ℤ) ^ i.val) = q - 1 := by
    rw [Fin.sum_univ_eq_sum_range]
    have h := geom_sum_mul (2 : ℤ) d
    norm_num at h
    exact h
  have hesum : (∑ i : Fin d, e i) = (w : ℤ) := charge_sum d w hd hw
  have hfsum (r : ℕ) : (∑ i : Fin d, f r i) = (w : ℤ) * q ^ r := by
    dsimp [f]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hpow, hesum]
    have := geom_mul d r hd1
    change (q - 1) * (geom d r : ℤ) = q ^ r - 1 at this
    nlinarith
  have hx (r : ℕ) (hr : r < m) (i : Fin d)
      (hp : r * d + i.val + 1 < d * m + 1) :
      actualSource (d * m + 1) (w * geom d m) ⟨r * d + i.val + 1, hp⟩ =
        2 * G * a i - f r i := by
    let T : ℤ := geom d r
    let R : ℤ := q ^ r
    let K : ℤ := 2 * G - T - 2 * R
    let y := actualSource (d + 1) w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    have hT : 0 ≤ T := Int.natCast_nonneg _
    have hR : 0 ≤ R := by dsimp [R, q]; positivity
    have hTR : T + R ≤ G := by
      have he := geom_succ d r hd1
      have hh := geom_mono d hd1 (show r + 1 ≤ m by omega)
      dsimp [T, R, G, q]; omega
    have hK : 0 ≤ K := by dsimp [K]; omega
    have hRrel : R = (q - 1) * T + 1 := by
      have := geom_mul d r hd1; dsimp [R, T, q]; omega
    have heq : 2 * G * a i - f r i = R * y + K * a i := by
      have ha := (hdigit i).2.1
      have hy := (hdigit i).2.2
      change y = 2 * a i - e i at hy
      change a i = 2 ^ i.val * w - (q - 1) * e i at ha
      dsimp [f, K, T]
      linear_combination T * ha - R * hy + e i * hRrel
    obtain ⟨hNa, hoa⟩ := TwoRunSource.modulus_positive_odd d (by omega)
    obtain ⟨hNy, hoy⟩ := TwoRunSource.modulus_positive_odd (d + 1) (by omega)
    have ha := centered_bounds hNa hoa ((2 : ℤ) ^ i.val * w)
    have hy := centered_bounds hNy hoy ((2 : ℤ) ^ (i.val + 1) * w)
    change -(modulus d / 2) ≤ a i ∧ a i ≤ modulus d / 2 at ha
    have hcy : modulus (d + 1) / 2 = q - 1 := by
      dsimp [modulus]; rw [pow_succ]; change (q * 2 - 1) / 2 = q - 1; omega
    change -(modulus (d + 1) / 2) ≤ y ∧ y ≤ modulus (d + 1) / 2 at hy
    rw [hcy] at hy
    have henvelope : R * (q - 1) + K * (modulus d / 2) ≤ (q - 1) * G := by
      dsimp [K]
      nlinarith [mul_nonneg hT (by omega : 0 ≤ modulus d / 2)]
    have hbounds : -(modulus (d * m + 1) / 2) ≤ 2 * G * a i - f r i ∧
        2 * G * a i - f r i ≤ modulus (d * m + 1) / 2 := by
      rw [heq, hC]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left ha.1 hK,
        mul_le_mul_of_nonneg_left ha.2 hK, mul_le_mul_of_nonneg_left hy.1 hR,
        mul_le_mul_of_nonneg_left hy.2 hR]
    obtain ⟨hNk, hok⟩ := TwoRunSource.modulus_positive_odd (d * m + 1) (by omega)
    apply centered_unique hNk hok (centered_bounds hNk hok _) hbounds
    rw [centered_mod]
    have heq' : 2 * G * a i - f r i =
        (2 : ℤ) ^ (r * d + i.val + 1) * (w * geom d m : ℕ) -
          modulus (d * m + 1) * f r i := by
      have hg := geom_mul d m hd1
      change (q - 1) * G = q ^ m - 1 at hg
      have ha := (hdigit i).2.1
      change a i = 2 ^ i.val * w - (q - 1) * e i at ha
      have hp2 : (2 : ℤ) ^ (r * d + i.val + 1) = 2 * R * 2 ^ i.val := by
        dsimp [R, q]; rw [pow_succ, pow_add, Nat.mul_comm r d, pow_mul]; ring
      rw [hp2, Nat.cast_mul, hN, ha]
      dsimp [f]
      linear_combination -2 * ((2 : ℤ) ^ i.val * (w : ℤ) * (geom d r : ℤ) + e i) * hg -
        2 * (2 : ℤ) ^ i.val * (w : ℤ) * G * hRrel
    rw [heq', Int.sub_mul_emod_self_left]
  have hy0 : actualSource (d + 1) w ⟨0, by omega⟩ = (w : ℤ) := by
    obtain ⟨hN0, ho0⟩ := TwoRunSource.modulus_positive_odd (d + 1) (by omega)
    apply centered_unique hN0 ho0 (centered_bounds hN0 ho0 _) ?_ (by simp [centered_mod])
    have hh : modulus (d + 1) / 2 = q - 1 := by
      dsimp [modulus]; rw [pow_succ]; change (q * 2 - 1) / 2 = q - 1; omega
    rw [hh]; constructor <;> omega
  have hx0 : actualSource (d * m + 1) (w * geom d m) ⟨0, by omega⟩ =
      (w * geom d m : ℕ) := by
    obtain ⟨hN0, ho0⟩ := TwoRunSource.modulus_positive_odd (d * m + 1) (by omega)
    apply centered_unique hN0 ho0 (centered_bounds hN0 ho0 _) ?_ (by simp [centered_mod])
    rw [hC, Nat.cast_mul]
    constructor <;> nlinarith [mul_nonneg hw0 (show 0 ≤ G by omega),
      mul_le_mul_of_nonneg_right hwB (show 0 ≤ G by omega)]
  refine ⟨hdigit, hesum, hx0, hy0, hx, fun r _ => hfsum r, ?_⟩
  intro i hp
  rw [hx (m - 1) (by omega) i hp]
  have hg := geom_succ d (m - 1) hd1
  rw [show m - 1 + 1 = m by omega] at hg
  have hr := geom_mul d (m - 1) hd1
  have ha := (hdigit i).2.1
  have hy := (hdigit i).2.2
  dsimp [f, G, a, e, q] at *
  linear_combination (geom d (m - 1) : ℤ) * ha -
    ((2 : ℤ) ^ d) ^ (m - 1) * hy + 2 * actualSource d w i * hg - charge d w i * hr

set_option maxHeartbeats 2000000 in
/-- Exact native old-value and charge alignment across a dyadic phase shift. -/
theorem native_charge_alignment (d a h : ℕ) (hd : 2 ≤ d) (ha : 1 ≤ a)
    (hb : 2 ^ h * a < 2 ^ (d - 1)) (i : Fin d) :
    let tau := (finRotate d : Equiv.Perm (Fin d)) ^ h
    actualSource d (2 ^ h * a) i = actualSource d a (tau i) ∧
    charge d (2 ^ h * a) i = charge d a (tau i) +
      (if (tau i).val < h then (2 : ℤ) ^ (tau i).val * a else 0) := by
  let tau := (finRotate d : Equiv.Perm (Fin d)) ^ h
  let j := tau i
  have hab : a ≤ 2 ^ h * a := by
    have := Nat.one_le_two_pow (n := h)
    nlinarith
  have hp : 2 ^ h < 2 ^ (d - 1) := by nlinarith
  have hh : h < d - 1 := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hp
  have hr : j.val = (i.val + h) % d := by
    have he := congrFun (finCycle_eq_finRotate_iterate (k := (⟨h, by omega⟩ : Fin d))) i
    have hv := congrArg Fin.val he
    simpa [j, tau, Equiv.Perm.coe_pow, finCycle, Fin.val_add] using hv.symm
  have da := digit_data d a hd (by omega) j
  have db := digit_data d (2 ^ h * a) hd (by omega) i
  obtain ⟨hM, ho⟩ := TwoRunSource.modulus_positive_odd d (by omega)
  have hM' : 0 < (2 : ℤ) ^ d - 1 := hM
  change actualSource d (2 ^ h * a) i = actualSource d a j ∧
    charge d (2 ^ h * a) i =
      charge d a j + (if j.val < h then (2 : ℤ) ^ j.val * a else 0)
  by_cases hw : i.val + h < d
  · have hj : j.val = i.val + h := by rw [hr, Nat.mod_eq_of_lt hw]
    have hjh : ¬ j.val < h := by omega
    have he : (2 : ℤ) ^ i.val * (2 ^ h * a : ℕ) = (2 : ℤ) ^ j.val * a := by
      rw [hj, pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    have hv : actualSource d (2 ^ h * a) i = actualSource d a j := by
      unfold actualSource
      rw [he]
    refine ⟨hv, ?_⟩
    rw [if_neg hjh, add_zero]
    have ea := da.2.1
    have eb := db.2.1
    rw [he, hv] at eb
    nlinarith
  · have hij : i.val + h < d + d := by omega
    have hj : j.val = i.val + h - d := by
      rw [hr, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hjh : j.val < h := by omega
    have huN : 2 ^ j.val * a ≤ 2 ^ h * a :=
      Nat.mul_le_mul_right a (Nat.pow_le_pow_right (by omega) (by omega))
    have hu : 0 ≤ (2 : ℤ) ^ j.val * a := by positivity
    have hhalf : modulus d / 2 = (2 : ℤ) ^ (d - 1) - 1 := by
      unfold modulus
      rw [show d = (d - 1) + 1 by omega, pow_succ]
      omega
    have huB : (2 : ℤ) ^ j.val * a ≤ modulus d / 2 := by
      rw [hhalf]
      exact_mod_cast (show 2 ^ j.val * a + 1 ≤ 2 ^ (d - 1) by omega)
    have hva : actualSource d a j = (2 : ℤ) ^ j.val * a := by
      exact centered_unique hM ho (centered_bounds hM ho _) ⟨by omega, huB⟩
        (centered_mod _ _)
    have he : (2 : ℤ) ^ i.val * (2 ^ h * a : ℕ) =
        (2 : ℤ) ^ d * ((2 : ℤ) ^ j.val * a) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, ← pow_add,
        show i.val + h = d + j.val by omega, pow_add]
      ring
    have hvb : actualSource d (2 ^ h * a) i = (2 : ℤ) ^ j.val * a := by
      unfold actualSource
      rw [he]
      have he' : (2 : ℤ) ^ d * ((2 : ℤ) ^ j.val * a) =
          (2 : ℤ) ^ j.val * a + ((2 : ℤ) ^ j.val * a) * modulus d := by
        unfold modulus
        ring
      apply (centered_congr (by rw [he', Int.add_mul_emod_self_right])).trans
      exact centered_unique hM ho (centered_bounds hM ho _) ⟨by omega, huB⟩
        (centered_mod _ _)
    have hqa : charge d a j = 0 := by
      have ea := da.2.1
      rw [hva] at ea
      nlinarith
    have hqb : charge d (2 ^ h * a) i = (2 : ℤ) ^ j.val * a := by
      have eb := db.2.1
      rw [he, hvb] at eb
      nlinarith
    exact ⟨hvb.trans hva.symm, by rw [if_pos hjh, hqa, hqb, zero_add]⟩


#check @periodic_source_equations
#print axioms periodic_source_equations

end D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
