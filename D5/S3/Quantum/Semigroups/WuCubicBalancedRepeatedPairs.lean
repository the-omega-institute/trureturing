import D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-!
At cubic exponent on the fixed-even two-CAR slice, the normalized deficit
for a repeated-pair spectrum is at least `2 * h^4 / 125`. The temperature
range is `0 < h ≤ 101 / 200`. Both spectral endpoints are included.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped BigOperators ComplexOrder Matrix Kronecker

namespace D5.S3.Quantum.Semigroups.WuCubicBalancedRepeatedPairs

open WuCubicOccupationEnvelope (CARConstraints orientationMoment edgeSum
  sym scaledCubicEnergy spectrumOf)
open WuCubicDirectedOccupationCap (rowImbalance frameWeight frameVector
  emptyProbability fullProbability evenProbability oddProbability)
open Set

noncomputable section

local notation "C" => Real.cosh
local notation "S" => Real.sinh

def thermalFactor (h : ℝ) : ℝ := (C h - C (h / 3)) * C h / S h

def sharpCoefficient (h : ℝ) : ℝ := 9 * (C h - C (h / 3)) / (8 * h * S h)

private def K (h : ℝ) : ℝ := thermalFactor h / (2 * h)
private def G (h : ℝ) : ℝ := S h - thermalFactor h

theorem scaled_sharpCoefficient {h : ℝ} (hh : 0 < h) :
    K h = (4 * C h / 9) * sharpCoefficient h := by
  unfold K thermalFactor sharpCoefficient
  field_simp [hh.ne', (Real.sinh_pos_iff.mpr hh).ne'] <;> ring

private def L (c : ℝ) : ℝ :=
  2 * (c^2 - 1) * (2 * c^2 + 1)^2 / (c * (4 * c^2 - 1)^2)

private def Hinf (c : ℝ) : ℝ :=
  c + 2 * (c^2 - 1) * (8 * c^2 + 3) / (c * (4 * c^2 - 1)^2)

private def Hextra (c : ℝ) : ℝ :=
  8 * (c^2)^2 * (c^2 - 1) / (c * (4 * c^2 - 1)^2)

def D0 (h : ℝ) : ℝ := C h - C (h / 3) - 2 * K h * Real.log (C h) - L (C (h / 3))
def R (h : ℝ) : ℝ := Hinf (C (h / 3)) + Hextra (C (h / 3)) - 9 / 2 * K h
def q (h : ℝ) : ℝ := 3 / 2 * K h - Hextra (C (h / 3))

private theorem cosh_triple (t : ℝ) :
    C (3 * t) = C t * (4 * C t ^ 2 - 3) := by
  rw [show 3 * t = (t + t) + t by ring, Real.cosh_add, Real.cosh_add, Real.sinh_add]
  linear_combination -3 * C t * Real.cosh_sq_sub_sinh_sq t

private theorem sinh_triple (t : ℝ) :
    S (3 * t) = S t * (4 * C t ^ 2 - 1) := by
  rw [show 3 * t = (t + t) + t by ring, Real.sinh_add, Real.cosh_add, Real.sinh_add]
  linear_combination -S t * Real.cosh_sq_sub_sinh_sq t

private theorem hyperbolic_parameters {h : ℝ} (hh : 0 < h) :
    let c := C (h / 3)
    let s := S (h / 3)
    let z := c^2
    1 ≤ c ∧ 0 < s ∧ c^2 - s^2 = 1 ∧
      C h = c * (4 * z - 3) ∧ S h = s * (4 * z - 1) ∧
      G h = s * (4 * z + 1) / (4 * z - 1) ∧ 0 < K h := by
  dsimp
  have ht : 0 < h / 3 := by positivity
  have hc := Real.one_le_cosh (h / 3)
  have hs := Real.sinh_pos_iff.mpr ht
  have hs2 := Real.cosh_sq_sub_sinh_sq (h / 3)
  have hC : C h = C (h / 3) * (4 * C (h / 3)^2 - 3) := by
    simpa only [show 3 * (h / 3) = h by ring] using cosh_triple (h / 3)
  have hS : S h = S (h / 3) * (4 * C (h / 3)^2 - 1) := by
    simpa only [show 3 * (h / 3) = h by ring] using sinh_triple (h / 3)
  have hz : 1 ≤ C (h / 3)^2 := by nlinarith only [hc, sq_nonneg (C (h / 3) - 1)]
  have hd : 0 < 4 * C (h / 3)^2 - 1 := by linarith
  have hdiff : 0 < C h - C (h / 3) := by
    rw [hC]
    have := mul_pos (Real.cosh_pos (h / 3)) (sq_pos_of_pos hs)
    nlinarith only [this, congrArg (fun x : ℝ => C (h / 3) * x) hs2]
  refine ⟨hc, hs, hs2, hC, hS, ?_, ?_⟩
  · unfold G thermalFactor
    rw [hC, hS]
    apply (eq_div_iff hd.ne').2
    rw [sub_mul]
    rw [show
        ((C (h / 3) * (4 * C (h / 3)^2 - 3) - C (h / 3)) *
          (C (h / 3) * (4 * C (h / 3)^2 - 3)) /
          (S (h / 3) * (4 * C (h / 3)^2 - 1))) *
          (4 * C (h / 3)^2 - 1) =
        (C (h / 3) * (4 * C (h / 3)^2 - 3) - C (h / 3)) *
          (C (h / 3) * (4 * C (h / 3)^2 - 3)) / S (h / 3) by
      rw [← div_div, div_mul_cancel₀ _ hd.ne']]
    apply (mul_left_inj' hs.ne').mp
    rw [sub_mul, div_mul_cancel₀ _ hs.ne']
    linear_combination (-16 * C (h / 3)^4 + 12 * C (h / 3)^2) * hs2
  · unfold K thermalFactor
    exact div_pos (div_pos (mul_pos hdiff (Real.cosh_pos h)) (Real.sinh_pos_iff.mpr hh))
      (by positivity)

private theorem log_one_add_cubic {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x^2 / 2 + x^3 / 3 := by
  let f (u : ℝ) := u - u^2 / 2 + u^3 / 3 - Real.log (1 + u)
  have hd (u : ℝ) (hu : u ∈ Icc 0 x) : HasDerivAt f (u^3 / (1 + u)) u := by
    have hu' : 0 < 1 + u := by linarith only [hu.1]
    have h := (((hasDerivAt_id u).sub ((hasDerivAt_pow 2 u).div_const 2)).add
      ((hasDerivAt_pow 3 u).div_const 3)).sub (((hasDerivAt_id u).const_add 1).log hu'.ne')
    convert h using 1
    · rfl
    · norm_num only [id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one]
      field_simp [hu'.ne'] <;> ring
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) x)
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u (interior_subset hu)).hasDerivWithinAt)
    (by
      intro u hu
      have hu' : u ∈ Icc 0 x := interior_subset hu
      exact div_nonneg (pow_nonneg hu'.1 3) (by linarith only [hu'.1]))
  have h := hm (show 0 ∈ Icc 0 x from ⟨le_rfl, hx⟩)
    (show x ∈ Icc 0 x from ⟨hx, le_rfl⟩) hx
  norm_num [f] at h
  linarith

private theorem neg_log_one_sub_cubic {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x + x^2 / 2 + x^3 / 3 + x^4 / (4 * (1 - x)) := by
  let f (u : ℝ) := u + u^2 / 2 + u^3 / 3 + u^4 / (4 * (1 - x)) + Real.log (1 - u)
  have hd (u : ℝ) (hu : u ∈ Icc 0 x) :
      HasDerivAt f (u^3 * (x - u) / ((1 - x) * (1 - u))) u := by
    have hu' : 0 < 1 - u := by linarith only [hu.2, hx1]
    have h := ((((hasDerivAt_id u).add ((hasDerivAt_pow 2 u).div_const 2)).add
      ((hasDerivAt_pow 3 u).div_const 3)).add ((hasDerivAt_pow 4 u).div_const
      (4 * (1 - x)))).add (((hasDerivAt_id u).const_sub 1).log hu'.ne')
    convert h using 1
    · rfl
    · norm_num only [id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one]
      field_simp [(sub_pos.mpr hx1).ne', hu'.ne'] <;> ring
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) x)
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u (interior_subset hu)).hasDerivWithinAt) (by
      intro u hu
      have hu' : u ∈ Icc 0 x := interior_subset hu
      exact div_nonneg (mul_nonneg (pow_nonneg hu'.1 3) (sub_nonneg.mpr hu'.2))
        (mul_nonneg (sub_nonneg.mpr hx1.le) (by linarith only [hu'.2, hx1])))
  have h := hm (show 0 ∈ Icc 0 x from ⟨le_rfl, hx⟩)
    (show x ∈ Icc 0 x from ⟨hx, le_rfl⟩) hx
  norm_num [f] at h
  linarith

private def J (η : ℝ) : ℝ := Real.log (1 + 3 * η) - 3 / 2 * Real.log (1 - η)
private def Jupper (η : ℝ) : ℝ :=
  9 / 2 * η - 15 / 4 * η^2 + 19 / 2 * η^3 + 3 * η^4 / (8 * (1 - η))

private theorem J_le {η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1) : J η ≤ Jupper η := by
  have hp := log_one_add_cubic (x := 3 * η) (by positivity)
  have hn := neg_log_one_sub_cubic hη hη1
  unfold J Jupper
  calc
    _ ≤ (3 * η - (3 * η)^2 / 2 + (3 * η)^3 / 3) +
        3 / 2 * (η + η^2 / 2 + η^3 / 3 + η^4 / (4 * (1 - η))) := by linarith
    _ = _ := by field_simp [(sub_pos.mpr hη1).ne'] <;> ring

private theorem half_log_ratio (t : ℝ) :
    1 / 2 * Real.log ((1 + S t / C t) / (1 - S t / C t)) = t := by
  have hc := Real.cosh_pos t
  have hp := Real.cosh_add_sinh t
  have hm : C t - S t = Real.exp (-t) := by rw [Real.cosh_eq, Real.sinh_eq]; ring
  have hr : (1 + S t / C t) / (1 - S t / C t) = Real.exp (2 * t) := by
    rw [show 2 * t = t + t by ring, Real.exp_add]
    rw [show 1 + S t / C t = Real.exp t / C t by rw [← hp]; field_simp [hc.ne'],
      show 1 - S t / C t = Real.exp (-t) / C t by rw [← hm]; field_simp [hc.ne'],
      Real.exp_neg]
    field_simp [hc.ne', (Real.exp_pos t).ne']
  rw [hr, Real.log_exp]
  ring

private def Hlo (η : ℝ) : ℝ := 1 + η / 3 + η^2 / 5
private def Hhi (η : ℝ) : ℝ := 1 + η / 3 + η^2 / (5 * (1 - η))

private theorem H_enclosure {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hη : t^2 ≤ 3 / 100) {u : ℝ}
    (hu : 1 / 2 * Real.log ((1 + t) / (1 - t)) = u) :
    Hlo (t^2) ≤ u / t ∧ u / t ≤ Hhi (t^2) ∧ Hhi (t^2) ≤ 98 / 97 := by
  have hd : 0 < 1 - t^2 := sub_pos.mpr (by nlinarith only [hη])
  have hlow := Real.sum_range_le_log_div ht.le ht1 3
  have hhigh := Real.log_div_le_sum_range_add ht.le ht1 4
  rw [hu] at hlow hhigh
  norm_num [Finset.sum_range_succ] at hlow hhigh
  refine ⟨(le_div_iff₀ ht).2 ?_, (div_le_iff₀ ht).2 ?_, ?_⟩
  · convert hlow using 1 <;> unfold Hlo <;> ring
  · have hhigh' : u ≤ t + t^3 / 3 + t^5 / 5 + t^7 / 7 + t^9 / (1 - t^2) := by
      convert hhigh using 1 <;> ring
    refine hhigh'.trans ?_
    have hh : (1 - t^2) / 7 + t^2 ≤ 1 / 5 := by nlinarith only [hη]
    apply (mul_le_mul_iff_right₀ hd).mp
    calc
      _ = (t + t^3 / 3 + t^5 / 5 + t^7 / 7) * (1 - t^2) + t^9 := by
        rw [mul_comm (1 - t^2), add_mul, div_mul_cancel₀ _ hd.ne']
      _ ≤ (t + t^3 / 3) * (1 - t^2) + t^5 / 5 := by
        nlinarith only [mul_le_mul_of_nonneg_left hh (show 0 ≤ t^7 by positivity)]
      _ = _ := by
        unfold Hhi
        field_simp [hd.ne'] <;> ring
  · have hn : t^4 ≤ (3 / 100 : ℝ)^2 := by
      rw [show t^4 = (t^2)^2 by ring]
      exact pow_le_pow_left₀ (sq_nonneg t) hη 2
    calc
      Hhi (t^2) ≤ 1 + (3 / 100 : ℝ) / 3 + (3 / 100 : ℝ)^2 / (5 * (1 - 3 / 100)) := by
        unfold Hhi
        rw [show (t^2)^2 = t^4 by ring]
        gcongr
      _ ≤ _ := by norm_num

private def T (η H j : ℝ) : ℝ :=
  H * (9 + 27 * η - 5 * η^2 + η^3) - 2 * (1 + 3 * η) * (3 + η) / (3 * η) * j

private def P1 (η : ℝ) : ℝ := 9 + 27 * η - 63 * η^2 + 33 * η^3 - 6 * η^4
private def P2 (η : ℝ) : ℝ := 9 + 30 * η + 9 * η^2

private theorem polynomial_certificates {η H : ℝ} (he : 0 < η) (he3 : η ≤ 3 / 100)
    (hlo : Hlo η ≤ H) (hhi : H ≤ Hhi η) :
    15 / 2 * η ≤ T η H (J η) ∧
      -62 * η^2 ≤ H * P1 η - P2 η ∧ H * P1 η - P2 η ≤ 0 := by
  have he1 : η < 1 := by linarith
  have hd : 0 < 1 - η := sub_pos.mpr he1
  have h2 : η^2 ≤ (3 / 100 : ℝ)^2 := pow_le_pow_left₀ he.le he3 2
  have h4 : η^4 ≤ (3 / 100 : ℝ)^4 := pow_le_pow_left₀ he.le he3 4
  have h3n : 0 ≤ η^3 := by positivity
  have h2n : 0 ≤ η^2 := sq_nonneg _
  have hA : 0 ≤ 9 + 27 * η - 5 * η^2 + η^3 := by linarith
  have hP : 0 ≤ P1 η := by unfold P1; linarith
  have hJ := J_le he.le he1
  constructor
  · calc
      15 / 2 * η ≤ T η (Hlo η) (Jupper η) := by
        have hexact :
            T η (Hlo η) (Jupper η) = 15 / 2 * η + η^2 / (1 - η) *
              (14 / 5 - 1093 / 20 * η + 434 / 15 * η^2 + 1147 / 60 * η^3 - η^4 / 5) := by
          unfold T Hlo Jupper
          field_simp [he.ne', hd.ne'] <;> ring
        rw [hexact]
        exact le_add_of_nonneg_right (mul_nonneg (by positivity) (by linarith))
      _ ≤ T η H (J η) := by
        unfold T
        exact sub_le_sub (mul_le_mul_of_nonneg_right hlo hA)
          (mul_le_mul_of_nonneg_left hJ (by positivity))
  constructor
  · calc
      -62 * η^2 ≤ Hlo η * P1 η - P2 η := by
        have hexact : Hlo η * P1 η - P2 η =
            η^2 * (-306 / 5 + 87 / 5 * η - 38 / 5 * η^2 + 23 / 5 * η^3 - 6 / 5 * η^4) := by
          unfold Hlo P1 P2
          ring
        rw [hexact, show -62 * η^2 = η^2 * (-62) by ring]
        exact mul_le_mul_of_nonneg_left (by linarith) h2n
      _ ≤ _ := sub_le_sub_right (mul_le_mul_of_nonneg_right hlo hP) _
  · calc
      H * P1 η - P2 η ≤ Hhi η * P1 η - P2 η :=
        sub_le_sub_right (mul_le_mul_of_nonneg_right hhi hP) _
      _ = -(2 / 5) * η^2 * (153 - 48 * η + η^2 + 2 * η^3) := by
        unfold Hhi P1 P2
        field_simp [hd.ne'] <;> ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
        (by linarith only [sq_nonneg η]) (by linarith)

/-- Rational coefficient estimates, with the common positive denominator
(H (1-eta)^{3/2} (3+eta)^2). -/
private theorem coefficient_bounds_of_parameters {h η H k : ℝ}
    (he : 0 < η) (he3 : η ≤ 3 / 100)
    (hlo : Hlo η ≤ H) (hhi : H ≤ Hhi η) (hHmax : H ≤ 98 / 97)
    (hk : 0 < k) (hk1 : k ≤ 1) (hk2 : k^2 = 1 - η)
    (hh4 : h^4 = 81 * η^2 * H^4)
    (hD : D0 h = 2 * η * T η H (J η) / (H * k * (1 - η) * (3 + η)^2))
    (hR : R h = (H * P1 η - P2 η) / (H * k * (1 - η) * (3 + η)^2))
    (hq : q h = ((1 + 3 * η) * (3 + η) - 8 * η * H * (1 - η)) /
      (H * k * (1 - η) * (3 + η)^2)) :
    h^4 / 60 ≤ D0 h ∧ -(h^4 / 10) ≤ R h ∧ R h ≤ 0 ∧ 1 / 4 ≤ q h := by
  have he1 : η < 1 := by linarith
  have hH : 1 ≤ H := by
    unfold Hlo at hlo
    nlinarith only [hlo, he.le, sq_nonneg η]
  have hH0 : 0 < H := by linarith
  have hH4 : 1 ≤ H^4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hH 4
  have hklo : 1 - η ≤ k := by
    rw [← hk2]
    nlinarith only [mul_nonneg hk.le (sub_nonneg.mpr hk1)]
  let den := H * k * (1 - η) * (3 + η)^2
  have hden : 0 < den := by unfold den; positivity
  have hdenlo : 9 * (97 / 100 : ℝ)^2 ≤ den := by
    unfold den
    calc
      9 * (97 / 100 : ℝ)^2 = 1 * (97 / 100) * (97 / 100) * 3^2 := by ring
      _ ≤ _ := by
        gcongr <;> linarith
  have hdenhi : den ≤ H * (303 / 100 : ℝ)^2 := by
    unfold den
    calc
      H * k * (1 - η) * (3 + η)^2 ≤ H * 1 * 1 * (303 / 100)^2 := by
        gcongr <;> linarith
      _ = _ := by ring
  have hdenH : den * H^4 ≤ 10 := by
    calc
      den * H^4 ≤ H * (303 / 100 : ℝ)^2 * H^4 :=
        mul_le_mul_of_nonneg_right hdenhi (by positivity)
      _ = (303 / 100 : ℝ)^2 * H^5 := by ring
      _ ≤ (303 / 100 : ℝ)^2 * (98 / 97)^5 := by gcongr
      _ ≤ _ := by norm_num
  have hden10 : den ≤ 10 := by
    calc
      den = den * 1 := by ring
      _ ≤ den * H^4 := mul_le_mul_of_nonneg_left hH4 hden.le
      _ ≤ _ := hdenH
  obtain ⟨hT, hRlo, hRhi⟩ := polynomial_certificates he he3 hlo hhi
  have hh4lo : 81 * η^2 ≤ h^4 := by
    rw [hh4]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hH4
      (show 0 ≤ 81 * η^2 by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hD]
    change h^4 / 60 ≤ 2 * η * T η H (J η) / den
    apply (le_div_iff₀ hden).2
    calc
      h^4 / 60 * den = (81 / 60 * η^2) * (den * H^4) := by rw [hh4]; ring
      _ ≤ (81 / 60 * η^2) * 10 := mul_le_mul_of_nonneg_left hdenH (by positivity)
      _ ≤ 2 * η * (15 / 2 * η) := by nlinarith only [sq_nonneg η]
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
  · rw [hR]
    change -(h^4 / 10) ≤ (H * P1 η - P2 η) / den
    apply (le_div_iff₀ hden).2
    have hmul : 81 * η^2 * (9 * (97 / 100 : ℝ)^2) ≤ h^4 * den :=
      mul_le_mul hh4lo hdenlo (by positivity) (by positivity)
    nlinarith only [hmul, hRlo, sq_nonneg η]
  · rw [hR]
    exact div_nonpos_of_nonpos_of_nonneg hRhi hden.le
  · rw [hq]
    change 1 / 4 ≤ ((1 + 3 * η) * (3 + η) - 8 * η * H * (1 - η)) / den
    apply (le_div_iff₀ hden).2
    have hsub : 8 * η * H * (1 - η) ≤ 8 * (3 / 100 : ℝ) * (98 / 97) * 1 := by
      gcongr <;> linarith
    have hprod : 3 ≤ (1 + 3 * η) * (3 + η) := by
      nlinarith only [he.le, sq_nonneg η]
    linarith only [hsub, hprod, hden10]

/-- The three analytic coefficients in the repeated-pair estimate. -/
theorem coefficient_bounds {h : ℝ} (hh : 0 < h) (hhmax : h ≤ 101 / 200) :
    h^4 / 60 ≤ D0 h ∧ -(h^4 / 10) ≤ R h ∧ R h ≤ 0 ∧ 1 / 4 ≤ q h := by
  let c := C (h / 3)
  let s := S (h / 3)
  obtain ⟨hc, hs, hcs, hC, hS, _, _⟩ := hyperbolic_parameters hh
  change 1 ≤ c at hc
  change 0 < s at hs
  change c^2 - s^2 = 1 at hcs
  change C h = c * (4 * c^2 - 3) at hC
  change S h = s * (4 * c^2 - 1) at hS
  have hc0 : 0 < c := by linarith
  let t := s / c
  let η := t^2
  let H := (h / 3) / t
  let k := 1 / c
  have ht : 0 < t := div_pos hs hc0
  have he : 0 < η := by dsimp [η]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hk1 : k ≤ 1 := (div_le_iff₀ hc0).2 (by linarith)
  have hk2 : k^2 = 1 - η := by
    dsimp [k, η, t]
    field_simp [hc0.ne'] <;> linarith only [hcs]
  have ht1 : t < 1 := by
    have h := sq_pos_of_pos hk
    rw [hk2] at h
    dsimp [η] at h
    nlinarith only [h, sq_nonneg (t - 1)]
  have htlog : 1 / 2 * Real.log ((1 + t) / (1 - t)) = h / 3 :=
    half_log_ratio (h / 3)
  have htle : t ≤ h / 3 := by
    have hl := Real.sum_range_le_log_div ht.le ht1 1
    rw [htlog] at hl
    simpa using hl
  have he3 : η ≤ 3 / 100 := by
    calc
      η ≤ ((101 / 200 : ℝ) / 3)^2 :=
        pow_le_pow_left₀ ht.le (htle.trans (by linarith)) 2
      _ ≤ _ := by norm_num
  have he1 : 0 < 1 - η := by linarith
  have h3e : 0 < 3 + η := by linarith
  have h1e : 0 < 1 + 3 * η := by linarith
  obtain ⟨hlo, hhi, hHmax⟩ := H_enclosure ht ht1 he3 htlog
  have hH : 0 < H := by dsimp [H]; positivity
  have hhH : h = 3 * t * H := by dsimp [H]; field_simp [ht.ne']
  have hh4 : h^4 = 81 * η^2 * H^4 := by rw [hhH]; dsimp [η]; ring
  have hz : c^2 = 1 / (1 - η) := by
    rw [← hk2]
    dsimp [k]
    field_simp [hc0.ne']
  have hck : c = 1 / k := by dsimp [k]; field_simp [hc0.ne']
  have hs' : s = t * c := by dsimp [t]; field_simp [hc0.ne']
  have hC' : C h = (1 + 3 * η) / (k * (1 - η)) := by
    calc
      C h = c * (4 * (1 / (1 - η)) - 3) := by rw [hC, hz]
      _ = _ := by rw [hck]; field_simp [hk.ne', he1.ne'] <;> ring
  have hS' : S h = t * (3 + η) / (k * (1 - η)) := by
    calc
      S h = (t * c) * (4 * (1 / (1 - η)) - 1) := by rw [hS, hz, hs']
      _ = _ := by rw [hck]; field_simp [hk.ne', he1.ne'] <;> ring
  have hlog : Real.log (C h) = J η := by
    have hklog : 2 * Real.log k = Real.log (1 - η) := by
      rw [← hk2, Real.log_pow]
      norm_num
    rw [hC', J, Real.log_div h1e.ne' (mul_ne_zero hk.ne' he1.ne'),
      Real.log_mul hk.ne' he1.ne']
    linarith only [hklog]
  have hK : K h = 2 * (1 + 3 * η) / (3 * H * k * (1 - η) * (3 + η)) := by
    have heq : K h = (C h - c) * C h / S h / (2 * h) := rfl
    rw [heq, hC', hS', hck, hhH]
    dsimp only [η] at *
    field_simp [ht.ne', hH.ne', hk.ne', he1.ne', h3e.ne'] <;> ring
  have hL : L c = 2 * η * (3 - η)^2 / (k * (3 + η)^2) := by
    have heq : 4 * c^2 - 1 = (3 + η) / (1 - η) := by
      rw [hz]; field_simp [he1.ne'] <;> ring
    have hL' : L c = 2 * (c^2 - 1) * (2 * c^2 + 1)^2 /
        (c * (4 * c^2 - 1)^2) := rfl
    rw [hL', heq, hz, hck]
    calc
      _ = 2 * η * (3 - η)^2 * k / ((1 - η) * (3 + η)^2) := by
        field_simp [hk.ne', he1.ne', h3e.ne'] <;> ring
      _ = _ := by
        rw [← hk2]
        field_simp [hk.ne', h3e.ne'] <;> ring
  have hExtra : Hextra c = 8 * η / (k * (3 + η)^2) := by
    have heq : 4 * c^2 - 1 = (3 + η) / (1 - η) := by
      rw [hz]; field_simp [he1.ne'] <;> ring
    have hE : Hextra c = 8 * (c^2)^2 * (c^2 - 1) / (c * (4 * c^2 - 1)^2) := rfl
    rw [hE, heq, hz, hck]
    calc
      _ = 8 * η * k / ((1 - η) * (3 + η)^2) := by
        field_simp [hk.ne', he1.ne', h3e.ne'] <;> ring
      _ = _ := by
        rw [← hk2]
        field_simp [hk.ne', h3e.ne'] <;> ring
  have hInf : Hinf c = 1 / k + 2 * η * (11 - 3 * η) * k / (3 + η)^2 := by
    have heq : 4 * c^2 - 1 = (3 + η) / (1 - η) := by
      rw [hz]; field_simp [he1.ne'] <;> ring
    have hI : Hinf c = c + 2 * (c^2 - 1) * (8 * c^2 + 3) /
        (c * (4 * c^2 - 1)^2) := rfl
    rw [hI, heq, hz, hck]
    field_simp [hk.ne', he1.ne', h3e.ne'] <;> ring
  refine coefficient_bounds_of_parameters (h := h) he he3 hlo hhi (hhi.trans hHmax)
    hk hk1 hk2 hh4 ?_ ?_ ?_
  · change C h - c - 2 * K h * Real.log (C h) - L c = _
    rw [hlog, hC', hK, hL, hck]
    unfold T
    field_simp [he.ne', hk.ne', hH.ne', he1.ne', h3e.ne']
    rw [hhH]
    ring
  · change Hinf c + Hextra c - 9 / 2 * K h = _
    rw [hInf, hExtra, hK]
    have hInf' : 2 * η * (11 - 3 * η) * k / (3 + η)^2 =
        2 * η * (11 - 3 * η) * (1 - η) / (k * (3 + η)^2) := by
      rw [← hk2]
      field_simp [hk.ne', h3e.ne'] <;> ring
    rw [hInf']
    unfold P1 P2
    field_simp [hk.ne', hH.ne', he1.ne', h3e.ne']
    rw [hhH]
    ring
  · change 3 / 2 * K h - Hextra c = _
    rw [hK, hExtra]
    field_simp [hk.ne', hH.ne', he1.ne', h3e.ne']
    rw [hhH]
    ring

private def binaryEntropy (r : ℝ) : ℝ :=
  (r^3 / (1 + r^3)) * Real.log (2 * r^3 / (1 + r^3)) +
    (1 / (1 + r^3)) * Real.log (2 / (1 + r^3))

private def V (y : ℝ) : ℝ := (y - 1) / (4 * y - 3) * (3 + 3 / (2 * y))

private def vOf (r : ℝ) : ℝ := ((1 - r) / (1 + r))^2
private def entropySupport (v : ℝ) : ℝ :=
  v / (1 + 3 * v) * (9 / 2 - 3 / 2 * v)

private theorem binaryEntropy_le_log_two {r : ℝ} (hr : 0 ≤ r) :
    binaryEntropy r ≤ Real.log 2 := by
  rcases hr.eq_or_lt with h | hr
  · subst r
    simp [binaryEntropy]
  have hm : 0 < 1 + r^3 := by positivity
  have hp : 0 < 2 * r^3 / (1 + r^3) := by positivity
  have hl := Real.log_le_log hp (show 2 * r^3 / (1 + r^3) ≤ 2 from
    (div_le_iff₀ hm).2 (by linarith))
  have hh := Real.log_le_log (show 0 < 2 / (1 + r^3) by positivity)
    (show 2 / (1 + r^3) ≤ 2 from (div_le_iff₀ hm).2 (by nlinarith only [pow_nonneg hr.le 3]))
  unfold binaryEntropy
  calc
    _ ≤ r^3 / (1 + r^3) * Real.log 2 + 1 / (1 + r^3) * Real.log 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hl (by positivity))
        (mul_le_mul_of_nonneg_left hh (by positivity))
    _ = _ := by field_simp [hm.ne'] <;> ring

private theorem log_two_le_three_fourths : Real.log 2 ≤ 3 / 4 := by
  have h := Real.log_div_le_sum_range_add (x := 1 / 3) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  linarith

private def hyperEntropy (t : ℝ) : ℝ :=
  (3 * t) * (S (3 * t) / C (3 * t)) - Real.log (C (3 * t))

private theorem hasDerivAt_sinh_div_cosh (t : ℝ) :
    HasDerivAt (fun x => S x / C x) (1 / C t ^ 2) t := by
  have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  convert h using 1
  rw [← pow_two, ← pow_two, Real.cosh_sq_sub_sinh_sq]

private theorem hasDerivAt_hyperEntropy (t : ℝ) :
    HasDerivAt hyperEntropy (9 * t / C (3 * t)^2) t := by
  have hx := (hasDerivAt_id t).const_mul 3
  have ht := (hasDerivAt_sinh_div_cosh (3 * t)).comp t hx
  have hlog := ((Real.hasDerivAt_cosh (3 * t)).comp t hx).log (Real.cosh_pos _).ne'
  have hd := (hx.mul ht).sub hlog
  convert hd using 1
  · rfl
  · simp only [id_eq, Function.comp_apply, mul_one]
    ring

private theorem hasDerivAt_V_cosh_sq (t : ℝ) :
    HasDerivAt (fun x => V (C x ^ 2))
      (3 * S t * (-2 * (C t ^ 2)^2 + 8 * C t ^ 2 - 3) /
        (C t * (C t ^ 2) * (4 * C t ^ 2 - 3)^2)) t := by
  let y := C t ^ 2
  have hc := Real.cosh_pos t
  have hy : 1 ≤ y := by
    simpa [y] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (Real.one_le_cosh t) 2
  have hy0 : 0 < y := by linarith
  have hd0 : 0 < 4 * y - 3 := by linarith
  have hy' : HasDerivAt (fun x => C x ^ 2) (2 * C t * S t) t := by
    convert (Real.hasDerivAt_cosh t).pow 2 using 1 <;> ring
  have ha := (hy'.sub_const 1).div ((hy'.const_mul 4).sub_const 3) hd0.ne'
  have hb := ((hasDerivAt_const t (3 : ℝ)).div (hy'.const_mul 2)
    (show 2 * y ≠ 0 by positivity)).const_add 3
  convert ha.mul hb using 1
  · rfl
  · change _ = _
    dsimp [y] at hy0 hd0 ⊢
    field_simp [hc.ne', hy0.ne', hd0.ne'] <;> ring

private theorem V_ge_hyperEntropy {t : ℝ} (ht : 0 ≤ t) (hy : C t ^ 2 ≤ 2) :
    hyperEntropy t ≤ V (C t ^ 2) := by
  let f (x : ℝ) := V (C x ^ 2) - hyperEntropy x
  let f' (x : ℝ) :=
    3 * S x * (-2 * (C x ^ 2)^2 + 8 * C x ^ 2 - 3) /
      (C x * (C x ^ 2) * (4 * C x ^ 2 - 3)^2) - 9 * x / C (3 * x)^2
  have hd (x : ℝ) : HasDerivAt f (f' x) x :=
    (hasDerivAt_V_cosh_sq x).sub (hasDerivAt_hyperEntropy x)
  have hs (x : ℝ) (hx : x ∈ Icc 0 t) : 0 ≤ f' x := by
    let y := C x ^ 2
    let P := -2 * y^2 + 8 * y - 3
    have hc := Real.cosh_pos x
    have hC1 := Real.one_le_cosh x
    have hy1 : 1 ≤ y := by
      simpa [y] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hC1 2
    have hy2 : y ≤ 2 := (pow_le_pow_left₀ hc.le
      (Real.cosh_le_cosh.mpr (by simpa [abs_of_nonneg hx.1, abs_of_nonneg ht] using hx.2)) 2).trans hy
    have hp : 0 ≤ P := by
      dsimp [P]
      nlinarith only [hy1, mul_nonneg (sub_nonneg.mpr hy2) (show 0 ≤ y by linarith)]
    have hfactor : 0 ≤ 4 * (y - 1)^3 - 16 * (y - 1)^2 + 4 * (y - 1) + 15 := by
      have hn := mul_nonneg (sub_nonneg.mpr hy1) (sq_nonneg (y - 3))
      nlinarith only [hn, hy2]
    have hsq : (3 * C x)^2 ≤ P^2 := by
      have hpoly : P^2 - (3 * C x)^2 =
          (y - 1) * (4 * (y - 1)^3 - 16 * (y - 1)^2 + 4 * (y - 1) + 15) := by
        dsimp [P, y]
        ring
      exact sub_nonneg.mp (hpoly.symm ▸ mul_nonneg (sub_nonneg.mpr hy1) hfactor)
    have hP : 3 * C x ≤ P := (sq_le_sq₀ (by positivity : 0 ≤ 3 * C x) hp).mp hsq
    have hS := Real.sinh_nonneg_iff.mpr hx.1
    have hXS := Real.self_le_sinh_iff.mpr hx.1
    have hdiff : 0 ≤ 4 * y - 3 := by linarith
    have hden : 0 < C x * y * (4 * y - 3)^2 := by
      have : 0 < y := by linarith
      have : 0 < 4 * y - 3 := by linarith
      positivity
    have hcombine : 9 * x * C x ≤ 3 * S x * P := by
      have ha := mul_le_mul_of_nonneg_right hXS hc.le
      have hb := mul_le_mul_of_nonneg_left hP hS
      nlinarith only [ha, hb]
    change 0 ≤ 3 * S x * P / (C x * y * (4 * y - 3)^2) - 9 * x / C (3 * x)^2
    rw [cosh_triple]
    apply sub_nonneg.mpr
    calc
      9 * x / (C x * (4 * C x ^ 2 - 3))^2 =
          (9 * x * C x) / (C x * y * (4 * y - 3)^2) := by
        have hh : 4 * C x ^ 2 - 3 ≠ 0 := by change 4 * y - 3 ≠ 0; linarith
        dsimp [y]
        field_simp [hc.ne', hh] <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right hcombine hden.le
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) t)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).hasDerivWithinAt)
    (fun x hx => hs x (interior_subset hx))
  have h := hm (show 0 ∈ Icc 0 t from ⟨le_rfl, ht⟩)
    (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩) ht
  have h0 : f 0 = 0 := by norm_num [f, V, hyperEntropy]
  rw [h0] at h
  exact sub_nonneg.mp h

private theorem binaryEntropy_le_support {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    binaryEntropy r ≤ entropySupport (vOf r) := by
  rcases hr.eq_or_lt with h | hr
  · subst r
    norm_num [binaryEntropy, entropySupport, vOf]
    exact log_two_le_three_fourths
  let t := -(Real.log r) / 2
  let y := C t ^ 2
  have ht : 0 ≤ t := by
    dsimp [t]
    linarith only [Real.log_nonpos hr.le hr1]
  have hlog : -(2 * t) = Real.log r := by dsimp [t]; ring
  have h2 : Real.exp (-(2 * t)) = r := by rw [hlog, Real.exp_log hr]
  have hr3 : Real.exp (-(3 * t)) = Real.exp (3 * t) * r^3 := by
    have hex : Real.exp (3 * t) * Real.exp (-(2 * t))^3 = Real.exp (-(3 * t)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      norm_num <;> ring
    rw [h2] at hex
    exact hex.symm
  have hpos := Real.cosh_pos (3 * t)
  have hmass : 0 < 1 + r^3 := by positivity
  have hsum : 2 * C (3 * t) = Real.exp (3 * t) * (1 + r^3) := by
    rw [Real.cosh_eq, hr3]
    ring
  have hp : r^3 / (1 + r^3) = Real.exp (-(3 * t)) / (2 * C (3 * t)) := by
    rw [hsum, hr3]
    field_simp [hmass.ne', (Real.exp_pos (3 * t)).ne']
  have hq : 1 / (1 + r^3) = Real.exp (3 * t) / (2 * C (3 * t)) := by
    rw [hsum]
    field_simp [hmass.ne', (Real.exp_pos (3 * t)).ne']
  have hE : binaryEntropy r = hyperEntropy t := by
    have hlow : 2 * r^3 / (1 + r^3) = Real.exp (-(3 * t)) / C (3 * t) := by
      calc
        _ = 2 * (r^3 / (1 + r^3)) := by ring
        _ = _ := by rw [hp]; ring
    have hhigh : 2 / (1 + r^3) = Real.exp (3 * t) / C (3 * t) := by
      calc
        _ = 2 * (1 / (1 + r^3)) := by ring
        _ = _ := by rw [hq]; ring
    unfold binaryEntropy hyperEntropy
    rw [hlow, hhigh, hp, hq, Real.log_div (Real.exp_pos _).ne' hpos.ne',
      Real.log_div (Real.exp_pos _).ne' hpos.ne', Real.log_exp, Real.log_exp,
      Real.sinh_eq]
    have hsum' : Real.exp (3 * t) + Real.exp (-(3 * t)) = 2 * C (3 * t) := by
      rw [Real.cosh_eq]
      ring
    calc
      _ = (3 * t) * ((Real.exp (3 * t) - Real.exp (-(3 * t))) / 2 / C (3 * t)) -
          (Real.exp (3 * t) + Real.exp (-(3 * t))) / (2 * C (3 * t)) * Real.log (C (3 * t)) := by ring
      _ = _ := by rw [hsum']; field_simp [hpos.ne']
  have hy : 1 ≤ y := by
    simpa [y] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (Real.one_le_cosh t) 2
  have hy0 : 0 < y := by linarith
  have hy4 : 0 < 4 * y - 3 := by linarith
  have hyv : vOf r = (y - 1) / y := by
    have hsC : S t / C t = (1 - r) / (1 + r) := by
      have he : Real.exp (-t) = Real.exp t * r := by
        rw [← h2, ← Real.exp_add]
        congr 1
        ring
      rw [Real.sinh_eq, Real.cosh_eq, he]
      have hr' : 0 < 1 + r := by positivity
      have hep := Real.exp_pos t
      have hsum' : Real.exp t + Real.exp t * r ≠ 0 := by positivity
      field_simp [hr'.ne', hep.ne', hsum'] <;> ring
    rw [vOf, ← hsC]
    have hc := Real.cosh_pos t
    dsimp [y]
    rw [div_pow]
    congr 1
    linarith only [Real.cosh_sq_sub_sinh_sq t]
  have hv : entropySupport (vOf r) = V y := by
    rw [entropySupport, hyv, V]
    have hd : 1 + 3 * ((y - 1) / y) = (4 * y - 3) / y := by
      field_simp [hy0.ne']
      ring
    rw [hd]
    field_simp [hy0.ne', hy4.ne'] <;> ring
  rw [hv]
  by_cases hy2 : y ≤ 2
  · rw [hE]
    exact V_ge_hyperEntropy ht hy2
  · have hV : (3 / 4 : ℝ) ≤ V y := by
      have hf : V y - 3 / 4 = 3 * (y - 2) / (4 * y * (4 * y - 3)) := by
        have hleft : (4 * y - 3) * V y = (y - 1) * (3 + 3 / (2 * y)) := by
          unfold V
          rw [← mul_assoc, mul_div_cancel₀ _ hy4.ne']
        have hright : (4 * y - 3) * (3 * (y - 2) / (4 * y * (4 * y - 3))) =
            3 * (y - 2) / (4 * y) := by
          rw [← div_div, mul_div_cancel₀ _ hy4.ne']
        apply (mul_right_inj' hy4.ne').mp
        rw [mul_sub, hleft, hright]
        field_simp [hy0.ne'] <;> ring
      exact sub_nonneg.mp (hf.symm ▸ div_nonneg
        (mul_nonneg (by norm_num) (sub_nonneg.mpr (le_of_not_ge hy2))) (by positivity))
    exact (binaryEntropy_le_log_two hr.le).trans (log_two_le_three_fourths.trans hV)

/-- The fixed-even directed caps, in the equivalent affine form indexed by
positive Young parameters. The imbalance is row mass minus column mass. -/
def DirectedCaps (w : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ (i j : Fin 4) (t : ℝ), i ≠ j → 0 < t →
    w i j ≤ (1 + t) * (1 + rowImbalance w i) / 8 +
      (1 + 1 / t) * (1 - rowImbalance w j) / 8

private def lowToHigh (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  w 0 2 + w 0 3 + w 1 2 + w 1 3

private def highToLow (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  w 2 0 + w 2 1 + w 3 0 + w 3 1

private def cutMass (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  (lowToHigh w + highToLow w) / 2

private def cutImbalance (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  (lowToHigh w - highToLow w) / 2

private theorem cut_support {w : Fin 4 → Fin 4 → ℝ}
    (hrows : ∀ i, (∑ j, sym w i j) = 2) (hdiag : ∀ i, w i i = 1 / 4)
    (hd : ∀ i, |rowImbalance w i| ≤ 1) (hcap : DirectedCaps w) :
    1 / 2 + (cutImbalance w)^2 / 4 ≤ cutMass w := by
  let δ := cutImbalance w
  have hδ : rowImbalance w 0 + rowImbalance w 1 = 2 * δ := by
    simp only [rowImbalance, Fin.sum_univ_four, δ, cutImbalance, lowToHigh, highToLow]
    ring
  -- The combined marginal expresses the cut mass using just the two directed caps.
  have hg : cutMass w = 3 / 2 - (w 0 1 + w 1 0) := by
    have h0 := hrows 0
    have h1 := hrows 1
    simp only [sym, Fin.sum_univ_four, hdiag] at h0 h1
    unfold cutMass lowToHigh highToLow
    linarith only [h0, h1]
  have hd0 := abs_le.mp (hd 0)
  have hd1 := abs_le.mp (hd 1)
  have hplus : 0 < 2 + δ := by linarith only [hδ, hd0.1, hd1.1]
  have hminus : 0 < 2 - δ := by linarith only [hδ, hd0.2, hd1.2]
  -- A common Young parameter yields the quadratic support without averaging the table.
  let t := (2 - δ) / (2 + δ)
  have ht : 0 < t := div_pos hminus hplus
  have h01 := hcap 0 1 t (by decide) ht
  have h10 := hcap 1 0 t (by decide) ht
  have hpair : w 0 1 + w 1 0 ≤ (2 + t * (1 + δ) + (1 - δ) / t) / 4 := by
    have heq :
        ((1 + t) * (1 + rowImbalance w 0) / 8 +
          (1 + 1 / t) * (1 - rowImbalance w 1) / 8) +
        ((1 + t) * (1 + rowImbalance w 1) / 8 +
          (1 + 1 / t) * (1 - rowImbalance w 0) / 8) =
          (2 + t * (1 + δ) + (1 - δ) / t) / 4 := by
      linear_combination ((t - 1 / t) / 8) * hδ
    exact (add_le_add h01 h10).trans_eq heq
  have hsupport : (2 + t * (1 + δ) + (1 - δ) / t) / 4 ≤ 1 - δ^2 / 4 := by
    have hexact : 1 - δ^2 / 4 - (2 + t * (1 + δ) + (1 - δ) / t) / 4 =
        δ^4 / (4 * (2 - δ) * (2 + δ)) := by
      dsimp only [t]
      field_simp [hplus.ne', hminus.ne'] <;> ring
    exact sub_nonneg.mp (hexact.symm ▸ (show 0 ≤ δ^4 / (4 * (2 - δ) * (2 + δ)) by positivity))
  rw [hg]
  change 1 / 2 + δ^2 / 4 ≤ _
  linarith only [hpair.trans hsupport]

def repeatedRoots (a b : ℝ) : Fin 4 → ℝ := ![a, a, b, b]

def cubicMass (x : Fin 4 → ℝ) : ℝ := ∑ i, (x i)^3

/-- The relative entropy of the spectral density against the equal-temperature
product Gibbs state. The signed charge moment is determined by the edge weights.
At a zero eigenvalue its entropy summand is zero. -/
def relativeEntropy (h : ℝ) (x : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  (∑ i, spectrumOf x (cubicMass x) i * Real.log (4 * spectrumOf x (cubicMass x) i)) +
    2 * Real.log (C h) - h * orientationMoment (spectrumOf x (cubicMass x)) w

/-- Ordinary-trace cubic jump energy with Wu's (1/[4p(1-p)]) factor at (p=1/3). -/
def cubicEnergy (h : ℝ) (x : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  9 / (4 * C h) *
    scaledCubicEnergy (C h) (S h) (C (h / 3)) (S (h / 3)) x (cubicMass x) w

def normalizedCubicDeficit (h : ℝ) (x : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  scaledCubicEnergy (C h) (S h) (C (h / 3)) (S (h / 3)) x (cubicMass x) w -
    K h * relativeEntropy h x w

theorem normalizedCubicDeficit_eq {h : ℝ} (hh : 0 < h)
    (x : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) :
    normalizedCubicDeficit h x w =
      (4 * C h / 9) * (cubicEnergy h x w - sharpCoefficient h * relativeEntropy h x w) := by
  rw [normalizedCubicDeficit, scaled_sharpCoefficient hh, cubicEnergy]
  field_simp [(Real.cosh_pos h).ne'] <;> ring

private def A (c r : ℝ) : ℝ := c * (1 - r)^2 * (1 + r) / (2 * (1 + r^3))
private def B (g s r : ℝ) : ℝ := (g * (1 - r^3) - s * r * (1 - r)) / (2 * (1 + r^3))

private theorem pair_mass (a b : ℝ) :
    cubicMass (repeatedRoots a b) = 2 * (a^3 + b^3) := by
  norm_num [cubicMass, repeatedRoots, Fin.sum_univ_four] <;> ring

private theorem sum_log_repeated {r : ℝ} (hr : 0 ≤ r) :
    (∑ i, spectrumOf (repeatedRoots r 1) (cubicMass (repeatedRoots r 1)) i *
      Real.log (4 * spectrumOf (repeatedRoots r 1) (cubicMass (repeatedRoots r 1)) i)) =
      binaryEntropy r := by
  have hm : 0 < 1 + r^3 := by positivity
  have he : 2 * (r^3 + 1^3) = 2 * (1 + r^3) := by ring
  rw [pair_mass, he]
  simp only [Fin.sum_univ_four]
  change
    (r^3 / (2 * (1 + r^3))) * Real.log (4 * (r^3 / (2 * (1 + r^3)))) +
      (r^3 / (2 * (1 + r^3))) * Real.log (4 * (r^3 / (2 * (1 + r^3)))) +
      ((1 : ℝ)^3 / (2 * (1 + r^3))) * Real.log (4 * (1^3 / (2 * (1 + r^3)))) +
      ((1 : ℝ)^3 / (2 * (1 + r^3))) * Real.log (4 * (1^3 / (2 * (1 + r^3)))) = _
  simp only [one_pow, binaryEntropy]
  have hlo : 4 * (r^3 / (2 * (1 + r^3))) = 2 * r^3 / (1 + r^3) := by
    field_simp [hm.ne'] <;> ring
  have hhi : 4 * (1 / (2 * (1 + r^3))) = 2 / (1 + r^3) := by
    field_simp [hm.ne'] <;> ring
  rw [hlo, hhi]
  field_simp [hm.ne'] <;> ring

private theorem exact_pair_reduction {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (w : Fin 4 → Fin 4 → ℝ) (hrows : ∀ i, (∑ j, sym w i j) = 2) :
    normalizedCubicDeficit h (repeatedRoots r 1) w =
      C h - C (h / 3) - K h * (binaryEntropy r + 2 * Real.log (C h)) +
        A (C (h / 3)) r * cutMass w - B (G h) (S (h / 3)) r * cutImbalance w := by
  let M := 2 * (1 + r^3)
  have hmass : cubicMass (repeatedRoots r 1) = M := by rw [pair_mass]; dsimp [M]; ring
  rw [normalizedCubicDeficit, relativeEntropy, sum_log_repeated hr]
  have h0 := hrows 0
  have h1 := hrows 1
  have h2 := hrows 2
  have h3 := hrows 3
  simp only [Fin.sum_univ_four, sym] at h0 h1 h2 h3
  have hlow : 2 * (w 0 0 + w 0 1 + w 1 0 + w 1 1) + lowToHigh w + highToLow w = 4 := by
    unfold lowToHigh highToLow
    linarith only [h0, h1]
  have hhigh : 2 * (w 2 2 + w 2 3 + w 3 2 + w 3 3) + lowToHigh w + highToLow w = 4 := by
    unfold lowToHigh highToLow
    linarith only [h2, h3]
  have hden : 0 < 1 + r^3 := by positivity
  have hFm : K h * h = thermalFactor h / 2 := by
    unfold K
    field_simp [hh.ne'] <;> ring
  rw [hmass, mul_sub, ← mul_assoc, hFm]
  simp only [lowToHigh, highToLow] at hlow hhigh
  simp only [scaledCubicEnergy, orientationMoment, edgeSum, spectrumOf, repeatedRoots,
    Fin.sum_univ_four, A, B, G, cutMass, cutImbalance, lowToHigh, highToLow, M,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, one_pow, one_mul, mul_one]
  have hconst : r^3 / (2 * (1 + r^3)) + 1 / (2 * (1 + r^3)) = 1 / 2 := by
    field_simp [hden.ne'] <;> ring
  let hlcoef : ℝ := (C h - C (h / 3)) * (r^3 / (2 * (1 + r^3))) / 2
  let hhcoef : ℝ := (C h - C (h / 3)) * (1 / (2 * (1 + r^3))) / 2
  linear_combination (norm := (dsimp only [hlcoef, hhcoef]; field_simp [hden.ne'] <;> ring))
    hlcoef * hlow + hhcoef * hhigh + (2 * (C h - C (h / 3))) * hconst

private theorem pair_rational_identity {c s g r : ℝ}
    (hc : 1 ≤ c) (hcs : c^2 - s^2 = 1)
    (hg : g = s * (4 * c^2 + 1) / (4 * c^2 - 1))
    (hr : 0 ≤ r) (hr1 : r < 1) :
    A c r / 2 + L c - (B g s r)^2 / A c r =
      vOf r / (1 + 3 * vOf r) * (Hinf c + Hextra c - Hextra c * vOf r) := by
  let p := (1 - r) / (1 + r)
  let v := vOf r
  have hp : 0 < p := div_pos (sub_pos.mpr hr1) (by positivity)
  have hv : 0 < v := sq_pos_of_pos hp
  have hpv : p^2 = v := rfl
  have hc0 : 0 < c := by linarith
  have h4c : 0 < 4 * c^2 - 1 := by nlinarith only [hc, sq_nonneg (c - 1)]
  have h3v : 0 < 1 + 3 * v := by positivity
  have h1r : 0 < 1 + r := by positivity
  have h1r3 : 0 < 1 + r^3 := by positivity
  have hA : A c r = 2 * c * v / (1 + 3 * v) := by
    unfold A
    dsimp only [v, vOf] at h3v ⊢
    field_simp [h3v.ne', h1r.ne', h1r3.ne'] <;> ring
  have hB : B g s r = 2 * p * s * (2 * c^2 + 1 + 2 * c^2 * v) /
      ((1 + 3 * v) * (4 * c^2 - 1)) := by
    rw [B, hg]
    dsimp only [p, v, vOf] at h3v ⊢
    field_simp [h3v.ne', h1r.ne', h1r3.ne', h4c.ne'] <;> ring
  have hs2 : s^2 = c^2 - 1 := by linarith
  have hBB : (B g s r)^2 / A c r =
      2 * (c^2 - 1) * (2 * c^2 + 1 + 2 * c^2 * v)^2 /
        (c * (1 + 3 * v) * (4 * c^2 - 1)^2) := by
    rw [hA, hB, div_pow]
    simp only [mul_pow, hpv, hs2]
    field_simp [hc0.ne', hv.ne', h3v.ne', h4c.ne'] <;> ring
  rw [hBB, hA]
  change _ = v / (1 + 3 * v) * (Hinf c + Hextra c - Hextra c * v)
  unfold Hinf Hextra L
  field_simp [hc0.ne', h3v.ne', h4c.ne'] <;> ring

private theorem scalar_margin {h v : ℝ} (hh : 0 < h) (hhmax : h ≤ 101 / 200)
    (hv : 0 ≤ v) :
    2 * h^4 / 125 ≤ D0 h + v / (1 + 3 * v) * (R h + q h * v) := by
  obtain ⟨hD, hR, _, hq⟩ := coefficient_bounds hh hhmax
  have hd : 0 < 1 + 3 * v := by positivity
  have hnum : -(h^8 / 100) ≤ v * (R h + q h * v) := by
    have ha := mul_le_mul_of_nonneg_left hR hv
    have hb := mul_le_mul_of_nonneg_right hq (sq_nonneg v)
    nlinarith only [ha, hb, sq_nonneg (v / 2 - h^4 / 10)]
  have hquot : -(h^8 / 100) ≤ v / (1 + 3 * v) * (R h + q h * v) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).2
    have hn : 0 ≤ (h^8 / 100) * v := by positivity
    nlinarith only [hn, hnum]
  have h4 : h^4 ≤ (1 / 15 : ℝ) := (pow_le_pow_left₀ hh.le hhmax 4).trans (by norm_num)
  have h8 : h^8 ≤ h^4 / 15 := by
    have hm := mul_le_mul_of_nonneg_left h4 (pow_nonneg hh.le 4)
    nlinarith only [hm]
  linarith only [hD, hquot, h8]

private theorem repeatedPair_core {h r : ℝ} {w : Fin 4 → Fin 4 → ℝ}
    (hh : 0 < h) (hhmax : h ≤ 101 / 200) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrows : ∀ i, (∑ j, sym w i j) = 2) (hdiag : ∀ i, w i i = 1 / 4)
    (hd : ∀ i, |rowImbalance w i| ≤ 1) (hcap : DirectedCaps w) :
    2 * h^4 / 125 ≤ normalizedCubicDeficit h (repeatedRoots r 1) w := by
  let c := C (h / 3)
  let s := S (h / 3)
  obtain ⟨hc, _, hcs, _, _, hG, hK⟩ := hyperbolic_parameters hh
  change 1 ≤ c at hc
  change c^2 - s^2 = 1 at hcs
  change G h = s * (4 * c^2 + 1) / (4 * c^2 - 1) at hG
  have hc0 : 0 < c := by linarith
  have hcut := cut_support hrows hdiag hd hcap
  rw [exact_pair_reduction hh hr w hrows]
  change _ ≤ C h - c - K h * (binaryEntropy r + 2 * Real.log (C h)) +
    A c r * cutMass w - B (G h) s r * cutImbalance w
  rcases hr1.eq_or_lt with heq | hrlt
  · subst r
    have hL : 0 ≤ L c := by
      have h1 : 0 ≤ c^2 - 1 := by nlinarith only [hc, sq_nonneg (c - 1)]
      unfold L
      positivity
    have hD := (coefficient_bounds hh hhmax).1
    change h^4 / 60 ≤ C h - c - 2 * K h * Real.log (C h) - L c at hD
    norm_num [A, B, binaryEntropy] <;> linarith only [hD, hL, pow_nonneg hh.le 4]
  have hAr : 0 < A c r := by
    have hgap : 0 < 1 - r := sub_pos.mpr hrlt
    unfold A
    positivity
  have hsquare : A c r / 2 - (B (G h) s r)^2 / A c r ≤
      A c r * cutMass w - B (G h) s r * cutImbalance w := by
    have hg := mul_le_mul_of_nonneg_left hcut hAr.le
    calc
      A c r / 2 - (B (G h) s r)^2 / A c r ≤
          A c r * (1 / 2 + (cutImbalance w)^2 / 4) -
            B (G h) s r * cutImbalance w := by
        apply (mul_le_mul_iff_right₀ hAr).mp
        rw [mul_sub, mul_div_cancel₀ _ hAr.ne']
        nlinarith only [sq_nonneg (A c r * cutImbalance w / 2 - B (G h) s r)]
      _ ≤ _ := sub_le_sub_right hg _
  have hE := mul_le_mul_of_nonneg_left (binaryEntropy_le_support hr hrlt.le) hK.le
  have halg : C h - c - K h * (entropySupport (vOf r) + 2 * Real.log (C h)) +
      (A c r / 2 - (B (G h) s r)^2 / A c r) =
      D0 h + vOf r / (1 + 3 * vOf r) * (R h + q h * vOf r) := by
    have he := pair_rational_identity hc hcs hG hr hrlt
    have he' : A c r / 2 - (B (G h) s r)^2 / A c r =
        vOf r / (1 + 3 * vOf r) * (Hinf c + Hextra c - Hextra c * vOf r) - L c := by
      linarith only [he]
    rw [he']
    unfold D0 R q entropySupport
    change _ = C h - c - 2 * K h * Real.log (C h) - L c + _
    change _ = C h - c - 2 * K h * Real.log (C h) - L c +
      vOf r / (1 + 3 * vOf r) *
        (Hinf c + Hextra c - 9 / 2 * K h + (3 / 2 * K h - Hextra c) * vOf r)
    ring
  have hmargin := scalar_margin hh hhmax (show 0 ≤ vOf r from sq_nonneg _)
  rw [← halg] at hmargin
  linarith only [hmargin, hsquare, hE]

/-- The quantitative bound on the revised fixed-even directed relaxation.
The endpoints (r=0) and (r=1) are included. -/
theorem repeatedPair_relaxation {h r m : ℝ} {w : Fin 4 → Fin 4 → ℝ}
    (hh : 0 < h) (hhmax : h ≤ 101 / 200) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hcar : CARConstraints (spectrumOf (repeatedRoots r 1) (cubicMass (repeatedRoots r 1)))
      w (fun _ => 1 / 2) m)
    (hd : ∀ i, |rowImbalance w i| ≤ 1) (hcap : DirectedCaps w) :
    2 * h^4 / 125 ≤ normalizedCubicDeficit h (repeatedRoots r 1) w :=
  repeatedPair_core hh hhmax hr hr1 hcar.combined_marginal
    (fun i => (hcar.diagonal i).trans (by norm_num)) hd hcap

private abbrev Mat := WuCubicDirectedOccupationCap.Mat
private abbrev lowering := WuCubicDirectedOccupationCap.lowering

private theorem frame_odd (U : unitary Mat) (i : Fin 4) :
    oddProbability (frameVector U i) = 1 - evenProbability (frameVector U i) := by
  have hU : (U : Mat)ᴴ * (U : Mat) = 1 := Unitary.coe_star_mul_self U
  have hi := congrArg (fun M : Mat => (M i i).re) hU
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.re_sum, Matrix.one_apply_eq, Complex.one_re] at hi
  have hi' : (∑ j, Complex.normSq ((U : Mat) j i)) = 1 := by
    have hentry (z : ℂ) : ((starRingEnd ℂ z) * z).re = Complex.normSq z := by
      rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
    simpa only [hentry] using hi
  simp only [Fin.sum_univ_four] at hi'
  simp only [oddProbability, evenProbability, emptyProbability, fullProbability, frameVector]
  linarith only [hi']

theorem physical_directedCaps (U : unitary Mat)
    (he : ∀ i, evenProbability (frameVector U i) = 1 / 2) : DirectedCaps (frameWeight U) := by
  have ho (i : Fin 4) : oddProbability (frameVector U i) = 1 / 2 := by
    rw [frame_odd, he i]
    norm_num
  have ha (i : Fin 4) : emptyProbability (frameVector U i) =
      (1 + rowImbalance (frameWeight U) i) / 4 := by
    have h := he i
    unfold evenProbability at h
    rw [WuCubicDirectedOccupationCap.frameWeight_rowImbalance]
    linarith only [h]
  have hb (i : Fin 4) : fullProbability (frameVector U i) =
      (1 - rowImbalance (frameWeight U) i) / 4 := by
    have h := he i
    unfold evenProbability at h
    rw [WuCubicDirectedOccupationCap.frameWeight_rowImbalance]
    linarith only [h]
  intro i j t _ tpos
  rw [WuCubicDirectedOccupationCap.frameWeight_eq_jumpWeight]
  have h := WuCubicDirectedOccupationCap.jumpWeight_le (frameVector U i)
    (frameVector U j) tpos
  rw [ha i, hb j, ho i, ho j] at h
  convert h using 1 <;> ring

private theorem lowering_matrix_entries :
    lowering 0 = !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] ∧
    lowering 1 = !![0, -1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0] := by
  have h0 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 0 = (0, 0) := rfl
  have h1 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 1 = (0, 1) := rfl
  have h2 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 2 = (1, 0) := rfl
  have h3 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 3 = (1, 1) := rfl
  constructor
  · change Matrix.reindex finProdFinEquiv finProdFinEquiv
      ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ 1) = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [h0, h1, h2, h3, Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  · change Matrix.reindex finProdFinEquiv finProdFinEquiv
      (diagonal (![-1, 1] : Fin 2 → ℂ) ⊗ₖ
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [h0, h1, h2, h3, Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.diagonal_apply]

private theorem frame_diagonal (U : unitary Mat)
    (he : ∀ i, evenProbability (frameVector U i) = 1 / 2) (i : Fin 4) :
    frameWeight U i i = 1 / 4 := by
  let x := frameVector U i
  rw [WuCubicDirectedOccupationCap.frameWeight_eq_jumpWeight]
  change WuCubicDirectedOccupationCap.jumpWeight x x = _
  have hx : WuCubicDirectedOccupationCap.jumpWeight x x = evenProbability x * oddProbability x := by
    rw [WuCubicDirectedOccupationCap.jumpWeight, Fin.sum_univ_two,
      show WuCubicDirectedOccupationCap.lowering 0 = _ from lowering_matrix_entries.1,
      show WuCubicDirectedOccupationCap.lowering 1 = _ from lowering_matrix_entries.2]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.star_apply,
      evenProbability, emptyProbability, fullProbability, oddProbability,
      Complex.normSq_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im]
    <;> ring
  have he' : evenProbability x = 1 / 2 := he i
  have ho' : oddProbability x = 1 - evenProbability x := frame_odd U i
  rw [hx, ho', he']
  norm_num

private theorem combined_frame_marginal (U : unitary Mat) (i : Fin 4) :
    (∑ j, sym (frameWeight U) i j) = 2 := by
  let f : Mat ≃⋆ₐ[ℂ] Mat := (Unitary.conjStarAlgAut ℂ Mat U).symm
  have hrow (A : Mat) : (∑ j, Complex.normSq (A i j)) = ((A * Aᴴ) i i).re := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
  have hcol (A : Mat) : (∑ j, Complex.normSq (A j i)) = ((Aᴴ * A) i i).re := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.normSq_conj] using hrow Aᴴ
  have hadj (A : Mat) : f Aᴴ = (f A)ᴴ := map_star f A
  have hCAR (k : Fin 2) : lowering k * (lowering k)ᴴ + (lowering k)ᴴ * lowering k = 1 := by
    have hk : k = 0 ∨ k = 1 := by fin_cases k <;> decide
    rcases hk with rfl | rfl
    all_goals
      change WuCubicDirectedOccupationCap.lowering _ * (WuCubicDirectedOccupationCap.lowering _)ᴴ +
        (WuCubicDirectedOccupationCap.lowering _)ᴴ * WuCubicDirectedOccupationCap.lowering _ = 1
      simp only [lowering_matrix_entries.1, lowering_matrix_entries.2]
      apply Matrix.ext
      intro a b
      fin_cases a <;> fin_cases b <;>
        norm_num [Matrix.mul_apply, Matrix.add_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_four,
          Matrix.conjTranspose_apply, Matrix.one_apply]
  calc
    _ = ∑ k : Fin 2, ((∑ j, Complex.normSq (f (lowering k) i j)) +
        (∑ j, Complex.normSq (f (lowering k) j i))) := by
      change (∑ j, ((∑ k : Fin 2, Complex.normSq (f (lowering k) i j)) +
          (∑ k : Fin 2, Complex.normSq (f (lowering k) j i)))) = _
      simp only [Finset.sum_add_distrib]
      exact congrArg₂ (· + ·)
        (Finset.sum_comm (f := fun j k => Complex.normSq (f (lowering k) i j)))
        (Finset.sum_comm (f := fun j k => Complex.normSq (f (lowering k) j i)))
    _ = ∑ _ : Fin 2, (1 : ℝ) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hrow, hcol, ← hadj, ← map_mul, ← map_mul, ← Complex.add_re, ← Matrix.add_apply,
        ← map_add, hCAR k, map_one, Matrix.one_apply_eq, Complex.one_re]
    _ = _ := by norm_num [Fin.sum_univ_two]

private theorem repeatedRoots_scaling {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h : ℝ)
    (w : Fin 4 → Fin 4 → ℝ) :
    normalizedCubicDeficit h (repeatedRoots a b) w =
      normalizedCubicDeficit h (repeatedRoots (a / b) 1) w := by
  let x := repeatedRoots a b
  let y := repeatedRoots (a / b) 1
  have hxy (i : Fin 4) : x i = b * y i := by
    fin_cases i <;> norm_num [x, y, repeatedRoots] <;> field_simp [hb.ne'] <;> ring
  have hm : 0 < cubicMass y := by
    rw [show y = repeatedRoots (a / b) 1 from rfl, pair_mass]
    have h := div_nonneg ha hb.le
    positivity
  have hM : cubicMass x = b^3 * cubicMass y := by
    unfold cubicMass
    simp only [hxy, mul_pow, Finset.mul_sum]
  have hlam : spectrumOf x (cubicMass x) = spectrumOf y (cubicMass y) := by
    funext i
    simp only [spectrumOf, hxy, hM, mul_pow]
    field_simp [hb.ne', hm.ne']
  have h21 (i j : Fin 4) :
      x i ^ 2 * x j / cubicMass x = y i ^ 2 * y j / cubicMass y := by
    rw [hxy i, hxy j, hM]
    field_simp [hb.ne', hm.ne'] <;> ring
  have h12 (i j : Fin 4) :
      x i * x j ^ 2 / cubicMass x = y i * y j ^ 2 / cubicMass y := by
    rw [hxy i, hxy j, hM]
    field_simp [hb.ne', hm.ne'] <;> ring
  change normalizedCubicDeficit h x w = normalizedCubicDeficit h y w
  simp only [normalizedCubicDeficit, relativeEntropy, scaledCubicEnergy, hlam, h21, h12]

/-- The repeated-pair bound for every complex two-CAR occupation frame whose
four vectors each have even probability (1/2). The ordered nonnegative
cube-root parameters allow a zero lower pair and equality of the two pairs. -/
theorem physical_repeatedPair {h a b : ℝ} (hh : 0 < h) (hhmax : h ≤ 101 / 200)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (U : unitary Mat)
    (he : ∀ i, evenProbability (frameVector U i) = 1 / 2) :
    2 * h^4 / 125 ≤ normalizedCubicDeficit h (repeatedRoots a b) (frameWeight U) := by
  rw [repeatedRoots_scaling ha hb]
  exact repeatedPair_core hh hhmax (div_nonneg ha hb.le)
    ((div_le_iff₀ hb).2 (by simpa using hab)) (combined_frame_marginal U)
    (frame_diagonal U he)
    (fun i => by
      simpa [he i] using WuCubicDirectedOccupationCap.frameWeight_abs_rowImbalance_le U i)
    (physical_directedCaps U he)

private theorem mixed_gibbs_rpow {u v d : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hd : 0 < d)
    (h : ℝ) :
    (Real.exp h * u^3 / d) ^ (1 - 1 / 3 : ℝ) *
      (Real.exp (-h) * v^3 / d) ^ (1 / 3 : ℝ) =
      Real.exp (h / 3) * (u^2 * v) / d := by
  rw [Real.div_rpow (by positivity : 0 ≤ Real.exp h * u^3) hd.le,
    Real.div_rpow (by positivity : 0 ≤ Real.exp (-h) * v^3) hd.le,
    Real.mul_rpow (Real.exp_pos h).le (pow_nonneg hu 3),
    Real.mul_rpow (Real.exp_pos (-h)).le (pow_nonneg hv 3),
    ← Real.exp_mul, ← Real.exp_mul, ← Real.rpow_natCast_mul hu, ← Real.rpow_natCast_mul hv]
  norm_num only [Nat.cast_ofNat, show (3 * (1 - 1 / 3) : ℝ) = 2 by norm_num,
    show (3 * (1 / 3) : ℝ) = 1 by norm_num, Real.rpow_two, Real.rpow_one]
  rw [div_mul_div_comm, ← Real.rpow_add hd,
    show (2 / 3 + 1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one,
    mul_mul_mul_comm, ← Real.exp_add, show h * (2 / 3) + -h * (1 / 3) = h / 3 by ring]

/-- Exact normalization against the existing spectral generator kernel.
The cubic powers formula also holds when either of the roots is zero. -/
theorem cubicEnergy_eq_spectral (h : ℝ) (x : Fin 4 → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hm : 0 < cubicMass x) (w : Fin 4 → Fin 4 → ℝ) :
    cubicEnergy h x w = (9 / 2) * ∑ i, ∑ j, w i j *
      WuModularEdgeSpectral.coshEdgeKernel (1 / 3)
        (Real.exp h / (2 * C h) * spectrumOf x (cubicMass x) i)
        (Real.exp (-h) / (2 * C h) * spectrumOf x (cubicMass x) j) := by
  let m := cubicMass x
  let d := 2 * C h * m
  have hc := Real.cosh_pos h
  have hd : 0 < d := by dsimp [d, m]; positivity
  have hentry (t : ℝ) (i : Fin 4) :
      Real.exp t / (2 * C h) * spectrumOf x m i = Real.exp t * (x i)^3 / d := by
    unfold spectrumOf d
    ring
  have hkernel (i j : Fin 4) :
      2 * C h * WuModularEdgeSpectral.coshEdgeKernel (1 / 3)
        (Real.exp h / (2 * C h) * spectrumOf x m i)
        (Real.exp (-h) / (2 * C h) * spectrumOf x m j) =
      (C h + S h) / 2 * spectrumOf x m i + (C h - S h) / 2 * spectrumOf x m j -
        (C (h / 3) + S (h / 3)) / 2 * ((x i)^2 * x j / m) -
        (C (h / 3) - S (h / 3)) / 2 * (x i * (x j)^2 / m) := by
    have hi : 0 ≤ Real.exp h * (x i)^3 / d := by have := hx i; positivity
    have hj : 0 ≤ Real.exp (-h) * (x j)^3 / d := by have := hx j; positivity
    rw [hentry, hentry, ← WuModularEdgeSpectral.edgeKernel_eq_cosh
      (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1) hi hj]
    change _ * ((_ + _ -
      ((Real.exp (-h) * (x j)^3 / d) ^ (1 - 1 / 3 : ℝ) *
        (Real.exp h * (x i)^3 / d) ^ (1 / 3 : ℝ) +
       (Real.exp h * (x i)^3 / d) ^ (1 - 1 / 3 : ℝ) *
        (Real.exp (-h) * (x j)^3 / d) ^ (1 / 3 : ℝ))) / 2) = _
    have hneg := mixed_gibbs_rpow (hx j) (hx i) hd (-h)
    rw [neg_neg, neg_div] at hneg
    rw [hneg, mixed_gibbs_rpow (hx i) (hx j) hd h]
    simp only [Real.cosh_add_sinh, Real.cosh_sub_sinh, spectrumOf, d]
    have hm' : 0 < m := hm
    field_simp [hc.ne', hm'.ne'] <;> ring
  have hscaled : scaledCubicEnergy (C h) (S h) (C (h / 3)) (S (h / 3)) x m w =
      2 * C h * ∑ i, ∑ j, w i j *
        WuModularEdgeSpectral.coshEdgeKernel (1 / 3)
          (Real.exp h / (2 * C h) * spectrumOf x m i)
          (Real.exp (-h) / (2 * C h) * spectrumOf x m j) := by
    unfold scaledCubicEnergy
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [mul_left_comm, hkernel]
  unfold cubicEnergy
  change 9 / (4 * C h) * scaledCubicEnergy (C h) (S h) (C (h / 3)) (S (h / 3)) x m w = _
  rw [hscaled]
  field_simp [hc.ne'] <;> ring

/-- The entropy normalization in a physical frame, with the two-mode
partition function `(2 * cosh h)^2` and charge `N - I`. This also holds
when some spectral masses vanish. -/
theorem relativeEntropy_eq_frameGibbs (h : ℝ) (x : Fin 4 → ℝ) (U : unitary Mat)
    (hm : 0 < cubicMass x) :
    let lam := spectrumOf x (cubicMass x)
    relativeEntropy h x (frameWeight U) =
      (∑ i, lam i * Real.log (lam i)) + 2 * Real.log (2 * C h) -
        2 * h * ∑ i, lam i *
          (fullProbability (frameVector U i) - emptyProbability (frameVector U i)) := by
  let lam := spectrumOf x (cubicMass x)
  let w := frameWeight U
  change relativeEntropy h x w = _
  have hmass : (∑ i, lam i) = 1 := by
    simp only [lam, spectrumOf, ← Finset.sum_div]
    exact div_self hm.ne'
  have hpoint (l : ℝ) : l * Real.log (4 * l) = l * Real.log l + l * Real.log 4 := by
    by_cases hl : l = 0
    · simp [hl]
    · rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hl]
      ring
  have hsum : (∑ i, lam i * Real.log (4 * lam i)) =
      (∑ i, lam i * Real.log (lam i)) + Real.log 4 := by
    simp only [hpoint, Finset.sum_add_distrib, ← Finset.sum_mul, hmass, one_mul]
  have hlog : Real.log 4 + 2 * Real.log (C h) = 2 * Real.log (2 * C h) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.cosh_pos h).ne',
      show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
    <;> ring
  have hmom : orientationMoment lam w = -(∑ i, lam i * rowImbalance w i) := by
    simp only [orientationMoment, edgeSum, rowImbalance, Fin.sum_univ_four]
    ring
  change (∑ i, lam i * Real.log (4 * lam i)) + 2 * Real.log (C h) -
      h * orientationMoment lam w = _
  rw [hsum, hmom]
  simp only [w, WuCubicDirectedOccupationCap.frameWeight_rowImbalance, Fin.sum_univ_four]
  linear_combination hlog

/-- The same bound in the ordinary-trace units of Wu's sharp inequality. -/
theorem physical_repeatedPair_ordinaryTrace {h a b : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 101 / 200) (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b)
    (U : unitary Mat) (he : ∀ i, evenProbability (frameVector U i) = 1 / 2) :
    9 * h^4 / (250 * C h) ≤ cubicEnergy h (repeatedRoots a b) (frameWeight U) -
      sharpCoefficient h * relativeEntropy h (repeatedRoots a b) (frameWeight U) := by
  have hbound := physical_repeatedPair hh hhmax ha hab hb U he
  rw [normalizedCubicDeficit_eq hh] at hbound
  have hscale : 0 < (4 * C h / 9 : ℝ) := by positivity
  have hprod : (4 * C h / 9) * (9 * h^4 / (250 * C h)) = 2 * h^4 / 125 := by
    field_simp [(Real.cosh_pos h).ne'] <;> ring
  exact (mul_le_mul_iff_right₀ hscale).mp (by simpa only [hprod] using hbound)

/-- The normalized spectrum has total mass one, including the lower rank case. -/
theorem repeatedSpectrum_psd {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (∀ i, 0 ≤ spectrumOf (repeatedRoots a b) (cubicMass (repeatedRoots a b)) i) ∧
      (∑ i, spectrumOf (repeatedRoots a b) (cubicMass (repeatedRoots a b)) i) = 1 := by
  have hm : 0 < cubicMass (repeatedRoots a b) := by rw [pair_mass]; positivity
  constructor
  · intro i
    have hi : 0 ≤ repeatedRoots a b i := by
      fin_cases i <;> simp [repeatedRoots, ha, hb.le]
    exact div_nonneg (pow_nonneg hi 3) hm.le
  · simp only [spectrumOf, ← Finset.sum_div]
    exact div_self hm.ne'

/-- Realization of every repeated spectrum as a trace-one positive semidefinite
density in the specified frame, including the spectrum with two zero masses. -/
theorem frameDensity_psd_trace {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (U : unitary Mat) :
    let lam := spectrumOf (repeatedRoots a b) (cubicMass (repeatedRoots a b))
    let ρ := (U : Mat) * diagonal (fun i => (lam i : ℂ)) * (U : Mat)ᴴ
    ρ.PosSemidef ∧ ρ.trace = 1 := by
  let lam := spectrumOf (repeatedRoots a b) (cubicMass (repeatedRoots a b))
  obtain ⟨hpos, hsum⟩ := repeatedSpectrum_psd ha hb
  let D : Mat := diagonal (fun i => (lam i : ℂ))
  change ((U : Mat) * D * (U : Mat)ᴴ).PosSemidef ∧
    ((U : Mat) * D * (U : Mat)ᴴ).trace = 1
  have hD : D.PosSemidef := PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (hpos i))
  refine ⟨hD.mul_mul_conjTranspose_same (U : Mat), ?_⟩
  have hU : (U : Mat)ᴴ * (U : Mat) = 1 := Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_cycle, hU, one_mul]
  change (diagonal (fun i => (lam i : ℂ))).trace = 1
  rw [Matrix.trace_diagonal]
  exact_mod_cast hsum

end

end D5.S3.Quantum.Semigroups.WuCubicBalancedRepeatedPairs
