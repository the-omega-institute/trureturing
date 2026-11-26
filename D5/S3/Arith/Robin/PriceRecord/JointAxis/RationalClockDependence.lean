/- GID: D5/S3/Arith/Robin/PriceRecord/JointAxis/RationalClockDependence
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/JointAxis/RationalClockDependence
   mirror-E: none(waiver:elementary-logarithmic-arithmetic)
   anchors: []
   utility: none
   digest: Common-base classification and quantitative separation for dependent Robin labels. -/
import D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order

/-! Rational dependence of the two bases of the joint Robin logarithm. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence

open Real
open D5.S3.Arith.Robin.PriceRecord.JointAxisLogarithm (omegaThree)

/-- Multiplicative independence for bases greater than one, expressed via positive powers. -/
def RationalPowerIndependent (α β : ℚ) : Prop :=
  ¬ ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ α ^ B = β ^ A

/-- Dependence is equivalent to a coprime common-base representation whose
reduced numerator to the second exponent divides the raw second numerator. -/
theorem clock_dependent_iff_common_base {h p q : ℕ}
    (hh : 0 < h) (hp : 2 * h ≤ p) (hq : q ≤ 3 * h) :
    let α : ℚ := 3 * (p : ℚ) / ((p : ℚ) + q)
    let β : ℚ := 2 * (p : ℚ) / ((p : ℚ) + h)
    ¬ RationalPowerIndependent α β ↔
      ∃ (A B : ℕ) (t : ℚ), 0 < A ∧ 0 < B ∧ B.Coprime A ∧ 1 < t ∧
        α = t ^ A ∧ β = t ^ B ∧ t.num.toNat ^ B ∣ 2 * p := by
  classical
  let α : ℚ := 3 * (p : ℚ) / ((p : ℚ) + q)
  let β : ℚ := 2 * (p : ℚ) / ((p : ℚ) + h)
  change ¬ RationalPowerIndependent α β ↔ _
  have hp0 : 0 < p := by omega
  have hhQ : (0 : ℚ) < h := by exact_mod_cast hh
  have hpQ : (2 : ℚ) * h ≤ p := by exact_mod_cast hp
  have hqQ : (q : ℚ) ≤ 3 * h := by exact_mod_cast hq
  have hα : 1 < α := by
    change (1 : ℚ) < 3 * (p : ℚ) / ((p : ℚ) + q)
    exact (lt_div_iff₀ (by positivity)).2 (by linarith only [hhQ, hpQ, hqQ])
  have hβ : 1 < β := by
    change (1 : ℚ) < 2 * (p : ℚ) / ((p : ℚ) + h)
    exact (lt_div_iff₀ (by positivity)).2 (by linarith only [hhQ, hpQ])
  unfold RationalPowerIndependent
  constructor
  · intro hdep
    obtain ⟨A, B, hA, hB, hrel⟩ := not_not.mp hdep
    let g := B.gcd A
    let B₀ := B / g
    let A₀ := A / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_left A hB
    have hB₀ : 0 < B₀ := Nat.div_gcd_pos_of_pos_left A hB
    have hA₀ : 0 < A₀ := by
      have hgcd : A.gcd B = g := Nat.gcd_comm A B
      simpa only [hgcd] using Nat.div_gcd_pos_of_pos_left B hA
    have hBfactor : B₀ * g = B := Nat.div_mul_cancel (Nat.gcd_dvd_left B A)
    have hAfactor : A₀ * g = A := Nat.div_mul_cancel (Nat.gcd_dvd_right B A)
    have hcop : B₀.Coprime A₀ := Nat.coprime_div_gcd_div_gcd hg
    have hα0 := zero_lt_one.trans hα
    have hβ0 := zero_lt_one.trans hβ
    have hreduced : α ^ B₀ = β ^ A₀ := by
      apply (pow_left_inj₀ (pow_pos hα0 B₀).le (pow_pos hβ0 A₀).le hg.ne').1
      rw [← pow_mul, ← pow_mul, hBfactor, hAfactor]
      exact hrel
    obtain ⟨root, hαroot, hβroot⟩ := (pow_eq_pow_iff_of_coprime hcop).1 hreduced
    let t : ℚ := |root|
    have htα : t ^ A₀ = α := by
      change |root| ^ A₀ = α
      rw [← abs_pow, ← hαroot, abs_of_pos hα0]
    have htβ : t ^ B₀ = β := by
      change |root| ^ B₀ = β
      rw [← abs_pow, ← hβroot, abs_of_pos hβ0]
    have ht : 1 < t := by
      apply (one_lt_pow_iff_of_nonneg (abs_nonneg root) hB₀.ne').1
      rwa [htβ]
    let a := t.num.toNat
    let b := t.den
    have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast t.den_pos.ne'
    have htNum : 0 ≤ t.num := Rat.num_nonneg.2 (zero_le_one.trans ht.le)
    have haInt : (a : ℤ) = t.num := Int.toNat_of_nonneg htNum
    have haQ : (a : ℚ) = (t.num : ℚ) := by exact_mod_cast haInt
    have hfrac : (a : ℚ) / (b : ℚ) = t := by
      rw [haQ]
      exact Rat.num_div_den t
    have hclear : t ^ B₀ * (b : ℚ) ^ B₀ = (a : ℚ) ^ B₀ := by
      rw [← hfrac, div_pow]
      exact div_mul_cancel₀ _ (pow_ne_zero _ hbQ)
    have hβclear : β * ((p : ℚ) + h) = 2 * (p : ℚ) :=
      div_mul_cancel₀ _ (by positivity)
    have hcrossQ : (a : ℚ) ^ B₀ * ((p : ℚ) + h) = 2 * (p : ℚ) * (b : ℚ) ^ B₀ := by
      rw [← hclear, htβ, mul_right_comm, hβclear]
    have hcross : a ^ B₀ * (p + h) = 2 * p * b ^ B₀ := by exact_mod_cast hcrossQ
    have hdiv : a ^ B₀ ∣ 2 * p * b ^ B₀ := ⟨p + h, hcross.symm⟩
    have haAbs : a = t.num.natAbs :=
      Int.ofNat_inj.mp (haInt.trans (Int.natAbs_of_nonneg htNum).symm)
    have hab : a.Coprime b := haAbs ▸ t.reduced
    exact ⟨A₀, B₀, t, hA₀, hB₀, hcop, ht, htα.symm, htβ.symm,
      (hab.pow B₀ B₀).dvd_of_dvd_mul_right hdiv⟩
  · rintro ⟨A, B, t, hA, hB, _, _, hαeq, hβeq, _⟩ hind
    refine hind ⟨A, B, hA, hB, ?_⟩
    change α = t ^ A at hαeq
    change β = t ^ B at hβeq
    rw [hαeq, hβeq, ← pow_mul, ← pow_mul, Nat.mul_comm A B]

/-- A nonzero joint form on dependent labels is bounded below by the reciprocal
of the logarithm of the raw second numerator. -/
theorem dependent_clock_abs_lower {h p q : ℕ}
    (hh : 0 < h) (hp : 2 * h ≤ p) (hq : q ≤ 3 * h)
    (hne : omegaThree (h : ℝ) (p : ℝ) (q : ℝ) ≠ 0)
    (hdep : ¬ RationalPowerIndependent
      (3 * (p : ℚ) / ((p : ℚ) + q)) (2 * (p : ℚ) / ((p : ℚ) + h))) :
    log (4 / 3) * log 2 / log (2 * (p : ℝ)) ≤
      |omegaThree (h : ℝ) (p : ℝ) (q : ℝ)| := by
  obtain ⟨A, B, t, _, _, _, ht, hα, hβ, hdiv⟩ :=
    (clock_dependent_iff_common_base hh hp hq).1 hdep
  have hpR : (2 : ℝ) * h ≤ p := by exact_mod_cast hp
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast (show 2 ≤ p by omega)
  have htR : (1 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hlogt : 0 < log (t : ℝ) := log_pos htR
  have hαR : 3 * (p : ℝ) / ((p : ℝ) + q) = (t : ℝ) ^ A := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat] using congrArg (fun x : ℚ => (x : ℝ)) hα
  have hβR : 2 * (p : ℝ) / ((p : ℝ) + h) = (t : ℝ) ^ B := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat] using congrArg (fun x : ℚ => (x : ℝ)) hβ
  have hβ43 : (4 / 3 : ℝ) ≤ 2 * (p : ℝ) / ((p : ℝ) + h) :=
    (le_div_iff₀ (by positivity)).2 (by linarith only [hpR])
  have hlogβ : log (4 / 3) ≤ (B : ℝ) * log (t : ℝ) := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 4 / 3) hβ43
    rwa [hβR, log_pow] at h
  have ha : 2 ≤ t.num.toNat := by
    have haInt : (t.num.toNat : ℤ) = t.num :=
      Int.toNat_of_nonneg (Rat.num_nonneg.2 (zero_le_one.trans ht.le))
    have haQ : (t.num.toNat : ℚ) = (t.num : ℚ) := by
      simpa only [Rat.intCast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) haInt
    have hden : (0 : ℚ) < t.den := by exact_mod_cast t.den_pos
    have hfrac : (t.num.toNat : ℚ) / (t.den : ℚ) = t := by
      rw [haQ]
      exact Rat.num_div_den t
    have hltQ : (t.den : ℚ) < (t.num.toNat : ℚ) := by
      have h : (1 : ℚ) < (t.num.toNat : ℚ) / (t.den : ℚ) := by rwa [hfrac]
      simpa only [one_mul] using (lt_div_iff₀ hden).1 h
    have hlt : t.den < t.num.toNat := by exact_mod_cast hltQ
    have := t.den_pos
    omega
  have hpow : (2 : ℕ) ^ B ≤ 2 * p :=
    (pow_le_pow_left₀ (by norm_num) ha B).trans (Nat.le_of_dvd (by omega) hdiv)
  have hpowR : (2 : ℝ) ^ B ≤ 2 * (p : ℝ) := by exact_mod_cast hpow
  have hlogpow : (B : ℝ) * log 2 ≤ log (2 * (p : ℝ)) := by
    have h := log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ B) hpowR
    rwa [log_pow] at h
  have hlog2p : 0 < log (2 * (p : ℝ)) := log_pos (by linarith only [hpTwo])
  have hquot : log (4 / 3) * log 2 / log (2 * (p : ℝ)) ≤ log (t : ℝ) := by
    apply (div_le_iff₀ hlog2p).2
    calc
      _ ≤ ((B : ℝ) * log (t : ℝ)) * log 2 :=
        mul_le_mul_of_nonneg_right hlogβ (log_nonneg (by norm_num))
      _ = ((B : ℝ) * log 2) * log (t : ℝ) := by ring
      _ ≤ log (2 * (p : ℝ)) * log (t : ℝ) :=
        mul_le_mul_of_nonneg_right hlogpow hlogt.le
      _ = _ := mul_comm _ _
  let k : ℤ := (h : ℤ) * (A : ℤ) - (q : ℤ) * (B : ℤ)
  have hkR : (k : ℝ) = (h : ℝ) * A - (q : ℝ) * B := by
    simp only [k, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  have hΩ : omegaThree (h : ℝ) (p : ℝ) (q : ℝ) = (k : ℝ) * log (t : ℝ) := by
    rw [omegaThree, hαR, hβR, log_pow, log_pow, hkR]
    ring
  have hk : k ≠ 0 := by
    intro hz
    apply hne
    simp only [hΩ, hz, Int.cast_zero, zero_mul]
  have hkAbs : (1 : ℝ) ≤ |(k : ℝ)| := by
    have h : (1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast (Int.one_le_abs hk)
    simpa only [Int.cast_abs] using h
  calc
    _ ≤ log (t : ℝ) := hquot
    _ ≤ |omegaThree (h : ℝ) (p : ℝ) (q : ℝ)| := by
      rw [hΩ, abs_mul, abs_of_pos hlogt]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hkAbs hlogt.le

end D5.S3.Arith.Robin.PriceRecord.JointAxis.RationalClockDependence
