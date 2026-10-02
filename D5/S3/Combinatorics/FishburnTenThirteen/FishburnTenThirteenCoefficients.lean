/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenCoefficients
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenCoefficients
   mirror-E: none(waiver:formal-counting-series)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Substitution]
   utility: none
   digest: Coefficientwise uniqueness and Catalan extraction for the Fishburn counting equation. -/

import D5.S3.Combinatorics.Fishburn.FishburnCatalanBinomialDefs
import D5.S1.Words.Patterns.A398542Polynomial
import Mathlib.RingTheory.PowerSeries.Substitution

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenCoefficients

open PowerSeries Finset
open D5.S3.Combinatorics
open scoped PowerSeries.WithPiTopology

theorem counting_solution (series : PowerSeries ℚ)
    (hzero : constantCoeff series = 0)
    (hequation : series = X * mk (fun _ => (1 : ℚ)) + series ^ 2) :
    ∀ size : ℕ, 1 ≤ size →
      coeff size (1 + series) =
        (FishburnCatalanBinomialDefs.binomialCatalan size : ℚ) := by
  classical
  let time : PowerSeries ℚ := X * mk (fun _ => (1 : ℚ))
  let cat : PowerSeries ℚ := map (Nat.castRingHom ℚ) catalanSeries
  let candidate : PowerSeries ℚ := time * cat.subst time
  have htime : constantCoeff time = 0 := by simp [time]
  have hsubst : HasSubst time := HasSubst.of_constantCoeff_zero' htime
  have hcat : cat ^ 2 * X + 1 = cat := by
    simpa [cat] using congrArg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  have hcandidate : candidate = time + candidate ^ 2 := by
    have equation := congrArg (subst time) hcat
    rw [subst_add hsubst, subst_mul hsubst, subst_pow hsubst, subst_X hsubst] at equation
    have hone : (1 : PowerSeries ℚ).subst time = 1 := by
      simpa using (subst_C (a := time) (1 : ℚ))
    rw [hone] at equation
    dsimp [candidate]
    calc
      time * cat.subst time = time * ((cat.subst time) ^ 2 * time + 1) :=
        congrArg (time * ·) equation.symm
      _ = time + (time * cat.subst time) ^ 2 := by ring
  have hcandzero : constantCoeff candidate = 0 := by simp [candidate, htime]
  have hunique : series = candidate := by
    apply PowerSeries.ext
    intro degree
    induction degree using Nat.strong_induction_on with
    | h degree induction =>
      by_cases hdegree : degree = 0
      · subst degree
        simp only [coeff_zero_eq_constantCoeff_apply, hzero, hcandzero]
      · have hleft := congrArg (coeff degree)
          (show series = time + series ^ 2 from hequation)
        have hright := congrArg (coeff degree) hcandidate
        simp only [map_add, pow_two, coeff_mul] at hleft hright
        rw [hleft, hright]
        congr 1
        apply sum_congr rfl
        rintro ⟨left, right⟩ hpair
        have hsum := Finset.mem_antidiagonal.mp hpair
        by_cases hl : left = 0
        · subst left
          simp [coeff_zero_eq_constantCoeff_apply, hzero, hcandzero]
        by_cases hr : right = 0
        · subst right
          simp [coeff_zero_eq_constantCoeff_apply, hzero, hcandzero]
        rw [induction left (by omega), induction right (by omega)]
  have hpower (degree exponent : ℕ) : coeff degree (time ^ (exponent + 1)) =
      if exponent + 1 ≤ degree then ((degree - 1).choose exponent : ℚ) else 0 := by
    dsimp only [time]
    rw [mul_pow, coeff_X_pow_mul']
    have hp := mk_one_pow_eq_mk_choose_add ℚ exponent
    change (mk (fun _ => (1 : ℚ))) ^ (exponent + 1) = _ at hp
    rw [hp]
    split_ifs with hbound
    · rw [coeff_mk]
      congr 2
      omega
    · rfl
  have hpositive : candidate = (X * cat).subst time := by
    rw [subst_mul hsubst, subst_X hsubst]
  intro size hsize
  rw [hunique, map_add, coeff_one, if_neg (by omega), zero_add, hpositive,
    coeff_subst' hsubst]
  have hcoeff (exponent : ℕ) : coeff exponent (X * cat) =
      if exponent = 0 then 0 else (catalan (exponent - 1) : ℚ) := by
    cases exponent with
    | zero => simp
    | succ exponent => simp [cat, coeff_map, coeff_succ_X_mul]
  have hfinite : Function.support (fun exponent : ℕ =>
      coeff exponent (X * cat) • coeff size (time ^ exponent)) ⊆
      (Icc 1 size : Set ℕ) := by
    intro exponent hexponent
    simp only [Function.mem_support, smul_eq_mul] at hexponent
    have hpos : 0 < exponent := by
      by_contra h
      have he : exponent = 0 := by omega
      simp [he, hcoeff] at hexponent
    have hbound : exponent ≤ size := by
      by_contra h
      obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : exponent ≠ 0)
      rw [hpower, if_neg (by omega), mul_zero] at hexponent
      contradiction
    exact mem_Icc.mpr ⟨hpos, hbound⟩
  rw [finsum_eq_sum_of_support_subset _ hfinite]
  have hsum : (∑ exponent ∈ Icc 1 size,
      coeff exponent (X * cat) • coeff size (time ^ exponent)) =
      ∑ exponent ∈ Icc 1 size,
        (((size - 1).choose (exponent - 1) * catalan (exponent - 1) : ℕ) : ℚ) := by
    apply sum_congr rfl
    intro exponent hexponent
    have hb := mem_Icc.mp hexponent
    obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : exponent ≠ 0)
    rw [hcoeff, if_neg (by omega), hpower, if_pos hb.2]
    simp only [Nat.succ_sub_one, smul_eq_mul, Nat.cast_mul]
    ring
  rw [hsum]
  unfold FishburnCatalanBinomialDefs.binomialCatalan
  push_cast
  apply sum_bij (fun exponent _ => size + 1 - exponent)
  · intro exponent hexponent
    have hb := mem_Icc.mp hexponent
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro left hleft right hright heq
    have hl := mem_Icc.mp hleft
    have hr := mem_Icc.mp hright
    omega
  · intro exponent hexponent
    have hb := mem_Icc.mp hexponent
    refine ⟨size + 1 - exponent, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro exponent hexponent
    have hb := mem_Icc.mp hexponent
    have hindex : size + 1 - exponent - 1 = size - exponent := by omega
    have hcatindex : size - (size + 1 - exponent) = exponent - 1 := by omega
    rw [hindex, hcatindex]
    have hchoose := Nat.choose_symm (by omega : exponent - 1 ≤ size - 1)
    rw [show size - 1 - (exponent - 1) = size - exponent by omega] at hchoose
    rw [hchoose]


end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenCoefficients
