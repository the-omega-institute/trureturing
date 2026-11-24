/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortJointLower
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quartic lower bound for the undifferentiated short-gap joint moment. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMomentEnclosure
import D5.S3.Quantum.Recovery.BKMSpectralVariance
import Batteries.Tactic.OpenPrivate

/-! A fourth-order lower bound for the undifferentiated midpoint moment. -/

namespace RefinedBMV.PositiveCenter

open scoped BigOperators

noncomputable section

open private shortJointAverage_add shortJointAverage_mul shortJointAverage_le
  shortJointAverage_swap from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMidpoint
open private cosh_quartic_lower from D5.S3.Quantum.Recovery.BKMSpectralVariance
open private shortMidpointMoment_eq_gridAverage from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMomentEnclosure
open private gridAverage gridPoint from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails

/-- The lower fourth-order approximation at center `s` and gap `d`. -/
def shortJointMomentFourth (p : ℕ) (s d : ℝ) : ℝ :=
  shortMidpointMoment p 0 0 s + ((d / 2) ^ 2 / 2) * shortMidpointMoment p 1 0 s +
    ((d / 2) ^ 4 / 24) * shortMidpointMoment p 2 0 s

/-- Symmetry in the two gaps gives the quartic lower bound for the joint moment. -/
theorem shortJointMomentFourth_le (p : ℕ) (u v : ℝ) :
    shortJointMomentFourth p ((u + v) / 2) (v - u) ≤ 1 + compositionMoment p u v := by
  rw [add_comm 1 (compositionMoment p u v), compositionMoment, sub_add_cancel]
  let s := (u + v) / 2
  let q := (v - u) / 2
  let F (x y : ℝ) := Real.exp (x * u + y * v)
  change shortJointMomentFourth p s (v - u) ≤ shortJointAverage p F
  have hpair (x y : ℝ) : Real.exp (s * (x + y)) * Real.cosh (q * (y - x)) =
      (1 / 2) * (F x y + F y x) := by
    have hx : x * u + y * v = s * (x + y) + q * (y - x) := by
      dsimp only [s, q]
      ring
    have hy : y * u + x * v = s * (x + y) + -(q * (y - x)) := by
      dsimp only [s, q]
      ring
    dsimp only [F]
    rw [hx, hy]
    simp only [Real.cosh_eq, Real.exp_add]
    ring
  have havg : shortJointAverage p (fun x y ↦
      Real.exp (s * (x + y)) * Real.cosh (q * (y - x))) = shortJointAverage p F := by
    simp_rw [hpair]
    rw [shortJointAverage_mul, shortJointAverage_add, shortJointAverage_swap p F]
    ring
  have hpoly (x y : ℝ) :
      Real.exp (s * (x + y)) * (1 + (q * (y - x)) ^ 2 / 2 + (q * (y - x)) ^ 4 / 24) =
        shortMidpointMonomial s 0 0 x y + (q ^ 2 / 2) * shortMidpointMonomial s 1 0 x y +
          (q ^ 4 / 24) * shortMidpointMonomial s 2 0 x y := by
    norm_num [shortMidpointMonomial] <;> ring
  have hfourth : shortJointAverage p (fun x y ↦
      Real.exp (s * (x + y)) * (1 + (q * (y - x)) ^ 2 / 2 + (q * (y - x)) ^ 4 / 24)) =
        shortJointMomentFourth p s (v - u) := by
    simp_rw [hpoly, shortJointAverage_add, shortJointAverage_mul] <;> rfl
  rw [← hfourth, ← havg]
  exact shortJointAverage_le p fun _ _ ↦
    mul_le_mul_of_nonneg_left (cosh_quartic_lower _) (Real.exp_pos _).le

/-- The polynomial obtained by averaging the quartic over the conditional separation. -/
def shortJointFourthPolynomial (h d r : ℝ) : ℝ :=
  1 + d ^ 2 * r * (r + 2 * h) / 24 +
    d ^ 4 * r * (r + 2 * h) * (3 * r ^ 2 + 6 * h * r - 4 * h ^ 2) / 5760

/-- The quartic lower approximation as a single sum on the reflected marginal grid. -/
theorem shortJointMomentFourth_eq_gridSum {p : ℕ} (hp : 0 < p) (s d : ℝ) :
    let h := 3 / (p : ℝ)
    shortJointMomentFourth p s d =
      (2 * Real.exp (-2 * s) / ((3 + h) * (3 + 2 * h))) *
        (h * ∑ n ∈ Finset.range (p + 1),
          let r := h * n
          (r + h) * shortJointFourthPolynomial h d r * Real.exp (s * r)) := by
  intro h
  let P := shortJointFourthPolynomial h d
  let W (j : Fin 4) (z : ℝ) :=
    shortConditionalEvenWeight j h (2 + h - z) * Real.exp (-z * s)
  have hm (j : Fin 4) : shortMidpointMoment p j 0 s = gridAverage p (W j) := by
    simpa only [W, h, pow_zero, mul_one] using shortMidpointMoment_eq_gridAverage hp j 0 s
  have hgrid : shortJointMomentFourth p s d =
      gridAverage p (fun z ↦ P (2 - z) * Real.exp (-z * s)) := by
    unfold shortJointMomentFourth
    change shortMidpointMoment p ((0 : Fin 4) : ℕ) 0 s +
      ((d / 2) ^ 2 / 2) * shortMidpointMoment p ((1 : Fin 4) : ℕ) 0 s +
      ((d / 2) ^ 4 / 24) * shortMidpointMoment p ((2 : Fin 4) : ℕ) 0 s = _
    rw [hm 0, hm 1, hm 2]
    unfold gridAverage
    simp only [← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    norm_num [W, P, shortJointFourthPolynomial, shortConditionalEvenWeight] <;> ring
  rw [hgrid]
  let D : ℝ := (DimThree.gaps p).length
  let F (r : ℝ) := (r + h) * P r * Real.exp (s * r)
  let G (i : ℕ) := (↑(p + 1 - i) : ℝ) *
    (P (2 - gridPoint p i) * Real.exp (-(gridPoint p i) * s))
  have hh : 0 < h := by dsimp only [h]; positivity
  have hscale : h * (p : ℝ) = 3 := by
    dsimp only [h]
    exact div_mul_cancel₀ _ (by exact_mod_cast hp.ne')
  have hsum : (∑ i ∈ Finset.range (p + 1), G i) =
      (Real.exp (-2 * s) / h) * ∑ n ∈ Finset.range (p + 1), F (h * n) := by
    rw [← Finset.sum_range_reflect G (p + 1), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hindex : p + 1 - 1 - n = p - n := by omega
    have hmult : p + 1 - (p - n) = n + 1 := by omega
    have hz : gridPoint p (p - n) = 2 - h * n := by
      change h * ((p - n : ℕ) : ℝ) - 1 = _
      rw [Nat.cast_sub hn']
      linear_combination hscale
    rw [hindex]
    dsimp only [G, F]
    rw [hmult, hz, Nat.cast_add, Nat.cast_one,
      show 2 - (2 - h * (n : ℝ)) = h * n by ring,
      show -(2 - h * (n : ℝ)) * s = -2 * s + s * (h * n) by ring,
      Real.exp_add]
    field_simp [hh.ne'] <;> ring
  change (∑ i ∈ Finset.range (p + 1), G i) / D =
    (2 * Real.exp (-2 * s) / ((3 + h) * (3 + 2 * h))) *
      (h * ∑ n ∈ Finset.range (p + 1), F (h * n))
  have hcountNat : 2 * (DimThree.gaps p).length = (p + 1) * (p + 2) := by
    rw [DimThree.gaps_length_eq_choose, Nat.mul_comm 2, Nat.mul_comm (p + 1) (p + 2)]
    simpa only [Nat.choose_one_right] using (Nat.add_one_mul_choose_eq (p + 1) 1).symm
  have hcount : 2 * D = ((p : ℝ) + 1) * ((p : ℝ) + 2) := by
    dsimp only [D]
    exact_mod_cast hcountNat
  have hleft : 3 + h = ((p : ℝ) + 1) * h := by linear_combination -hscale
  have hright : 3 + 2 * h = ((p : ℝ) + 2) * h := by linear_combination -hscale
  have hnorm : (3 + h) * (3 + 2 * h) = 2 * D * h ^ 2 := by
    calc
      _ = (((p : ℝ) + 1) * ((p : ℝ) + 2)) * h ^ 2 := by rw [hleft, hright]; ring
      _ = _ := by rw [← hcount]
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast (DimThree.word_counts_all p).2.1
  rw [hsum, hnorm]
  field_simp [hh.ne', hD.ne'] <;> ring

end

end RefinedBMV.PositiveCenter
