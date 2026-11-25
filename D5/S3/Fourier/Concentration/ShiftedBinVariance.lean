/- GID: D5 / S3 / Fourier / Concentration / ShiftedBinVariance
   generality: G
   mirror - B: D5 / B / S3 / Fourier / Concentration / ShiftedBinVariance
   mirror - E: none(waiver:evidence - not - specified - by - formal - manifest)
   anchors: []
   utility: none
   digest: Common shifted rounding and a parabolic lattice test give a collision lower bound. -/

import D5.S3.Fourier.Concentration.FiniteCollisionVariance
import D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
import D5.S1.Words.Mechanical.FloorFractShift

/-! A shared shift controls the weighted integer - bin variance before applying Cauchy–Schwarz. -/

open Finset Set MeasureTheory
open scoped Interval

noncomputable section

namespace D5.S3.Fourier.Concentration.ShiftedBinVariance

open D5.S1.Words.Mechanical.FloorFractShift
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

private theorem shifted_floor (z u : ℝ) (hu : u ∈ Ico (0 : ℝ) 1) :
    ⌊z + u⌋ = ⌊z⌋ + if 1 - Int.fract z ≤ u then 1 else 0 := by
  have h := floor_fract_add_indicator u z
  rw [Int.fract_eq_self.mpr ⟨hu.1, hu.2⟩, add_comm u z] at h
  exact h

private theorem square_average (z : ℝ) :
    IntervalIntegrable (fun u : ℝ => (⌊z + u⌋ : ℝ) ^ 2) volume 0 1 ∧
    (∫ u in (0 : ℝ)..1, (⌊z + u⌋ : ℝ) ^ 2) = z ^ 2 + Int.fract z * (1 - Int.fract z) := by
  let r := 1 - Int.fract z
  let m : ℝ := ⌊z⌋
  let f := fun u : ℝ => (⌊z + u⌋ : ℝ) ^ 2
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [Int.fract_lt_one z]
  have hr1 : r ≤ 1 := by dsimp [r]; linarith [Int.fract_nonneg z]
  have hlow : EqOn f (fun _ => m ^ 2) (Ioo 0 r) := by
    intro u hu
    have hmem : u ∈ Ico (0 : ℝ) 1 := ⟨hu.1.le, hu.2.trans_le hr1⟩
    have hshift := shifted_floor z u hmem
    rw [ite_eq_right (not_le.mpr hu.2), add_zero] at hshift
    simp [f, m, hshift]
  have hhigh : EqOn f (fun _ => (m + 1) ^ 2) (Ioo r 1) := by
    intro u hu
    have hmem : u ∈ Ico (0 : ℝ) 1 := ⟨hr0.trans hu.1.le, hu.2⟩
    have hshift := shifted_floor z u hmem
    rw [ite_eq_left hu.1.le] at hshift
    simp [f, m, hshift]
  have hil : IntervalIntegrable f volume 0 r :=
    intervalIntegrable_const.congr_uIoo (by rw [uIoo_of_le hr0]; exact hlow.symm)
  have hih : IntervalIntegrable f volume r 1 :=
    intervalIntegrable_const.congr_uIoo (by rw [uIoo_of_le hr1]; exact hhigh.symm)
  constructor
  · exact hil.trans hih
  · change (∫ u in (0 : ℝ)..1, f u) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals hil hih,
      intervalIntegral.integral_congr_Ioo_of_le hr0 hlow,
      intervalIntegral.integral_congr_Ioo_of_le hr1 hhigh]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    dsimp [r, m]
    calc
      _ = ((⌊z⌋ : ℝ) + Int.fract z) ^ 2 + Int.fract z * (1 - Int.fract z) := by ring
      _ = _ := by rw [Int.floor_add_fract]

/-- One shift works for the whole finite family, with the exact weighted rounding penalty. -/
theorem exists_shifted_squared_moment {I : Type*} (s : Finset I) (z c : I → ℝ) :
    let roundingPenalty := fun x : ℝ => Int.fract x * (1 - Int.fract x)
    ∃ u ∈ Ico (0 : ℝ) 1,
      (∑ i ∈ s, c i * (⌊z i + u⌋ : ℝ) ^ 2) ≤
        ∑ i ∈ s, c i * ((z i) ^ 2 + roundingPenalty (z i)) := by
  classical
  dsimp only
  let f := fun u : ℝ => ∑ i ∈ s, c i * (⌊z i + u⌋ : ℝ) ^ 2
  let M := ∑ i ∈ s, c i * ((z i) ^ 2 + Int.fract (z i) * (1 - Int.fract (z i)))
  have hi : ∀ i ∈ s, IntervalIntegrable (fun u : ℝ => c i * (⌊z i + u⌋ : ℝ) ^ 2) volume 0 1 :=
    fun i _ => (square_average (z i)).1.const_mul _
  have hf : IntervalIntegrable f volume 0 1 := by
    have heq : (∑ i ∈ s, fun u : ℝ => c i * (⌊z i + u⌋ : ℝ) ^ 2) = f := by
      funext u
      simp [f]
    rw [← heq]
    exact IntervalIntegrable.sum s hi
  have hmean : (∫ u in (0 : ℝ)..1, f u) = M := by
    dsimp [f, M]
    rw [intervalIntegral.integral_finsetSum hi]
    simp_rw [intervalIntegral.integral_const_mul, (square_average _).2]
  by_contra! h
  have hp : 0 < ∫ u in (0 : ℝ)..1, (f u - M) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hf.sub intervalIntegrable_const)
      (fun u hu => sub_pos.mpr (h u ⟨hu.1.le, hu.2⟩)) zero_lt_one
  rw [intervalIntegral.integral_sub hf intervalIntegrable_const, hmean,
    intervalIntegral.integral_const] at hp
  norm_num at hp

private def parabola (r : ℕ) (k : ℤ) : ℝ := max 0 (1 - (k : ℝ) ^ 2 / (r : ℝ) ^ 2)

private theorem parabola_value {r : ℕ} (hr : 0 < r) (k : ℤ) (hk : k ∈ latticeInterval r) :
    parabola r k = 1 - (k : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
  have h := (sq_le_iff_mem k r).mpr hk
  have hr2 : 0 < (r : ℝ) ^ 2 := by positivity
  unfold parabola
  rw [max_eq_right (sub_nonneg.mpr ((div_le_one hr2).mpr h))]

private theorem parabola_zero {r : ℕ} (hr : 0 < r) {k : ℤ} (hk : k ∉ latticeInterval r) :
    parabola r k = 0 := by
  have hh : (r : ℝ) ^ 2 < (k : ℝ) ^ 2 := lt_of_not_ge fun h => hk ((sq_le_iff_mem k r).mp h)
  have hr2 : 0 < (r : ℝ) ^ 2 := by positivity
  unfold parabola
  rw [max_eq_left (sub_nonpos.mpr ((one_le_div hr2).mpr hh.le))]

private theorem parabola_sq_sum (r : ℕ) (hr : 0 < r) :
    (∑ k ∈ latticeInterval r, parabola r k ^ 2) =
      16 * (r : ℝ) / 15 - 1 / (15 * (r : ℝ) ^ 3) := by
  have hr0 : (r : ℝ)≠0 := by positivity
  calc
    _ = ∑ k ∈ latticeInterval r,
        (1 - 2 * (k : ℝ) ^ 2 / (r : ℝ) ^ 2 + (k : ℝ) ^ 4 / (r : ℝ) ^ 4) := by
      apply sum_congr rfl
      intro k hk
      rw [parabola_value hr k hk]
      field_simp
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul,
        ← sum_div, ← mul_sum, ← sum_div, card_latticeInterval,
        sum_lattice_square, sum_lattice_fourth]
      field_simp
      ring

private theorem bin_parabola_bound {I : Type*} (s : Finset I) (b : I → ℤ) (c : I → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (r : ℕ) (hr : 0 < r) (M : ℝ) (hM : M ≤ (r : ℝ) ^ 2)
    (hm : ∑ i ∈ s, c i * (b i : ℝ) ^ 2 ≤ M*∑ i ∈ s, c i) :
    (∑ i ∈ s, c i) ^ 2 * (1 - M / (r : ℝ) ^ 2) ^ 2 ≤
      (16 * (r : ℝ) / 15 - 1 / (15 * (r : ℝ) ^ 3))*
        ∑ k ∈ s.image b, (∑ i ∈ s with b i = k, c i) ^ 2 := by
  classical
  let bins := s.image b
  let mass := fun k => ∑ i ∈ s with b i = k, c i
  let W := ∑ i ∈ s, c i
  have hr2 : 0 < (r : ℝ) ^ 2 := by positivity
  have hpair : (∑ k ∈ bins, mass k * parabola r k) = ∑ i ∈ s, c i * parabola r (b i) := by
    rw [← sum_fiberwise_of_maps_to (fun _ hi => mem_image_of_mem b hi)
      (fun i => c i * parabola r (b i))]
    apply sum_congr rfl
    intro k hk
    dsimp [mass]
    rw [sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [(mem_filter.mp hi).2]
  have hline : W * (1 - M / (r : ℝ) ^ 2) ≤ ∑ k ∈ bins, mass k * parabola r k := by
    rw [hpair]
    calc
      _ ≤ ∑ i ∈ s, c i * (1 - (b i : ℝ) ^ 2 / (r : ℝ) ^ 2) := by
        simp only [mul_sub, mul_one, sum_sub_distrib]
        simp_rw [← mul_div_assoc, ← sum_div]
        dsimp [W]
        have h := div_le_div_of_nonneg_right hm hr2.le
        rw [mul_comm M] at h
        linarith
      _ ≤ _ := sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (le_max_right _ _) (hc i hi)
  have hnon : 0 ≤ W * (1 - M / (r : ℝ) ^ 2) :=
    mul_nonneg (sum_nonneg hc) (sub_nonneg.mpr ((div_le_one hr2).mpr hM))
  have hq : (∑ k ∈ bins, parabola r k ^ 2) ≤
      16 * (r : ℝ) / 15 - 1 / (15 * (r : ℝ) ^ 3) := by
    rw [← parabola_sq_sum r hr]
    calc
      _ = ∑ k ∈ bins ∩ latticeInterval r, parabola r k ^ 2 := by
        symm
        apply sum_subset inter_subset_left
        intro k hk hnot
        have hk' : k ∉ latticeInterval r := fun hh => hnot (mem_inter.mpr ⟨hk, hh⟩)
        simp [parabola_zero hr hk']
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg inter_subset_right fun _ _ _ => sq_nonneg _
  calc
    _ = (W * (1 - M / (r : ℝ) ^ 2)) ^ 2 := by dsimp [W]; ring
    _ ≤ (∑ k ∈ bins, mass k * parabola r k) ^ 2 := pow_le_pow_left₀ hnon hline 2
    _ ≤ (∑ k ∈ bins, parabola r k ^ 2) * (∑ k ∈ bins, mass k ^ 2) := by
      simpa only [mul_comm] using sum_mul_sq_le_sq_mul_sq bins mass (parabola r)
    _ ≤ _ := mul_le_mul_of_nonneg_right hq (sum_nonneg fun _ _ => sq_nonneg _)

/-- A shifted-bin parabolic test bounds the collision mass using a weighted second moment. -/
theorem collision_parabolic_lower {I : Type*} (s : Finset I) (x c : I → ℝ)
    (a V η : ℝ) (hη : 0 < η) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hm : ∑ i ∈ s, c i * (x i - a) ^ 2 ≤ V * ∑ i ∈ s, c i)
    (r : ℕ) (hr : 0 < r) (hM : V / η ^ 2 + 1 / 4 ≤ (r : ℝ) ^ 2) :
    let W := ∑ i ∈ s, c i
    let M := V / η ^ 2 + 1 / 4
    let factor := fun n : ℕ => 16 * (n : ℝ) / 15 - 1 / (15 * (n : ℝ) ^ 3)
    W ^ 2 * (1 - M / (r : ℝ) ^ 2) ^ 2 ≤
      factor r * nearCollisionMass s x c η := by
  classical
  intro W M factor
  let z := fun i => (x i - a) / η
  obtain ⟨u, hu, hround⟩ := exists_shifted_squared_moment s z c
  let b := fun i => ⌊z i + u⌋
  have hmround : (∑ i ∈ s, c i * (b i : ℝ) ^ 2) ≤ M * W := by
    change _ ≤ (V / η ^ 2 + 1 / 4)*∑ i ∈ s, c i
    refine hround.trans ?_
    calc
      _ ≤ ∑ i ∈ s, c i * ((z i) ^ 2 + 1 / 4) := by
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (Int.fract (z i) - 1 / 2)]) (hc i hi)
      _ = (∑ i ∈ s, c i * (x i - a) ^ 2) / η ^ 2 + (∑ i ∈ s, c i) / 4 := by
        dsimp [z]
        simp_rw [div_pow, mul_add, ← mul_div_assoc, mul_one]
        rw [sum_add_distrib, ← sum_div, ← sum_div]
      _ ≤ _ := by
        have h := div_le_div_of_nonneg_right hm (sq_nonneg η)
        calc
          _ ≤ (V * ∑ i ∈ s, c i) / η ^ 2 + (∑ i ∈ s, c i) / 4 := add_le_add_left h _
          _ = _ := by ring
  have hbins := bin_parabola_bound s b c hc r hr M hM hmround
  have hdiag := sum_bin_mass_sq_le_nearCollisionMass s x c b η hc (by
    intro i _ j _ hb
    have hi := Int.floor_le (z i + u)
    have hj := Int.floor_le (z j + u)
    have hi' := Int.lt_floor_add_one (z i + u)
    have hj' := Int.lt_floor_add_one (z j + u)
    change (b i : ℝ) ≤ _ at hi
    change (b j : ℝ) ≤ _ at hj
    change _ < (b i : ℝ) + 1 at hi'
    change _ < (b j : ℝ) + 1 at hj'
    rw [hb] at hi hi'
    have hdiff : |z i - z j| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    dsimp [z] at hdiff
    rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hη,
      div_le_iff₀ hη, one_mul] at hdiff
    exact hdiff)
  have hfactor : 0 ≤ 16 * (r : ℝ) / 15 - 1 / (15 * (r : ℝ) ^ 3) := by
    rw [← parabola_sq_sum r hr]
    exact sum_nonneg fun _ _ => sq_nonneg _
  exact hbins.trans (mul_le_mul_of_nonneg_left hdiag hfactor)

#print axioms exists_shifted_squared_moment
#print axioms collision_parabolic_lower

end D5.S3.Fourier.Concentration.ShiftedBinVariance
