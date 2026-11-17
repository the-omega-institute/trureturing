/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalWeightAverage
   generality: G
   mirror-B: none(waiver:actual-physical-weight-average)
   mirror-E: none(waiver:actual-physical-weight-average)
   anchors: []
   utility: none
   digest: Original integer parameter incidence for the physical rational multiplicity. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalLattice
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Int.Interval

/-! Counting is in the original integer `(w,t)` rectangle. A unit short vector
identifies the actual index-p-squared lattice, so no independent slope lift is
introduced. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private def integerRectangle (U V : ℝ) : Finset Coordinate :=
  (Finset.Icc (-⌊U⌋) ⌊U⌋) ×ˢ (Finset.Icc (-⌊V⌋) ⌊V⌋)

private theorem mem_integerRectangle {U V : ℝ} {z : Coordinate}
    (hz : |(z.1 : ℝ)| ≤ U ∧ |(z.2 : ℝ)| ≤ V) :
    z ∈ integerRectangle U V := by
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    exact ⟨by have := Int.le_floor.mpr (by push_cast; linarith [abs_le.mp hz.1] :
      (-z.1 : ℤ) ≤ U); omega, Int.le_floor.mpr (abs_le.mp hz.1).2⟩
  · apply Finset.mem_Icc.mpr
    exact ⟨by have := Int.le_floor.mpr (by push_cast; linarith [abs_le.mp hz.2] :
      (-z.2 : ℤ) ≤ V); omega, Int.le_floor.mpr (abs_le.mp hz.2).2⟩

private theorem integerRectangle_card {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ((integerRectangle U V).card : ℝ) ≤ (2 * U + 1) * (2 * V + 1) := by
  have hcount (T : ℝ) (hT : 0 ≤ T) :
      ((Finset.Icc (-⌊T⌋) ⌊T⌋).card : ℝ) ≤ 2 * T + 1 := by
    have hN : 0 ≤ ⌊T⌋ := Int.floor_nonneg.mpr hT
    have he := Int.card_Icc_of_le (a := -⌊T⌋) (b := ⌊T⌋) (by omega)
    have heR : ((Finset.Icc (-⌊T⌋) ⌊T⌋).card : ℝ) =
        (⌊T⌋ : ℝ) + 1 - (-⌊T⌋ : ℤ) := by exact_mod_cast he
    rw [heR]
    push_cast
    linarith [Int.floor_le T]
  rw [integerRectangle, Finset.card_product, Nat.cast_mul]
  exact mul_le_mul (hcount U hU) (hcount V hV)
    (Nat.cast_nonneg _) (by positivity)

private theorem reduced_coordinate_abs_bounds {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y) (hc : 0 < c)
    (hX : 0 < X) (hY : 0 < Y) (H σ : ℝ) (hH : 0 < H)
    (hHsq : H ^ 2 = X * Y) (hσ : 0 < σ)
    (hσsq : σ ^ 2 = weightedSq X Y B.R)
    {z : Coordinate} (hz : physical B.R B.V z ∈ literalBox X Y) :
    |(z.1 : ℝ)| ≤ 2 * H / σ ∧
      |(z.2 : ℝ)| ≤ 2 * H * σ / c := by
  obtain ⟨hi, hj⟩ := B.coordinate_sq_bounds hc hX hY z hz
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hfirst : |(z.1 : ℝ)| * σ ≤ 2 * H := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, sq_abs, hσsq]
    nlinarith
  have hsecond : |(z.2 : ℝ)| * c ≤ 2 * H * σ := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, sq_abs]
    nlinarith [sq_nonneg H, sq_nonneg σ]
  exact ⟨(le_div_iff₀ hσ).mpr hfirst, (le_div_iff₀ hcR).mpr hsecond⟩

/-- The actual physical box section of a reduced congruence lattice has its
shortest-vector boundary term and its determinant-volume term. -/
theorem actual_middle_box_section_count {c : ℕ} {t w : ℤ} {X Y : ℝ}
    (B : ReducedMiddleBasis c t w X Y) (hc : 0 < c)
    (hX : 0 < X) (hY : 0 < Y) (H : ℝ) (hH : 0 < H)
    (hHsq : H ^ 2 = X * Y) (s : Finset Coordinate)
    (hmem : ∀ z ∈ s, z ∈ middleLattice c t w)
    (hbox : ∀ z ∈ s, z ∈ literalBox X Y) :
    let σ := Real.sqrt (weightedSq X Y B.R)
    (s.card : ℝ) ≤ 16 * (1 + H / σ + (X * Y) / c) := by
  classical
  dsimp only
  let σ := Real.sqrt (weightedSq X Y B.R)
  have hσ : 0 < σ := Real.sqrt_pos.mpr
    (weightedSq_pos hX hY (B.first_ne_zero hc))
  have hσsq : σ ^ 2 = weightedSq X Y B.R :=
    Real.sq_sqrt (weightedSq_nonneg hX hY _)
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  let cs := integerRectangle (2 * H / σ) (2 * H * σ / c)
  have hsub : s ⊆ cs.image (physical B.R B.V) := by
    intro z hz
    obtain ⟨i, j, hij⟩ := B.decompose z (hmem z hz)
    refine Finset.mem_image.mpr ⟨(i, j), ?_, hij⟩
    apply mem_integerRectangle
    exact reduced_coordinate_abs_bounds B hc hX hY H σ hH hHsq hσ hσsq
      (by simpa only [hij] using hbox z hz)
  have hcard : (s.card : ℝ) ≤ (2 * (2 * H / σ) + 1) *
      (2 * (2 * H * σ / c) + 1) := by
    calc
      (s.card : ℝ) ≤ ((cs.image (physical B.R B.V)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ (cs.card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ ≤ _ := integerRectangle_card (by positivity) (by positivity)
  have hshort : σ ^ 2 ≤ 2 * c := by
    rw [hσsq]
    exact (B.reduction_bounds hc hX hY).2.1.le
  have hboundary : H * σ / c ≤ 2 * (H / σ) := by
    apply (div_le_iff₀ hcR).mpr
    have hh : H * σ * σ ≤ 2 * H * c := by
      nlinarith [mul_le_mul_of_nonneg_left hshort hH.le]
    convert (le_div_iff₀ hσ).mpr hh using 1 <;> ring
  have hexpand : (2 * (2 * H / σ) + 1) * (2 * (2 * H * σ / c) + 1) =
      1 + 4 * (H / σ) + 4 * (H * σ / c) + 16 * ((X * Y) / c) := by
    field_simp
    nlinarith [hHsq]
  rw [hexpand] at hcard
  have hpos : 0 ≤ H / σ := div_nonneg hH.le hσ.le
  have hA : 0 ≤ X * Y / c := by positivity
  change (s.card : ℝ) ≤ 16 * (1 + H / σ + (X * Y) / c)
  linarith

/-- A unit vector in the original congruence lattice determines that entire
lattice modulo c. Both sides still consist of actual integer vectors. -/
theorem middleLattice_eq_of_unit_vector {c : ℕ} {t w : ℤ}
    (hw : IsUnit (w : ZMod c)) (U : Coordinate)
    (hu : IsUnit (U.1 : ZMod c)) (hU : U ∈ middleLattice c t w) :
    middleLattice c t w = middleLattice c U.2 U.1 := by
  ext z
  have hrel : (w : ZMod c) * (U.2 : ZMod c) =
      (t : ZMod c) * (U.1 : ZMod c) := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hU
    simpa only [Int.cast_sub, Int.cast_mul, sub_eq_zero] using h
  constructor
  · intro hz
    have hzero : ((w * z.2 - t * z.1 : ℤ) : ZMod c) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hz
    have heq : (w : ZMod c) *
        ((U.1 : ZMod c) * z.2 - (U.2 : ZMod c) * z.1) = w * 0 := by
      push_cast at hzero
      linear_combination (U.1 : ZMod c) * hzero - (z.1 : ZMod c) * hrel
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_sub, Int.cast_mul] using hw.mul_left_cancel heq
  · intro hz
    have hzero : ((U.1 * z.2 - U.2 * z.1 : ℤ) : ZMod c) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hz
    have heq : (U.1 : ZMod c) *
        ((w : ZMod c) * z.2 - (t : ZMod c) * z.1) = U.1 * 0 := by
      push_cast at hzero
      linear_combination (w : ZMod c) * hzero + (z.1 : ZMod c) * hrel
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_sub, Int.cast_mul] using hu.mul_left_cancel heq

/-- A fixed short unit vector counts original integer parameter pairs directly.
There is no additional choice of a slope lift and hence no extra factor p. -/
theorem original_short_vector_incidence_count {c : ℕ} [NeZero c] {X Y : ℝ}
    (hc : 0 < c) (hX : 0 < X) (hY : 0 < Y) (H : ℝ) (hH : 0 < H)
    (hHsq : H ^ 2 = X * Y) (U : Coordinate) (hU0 : U ≠ 0)
    (hu : IsUnit (U.1 : ZMod c)) (s : Finset Coordinate)
    (hbox : ∀ wt ∈ s, wt ∈ literalBox X Y)
    (hunit : ∀ wt ∈ s, IsUnit (wt.1 : ZMod c))
    (hmem : ∀ wt ∈ s, U ∈ middleLattice c wt.2 wt.1)
    (hmin : ∀ wt ∈ s, ∀ z ∈ middleLattice c wt.2 wt.1,
      z ≠ 0 → weightedSq X Y U ≤ weightedSq X Y z) :
    (s.card : ℝ) ≤ 16 * (1 + H / Real.sqrt (weightedSq X Y U) +
      (X * Y) / c) := by
  classical
  obtain ⟨B⟩ := exists_reduced_middle_basis c U.2 U.1 X Y hc hX hY hu
  have hUmem : U ∈ middleLattice c U.2 U.1 := by
    change (c : ℤ) ∣ U.1 * U.2 - U.2 * U.1
    simp [mul_comm]
  have hslope (wt : Coordinate) (hwt : wt ∈ s) :
      middleLattice c wt.2 wt.1 = middleLattice c U.2 U.1 :=
    middleLattice_eq_of_unit_vector (hunit wt hwt) U hu (hmem wt hwt)
  by_cases hs : s.Nonempty
  · obtain ⟨wt, hwt⟩ := hs
    have hσeq : weightedSq X Y B.R = weightedSq X Y U := by
      apply le_antisymm (B.shortest U hUmem hU0)
      apply hmin wt hwt B.R
      · rw [hslope wt hwt]
        exact B.memR
      · exact B.first_ne_zero hc
    have hcount := actual_middle_box_section_count B hc hX hY H hH hHsq s
      (by
        intro wt hwt
        change (c : ℤ) ∣ U.1 * wt.2 - U.2 * wt.1
        have hh := hmem wt hwt
        change (c : ℤ) ∣ wt.1 * U.2 - wt.2 * U.1 at hh
        convert dvd_neg.mpr hh using 1 <;> ring) hbox
    simpa only [hσeq] using hcount
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty, Nat.cast_zero]
    positivity

private theorem weightedSq_mul_area {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (U : Coordinate) :
    weightedSq X Y U * (X * Y) =
      Y ^ 2 * (U.1 : ℝ) ^ 2 + X ^ 2 * (U.2 : ℝ) ^ 2 := by
  unfold weightedSq
  field_simp

private theorem two_abs_product_le_weightedSq {X Y : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (U : Coordinate) :
    2 * |(U.1 : ℝ)| * |(U.2 : ℝ)| ≤ weightedSq X Y U := by
  have harea : 0 < X * Y := mul_pos hX hY
  have he := weightedSq_mul_area hX hY U
  have hsq := sq_nonneg (Y * |(U.1 : ℝ)| - X * |(U.2 : ℝ)|)
  have hineq : (2 * |(U.1 : ℝ)| * |(U.2 : ℝ)|) * (X * Y) ≤
      weightedSq X Y U * (X * Y) := by
    nlinarith [sq_abs (U.1 : ℝ), sq_abs (U.2 : ℝ)]
  exact (mul_le_mul_iff_left₀ harea).mp hineq

private theorem integer_unit_cancel_dvd {c : ℕ} {a b : ℤ}
    (ha : IsUnit (a : ZMod c)) (h : (c : ℤ) ∣ a * b) : (c : ℤ) ∣ b := by
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  have heq : (a : ZMod c) * (b : ZMod c) = a * 0 := by
    simpa only [Int.cast_mul, mul_zero] using hz
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (ha.mul_left_cancel heq)

private theorem primeSquare_int_unit {p : ℕ} (hp : p.Prime) {z : ℤ}
    (hz : ¬ (p : ℤ) ∣ z) : IsUnit (z : ZMod (p ^ 2)) := by
  have hn : ¬ p ∣ z.natAbs := by
    simpa only [← Int.natCast_dvd] using hz
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 2)).mpr hn
  rw [Nat.cast_natAbs] at hu
  by_cases hpos : 0 ≤ z
  · simpa only [abs_of_nonneg hpos] using hu
  · have hneg : IsUnit (-(z : ZMod (p ^ 2))) := by
      simpa only [abs_of_neg (lt_of_not_ge hpos), Int.cast_neg] using hu
    simpa only [neg_neg] using hneg.neg

/-- At the short-vector scales of the physical average, neither coordinate
can be zero or divisible by p. The explicit cutoff conditions are sufficient
conditions that the original range supplies once p is large enough. -/
theorem short_middle_vector_unit_coordinates {p : ℕ} (hp : p.Prime)
    {t w : ℤ} {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (hXY : X ≤ Y)
    (hYcut : Y < (p : ℝ) ^ 3) (hAcut : X * Y < 2 * (p : ℝ) ^ 4)
    (ht : IsUnit (t : ZMod (p ^ 2))) (hw : IsUnit (w : ZMod (p ^ 2)))
    (U : Coordinate) (hU : U ∈ middleLattice (p ^ 2) t w) (hU0 : U ≠ 0)
    (hshort : weightedSq X Y U ≤ (X * Y) / (p : ℝ) ^ 2) :
    U.1 ≠ 0 ∧ U.2 ≠ 0 ∧
      IsUnit (U.1 : ZMod (p ^ 2)) ∧ IsUnit (U.2 : ZMod (p ^ 2)) := by
  change ((p ^ 2 : ℕ) : ℤ) ∣ w * U.2 - t * U.1 at hU
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpp : 0 < (p : ℝ) ^ 2 := sq_pos_of_pos hpR
  have hbound : weightedSq X Y U * (p : ℝ) ^ 2 ≤ X * Y :=
    (le_div_iff₀ hpp).mp hshort
  have harea := mul_le_mul_of_nonneg_right hbound (mul_pos hX hY).le
  have hid := weightedSq_mul_area hX hY U
  have htotal : (Y^2 * (U.1 : ℝ)^2 + X^2 * (U.2 : ℝ)^2) * (p : ℝ) ^ 2 ≤
      X^2 * Y^2 := by nlinarith [harea, hid]
  have haxis (a b : ℤ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
      (hBcut : B < (p : ℝ) ^ 3) (hb0 : b ≠ 0)
      (hd : ((p ^ 2 : ℕ) : ℤ) ∣ b)
      (hineq : A^2 * (b : ℝ)^2 * (p : ℝ) ^ 2 ≤ A^2 * B^2) : False := by
    have hdiv := Int.le_abs_of_dvd hb0 hd
    have habs : (p : ℝ) ^ 2 ≤ |(b : ℝ)| := by exact_mod_cast hdiv
    have hsq : (p : ℝ) ^ 4 ≤ (b : ℝ)^2 := by
      have := (sq_le_sq₀ (by positivity) (abs_nonneg (b : ℝ))).mpr habs
      nlinarith [sq_abs (b : ℝ)]
    have hb : (b : ℝ)^2 * (p : ℝ) ^ 2 ≤ B^2 := by
      apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hA)).mp
      nlinarith [hineq]
    have hBsq : B^2 < (p : ℝ) ^ 6 := by
      have := (sq_lt_sq₀ hB.le (by positivity)).mpr hBcut
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hsq hpp.le
    nlinarith
  have hu0 : U.1 ≠ 0 := by
    intro hu
    have hv : U.2 ≠ 0 := by
      intro hv
      exact hU0 (Prod.ext hu hv)
    have hd : ((p ^ 2 : ℕ) : ℤ) ∣ w * U.2 := by
      simpa only [hu, mul_zero, sub_zero] using hU
    exact haxis U.1 U.2 X Y hX hY hYcut hv
      (integer_unit_cancel_dvd hw hd) (by simpa [hu] using htotal)
  have hv0 : U.2 ≠ 0 := by
    intro hv
    have hd : ((p ^ 2 : ℕ) : ℤ) ∣ t * U.1 := by
      have hh : ((p ^ 2 : ℕ) : ℤ) ∣ -(t * U.1) := by
        simpa only [hv, mul_zero, zero_sub] using hU
      exact dvd_neg.mp hh
    apply haxis U.2 U.1 Y X hY hX (hXY.trans_lt hYcut) hu0
      (integer_unit_cancel_dvd ht hd)
    simpa [hv, mul_comm] using htotal
  have hpdiv : (p : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast dvd_pow_self p (by decide : 2 ≠ 0)
  have hrel : (w : ZMod p) * (U.2 : ZMod p) =
      (t : ZMod p) * (U.1 : ZMod p) := by
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans hpdiv hU)
    simpa only [Int.cast_sub, Int.cast_mul, sub_eq_zero] using hh
  let reduction : ZMod (p ^ 2) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  have htp : IsUnit (t : ZMod p) := by simpa only [map_intCast] using ht.map reduction
  have hwp : IsUnit (w : ZMod p) := by simpa only [map_intCast] using hw.map reduction
  have hnotboth : ¬ ((p : ℤ) ∣ U.1 ∧ (p : ℤ) ∣ U.2) := by
    rintro ⟨hu, hv⟩
    have hau : (p : ℝ) ≤ |(U.1 : ℝ)| := by exact_mod_cast Int.le_abs_of_dvd hu0 hu
    have hav : (p : ℝ) ≤ |(U.2 : ℝ)| := by exact_mod_cast Int.le_abs_of_dvd hv0 hv
    have hab : (p : ℝ) ^ 2 ≤ |(U.1 : ℝ)| * |(U.2 : ℝ)| := by
      nlinarith [mul_le_mul hau hav hpR.le (abs_nonneg _)]
    have hnorm := two_abs_product_le_weightedSq hX hY U
    have hlow : 2 * (p : ℝ) ^ 2 ≤ weightedSq X Y U := by linarith
    have hh := mul_le_mul_of_nonneg_right hlow hpp.le
    nlinarith
  have hun : ¬ (p : ℤ) ∣ U.1 := by
    intro hu
    have hz : (U.1 : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hu
    have hv : (U.2 : ZMod p) = 0 := hwp.mul_left_cancel
      (by simpa only [hz, mul_zero] using hrel)
    exact hnotboth ⟨hu, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hv⟩
  have hvn : ¬ (p : ℤ) ∣ U.2 := by
    intro hv
    have hz : (U.2 : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hv
    have hu : (U.1 : ZMod p) = 0 := htp.mul_left_cancel
      (by simpa only [hz, mul_zero] using hrel.symm)
    exact hnotboth ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hu, hv⟩
  exact ⟨hu0, hv0, primeSquare_int_unit hp hun, primeSquare_int_unit hp hvn⟩

private theorem nonzero_integer_interval_card {T : ℝ} (hT : 0 ≤ T) :
    (((Finset.Icc (-⌊T⌋) ⌊T⌋).erase 0).card : ℝ) ≤ 2 * T := by
  have hN : 0 ≤ ⌊T⌋ := Int.floor_nonneg.mpr hT
  have hzero : (0 : ℤ) ∈ Finset.Icc (-⌊T⌋) ⌊T⌋ :=
    Finset.mem_Icc.mpr ⟨by omega, hN⟩
  have hcard := Int.card_Icc_of_le (a := -⌊T⌋) (b := ⌊T⌋) (by omega)
  have he : (((Finset.Icc (-⌊T⌋) ⌊T⌋).erase 0).card : ℝ) = 2 * (⌊T⌋ : ℝ) := by
    have hh : (((Finset.Icc (-⌊T⌋) ⌊T⌋).erase 0).card : ℤ) = 2 * ⌊T⌋ := by
      have hc := Finset.card_erase_add_one hzero
      omega
    exact_mod_cast hh
  rw [he]
  linarith [Int.floor_le T]

private theorem weighted_ball_box {X Y H R : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 < H) (hHsq : H ^ 2 = X * Y) (hR : 0 ≤ R)
    {U : Coordinate} (hQ : weightedSq X Y U ≤ R ^ 2) :
    |(U.1 : ℝ)| ≤ R * X / H ∧ |(U.2 : ℝ)| ≤ R * Y / H := by
  have hfirst : Y / X * (U.1 : ℝ)^2 ≤ R^2 := by
    have hterm : 0 ≤ X / Y * (U.2 : ℝ)^2 := by positivity
    dsimp [weightedSq] at hQ
    linarith
  have hsecond : X / Y * (U.2 : ℝ)^2 ≤ R^2 := by
    have hterm : 0 ≤ Y / X * (U.1 : ℝ)^2 := by positivity
    dsimp [weightedSq] at hQ
    linarith
  have hfirst' : Y * (U.1 : ℝ)^2 ≤ R^2 * X := by
    have h := mul_le_mul_of_nonneg_right hfirst hX.le
    have hc : Y / X * (U.1 : ℝ)^2 * X = Y * (U.1 : ℝ)^2 := by
      field_simp
    simpa only [hc] using h
  have hsecond' : X * (U.2 : ℝ)^2 ≤ R^2 * Y := by
    have h := mul_le_mul_of_nonneg_right hsecond hY.le
    have hc : X / Y * (U.2 : ℝ)^2 * Y = X * (U.2 : ℝ)^2 := by
      field_simp
    simpa only [hc] using h
  constructor
  · apply (le_div_iff₀ hH).mpr
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, sq_abs, hHsq, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hfirst' hX.le]
  · apply (le_div_iff₀ hH).mpr
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, sq_abs, hHsq, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hsecond' hY.le]

/-- An area-preserving ball contains at most 4R² integer vectors with both
coordinates nonzero. Removing the axes is essential for this uniform bound. -/
theorem nonaxis_short_vector_candidates_count {X Y H R : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hH : 0 < H) (hHsq : H ^ 2 = X * Y)
    (hR : 0 ≤ R) (s : Finset Coordinate)
    (hnonaxis : ∀ U ∈ s, U.1 ≠ 0 ∧ U.2 ≠ 0)
    (hshort : ∀ U ∈ s, weightedSq X Y U ≤ R ^ 2) :
    (s.card : ℝ) ≤ 4 * R^2 := by
  classical
  let W₁ := R * X / H
  let W₂ := R * Y / H
  let is₁ := (Finset.Icc (-⌊W₁⌋) ⌊W₁⌋).erase 0
  let is₂ := (Finset.Icc (-⌊W₂⌋) ⌊W₂⌋).erase 0
  have hsub : s ⊆ is₁ ×ˢ is₂ := by
    intro U hU
    have hb := weighted_ball_box hX hY hH hHsq hR (hshort U hU)
    have hi := Finset.mem_product.mp (mem_integerRectangle hb)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨(hnonaxis U hU).1, hi.1⟩,
        Finset.mem_erase.mpr ⟨(hnonaxis U hU).2, hi.2⟩⟩
  have hW₁ : 0 ≤ W₁ := by dsimp [W₁]; positivity
  have hW₂ : 0 ≤ W₂ := by dsimp [W₂]; positivity
  calc
    (s.card : ℝ) ≤ ((is₁ ×ˢ is₂).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = (is₁.card : ℝ) * (is₂.card : ℝ) := by rw [Finset.card_product, Nat.cast_mul]
    _ ≤ (2 * W₁) * (2 * W₂) :=
      mul_le_mul (nonzero_integer_interval_card hW₁) (nonzero_integer_interval_card hW₂)
        (Nat.cast_nonneg _) (by positivity)
    _ = 4 * R^2 := by
      dsimp [W₁, W₂]
      field_simp
      nlinarith [hHsq]

/-- One actual shortest-vector scale, counted in the original integer
parameter rectangle. The vectors come from actual reduced bases. -/
theorem actual_shortest_vector_scale_count {p : ℕ} (hp : p.Prime)
    {X Y H R : ℝ} (hX : 0 < X) (hY : 0 < Y) (hXY : X ≤ Y)
    (hYcut : Y < (p : ℝ) ^ 3) (hAcut : X * Y < 2 * (p : ℝ) ^ 4)
    (hH : 0 < H) (hHsq : H ^ 2 = X * Y) (hR : 0 < R)
    (s : Finset Coordinate) (hbox : ∀ wt ∈ s, wt ∈ literalBox X Y)
    (hunit : ∀ wt ∈ s, IsUnit (wt.2 : ZMod (p ^ 2)) ∧ IsUnit (wt.1 : ZMod (p ^ 2)))
    (U : Coordinate → Coordinate)
    (hbasis : ∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p ^ 2) wt.2 wt.1 X Y, U wt = B.R)
    (hlow : ∀ wt ∈ s, R ^ 2 ≤ weightedSq X Y (U wt))
    (hhigh : ∀ wt ∈ s, weightedSq X Y (U wt) ≤ 4 * R ^ 2)
    (hshort : ∀ wt ∈ s, weightedSq X Y (U wt) ≤ X * Y / (p : ℝ) ^ 2) :
    (s.card : ℝ) ≤ 256 * R ^ 2 * (1 + H / R + X * Y / (p : ℝ) ^ 2) := by
  classical
  have hp2 : 0 < p ^ 2 := pow_pos hp.pos _
  let : NeZero (p ^ 2) := ⟨ne_of_gt hp2⟩
  have hvector (wt : Coordinate) (hwt : wt ∈ s) :
      U wt ≠ 0 ∧ U wt ∈ middleLattice (p ^ 2) wt.2 wt.1 ∧
      (∀ z ∈ middleLattice (p ^ 2) wt.2 wt.1, z ≠ 0 →
        weightedSq X Y (U wt) ≤ weightedSq X Y z) := by
    obtain ⟨B, hB⟩ := hbasis wt hwt
    rw [hB]
    exact ⟨B.first_ne_zero hp2, B.memR, B.shortest⟩
  have hunits (wt : Coordinate) (hwt : wt ∈ s) :=
    short_middle_vector_unit_coordinates hp hX hY hXY hYcut hAcut
      (hunit wt hwt).1 (hunit wt hwt).2 (U wt)
      (hvector wt hwt).2.1 (hvector wt hwt).1 (hshort wt hwt)
  have hvec : ((s.image U).card : ℝ) ≤ 16 * R ^ 2 := by
    have hh := nonaxis_short_vector_candidates_count hX hY hH hHsq
      (show 0 ≤ 2 * R by positivity) (s.image U)
      (by
        intro v hv
        obtain ⟨wt, hwt, rfl⟩ := Finset.mem_image.mp hv
        exact ⟨(hunits wt hwt).1, (hunits wt hwt).2.1⟩)
      (by
        intro v hv
        obtain ⟨wt, hwt, rfl⟩ := Finset.mem_image.mp hv
        nlinarith [hhigh wt hwt])
    nlinarith
  let C := 16 * (1 + H / R + X * Y / (p : ℝ) ^ 2)
  have hfiber (v : Coordinate) (hv : v ∈ s.image U) :
      ((s.filter (fun wt => U wt = v)).card : ℝ) ≤ C := by
    obtain ⟨wt₀, hwt₀, heq⟩ := Finset.mem_image.mp hv
    have hv0 : v ≠ 0 := heq ▸ (hvector wt₀ hwt₀).1
    have hvunit : IsUnit (v.1 : ZMod (p ^ 2)) := heq ▸ (hunits wt₀ hwt₀).2.2.1
    have hc := original_short_vector_incidence_count hp2 hX hY H hH hHsq
      v hv0 hvunit (s.filter (fun wt => U wt = v))
      (by intro wt hwt; exact hbox wt (Finset.mem_filter.mp hwt).1)
      (by intro wt hwt; exact (hunit wt (Finset.mem_filter.mp hwt).1).2)
      (by
        intro wt hwt
        obtain ⟨hs, he⟩ := Finset.mem_filter.mp hwt
        rw [← he]
        exact (hvector wt hs).2.1)
      (by
        intro wt hwt z hz hz0
        obtain ⟨hs, he⟩ := Finset.mem_filter.mp hwt
        rw [← he]
        exact (hvector wt hs).2.2 z hz hz0)
    have hlen : R ≤ Real.sqrt (weightedSq X Y v) := by
      apply Real.le_sqrt_of_sq_le
      simpa only [heq] using hlow wt₀ hwt₀
    have hd : H / Real.sqrt (weightedSq X Y v) ≤ H / R :=
      div_le_div_of_nonneg_left hH.le hR hlen
    dsimp [C]
    push_cast at hc
    linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    (s.card : ℝ) = ∑ v ∈ s.image U, ((s.filter (fun wt => U wt = v)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image U s
    _ ≤ ∑ _v ∈ s.image U, C := Finset.sum_le_sum hfiber
    _ = ((s.image U).card : ℝ) * C := by simp
    _ ≤ (16 * R ^ 2) * C := mul_le_mul_of_nonneg_right hvec hC
    _ = _ := by dsimp [C]; ring

/-- The physical multiplicity at one actual short-vector scale. Its cost is
linear in the shortest-length scale plus one scale-independent area term. -/
theorem actual_shortest_vector_scale_weight {p : ℕ} (hp : p.Prime)
    {X Y H R : ℝ} (hX : 0 < X) (hY : 0 < Y) (hXY : X ≤ Y)
    (hYcut : Y < (p : ℝ) ^ 3) (hAcut : X * Y < 2 * (p : ℝ) ^ 4)
    (hH : 0 < H) (hHsq : H ^ 2 = X * Y) (hR : 0 < R) (hscale : R ≤ H / p)
    (s : Finset Coordinate) (hbox : ∀ wt ∈ s, wt ∈ literalBox X Y)
    (hunit : ∀ wt ∈ s, IsUnit (wt.2 : ZMod (p ^ 2)) ∧ IsUnit (wt.1 : ZMod (p ^ 2)))
    (U : Coordinate → Coordinate)
    (hbasis : ∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p ^ 2) wt.2 wt.1 X Y, U wt = B.R)
    (hlow : ∀ wt ∈ s, R ^ 2 ≤ weightedSq X Y (U wt))
    (hhigh : ∀ wt ∈ s, weightedSq X Y (U wt) ≤ 4 * R ^ 2)
    (hshort : ∀ wt ∈ s, weightedSq X Y (U wt) ≤ X * Y / (p : ℝ) ^ 2) :
    (∑ wt ∈ s, (1 + H / ((p : ℝ) * Real.sqrt (weightedSq X Y (U wt))))) ≤
      512 * (H / p) * (R + H + (X * Y / (p : ℝ) ^ 2) * R) := by
  classical
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hden : 0 < (p : ℝ) * R := mul_pos hpR hR
  have hone : 1 ≤ H / ((p : ℝ) * R) := by
    apply (le_div_iff₀ hden).mpr
    have hh := (le_div_iff₀ hpR).mp hscale
    nlinarith
  have hw (wt : Coordinate) (hwt : wt ∈ s) :
      1 + H / ((p : ℝ) * Real.sqrt (weightedSq X Y (U wt))) ≤
        2 * H / ((p : ℝ) * R) := by
    have hlen : R ≤ Real.sqrt (weightedSq X Y (U wt)) :=
      Real.le_sqrt_of_sq_le (hlow wt hwt)
    have hd := div_le_div_of_nonneg_left hH.le hden
      (mul_le_mul_of_nonneg_left hlen hpR.le)
    calc
      _ ≤ H / ((p : ℝ) * R) + H / ((p : ℝ) * R) := add_le_add hone hd
      _ = _ := by ring
  have hc := actual_shortest_vector_scale_count hp hX hY hXY hYcut hAcut hH hHsq
    hR s hbox hunit U hbasis hlow hhigh hshort
  calc
    _ ≤ ∑ _wt ∈ s, 2 * H / ((p : ℝ) * R) := Finset.sum_le_sum hw
    _ = (s.card : ℝ) * (2 * H / ((p : ℝ) * R)) := by simp
    _ ≤ (256 * R ^ 2 * (1 + H / R + X * Y / (p : ℝ) ^ 2)) *
        (2 * H / ((p : ℝ) * R)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by field_simp; ring

private theorem dyadic_sum_le {T : ℝ} {N : ℕ} (hN : (2 : ℝ) ^ N ≤ T) :
    (∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ k) ≤ 2 * T := by
  have hid (n : ℕ) : (∑ k ∈ Finset.range (n + 1), (2 : ℝ) ^ k) =
      2 ^ (n + 1) - 1 := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [hid, pow_succ]
  linarith

/-- Average physical rational multiplicity over actual original integer
parameters. The logarithmic number of scales and all their incidence counts
are proved, using actual reduced bases rather than freely lifted slopes. -/
theorem actual_physical_weight_average {p : ℕ} (hp : p.Prime)
    {X Y H : ℝ} (hX1 : 1 ≤ X) (hXY : X ≤ Y)
    (hYcut : Y < (p : ℝ) ^ 3) (hAcut : X * Y < 2 * (p : ℝ) ^ 4)
    (hH : 0 < H) (hHsq : H ^ 2 = X * Y) (hHp : (p : ℝ) ≤ H)
    (s : Finset Coordinate) (hbox : ∀ wt ∈ s, wt ∈ literalBox X Y)
    (hunit : ∀ wt ∈ s, IsUnit (wt.2 : ZMod (p ^ 2)) ∧ IsUnit (wt.1 : ZMod (p ^ 2)))
    (U : Coordinate → Coordinate)
    (hbasis : ∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p ^ 2) wt.2 wt.1 X Y, U wt = B.R) :
    (∑ wt ∈ s, (1 + H / ((p : ℝ) * Real.sqrt (weightedSq X Y (U wt))))) ≤
      2048 * (X * Y + (X * Y / p) * (1 + Real.log (2 * p) / Real.log 2) +
        (X * Y) ^ 2 / (p : ℝ) ^ 4) := by
  classical
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hY1 : 1 ≤ Y := hX1.trans hXY
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hp2 : 0 < p ^ 2 := pow_pos hp.pos _
  let T := H / (p : ℝ)
  let Q := fun wt => weightedSq X Y (U wt)
  let W := fun wt => 1 + H / ((p : ℝ) * Real.sqrt (Q wt))
  have hT : 0 < T := div_pos hH hpR
  have hT1 : 1 ≤ T := (le_div_iff₀ hpR).mpr (by simpa using hHp)
  have hTsq : T ^ 2 = X * Y / (p : ℝ) ^ 2 := by
    dsimp [T]
    rw [div_pow, hHsq]
  have hTcut : T < 2 * p := by
    have hsq : T ^ 2 < 2 * (p : ℝ) ^ 2 := by
      rw [hTsq]
      apply (div_lt_iff₀ (sq_pos_of_pos hpR)).mpr
      nlinarith [hAcut]
    nlinarith [sq_nonneg (T - 2 * p)]
  obtain ⟨N, hNlow, hNhigh⟩ := exists_nat_pow_near hT1 (by norm_num : (1 : ℝ) < 2)
  let P := fun k wt => ((2 : ℝ) ^ k) ^ 2 ≤ Q wt ∧
    Q wt < 4 * ((2 : ℝ) ^ k) ^ 2 ∧ Q wt ≤ X * Y / (p : ℝ) ^ 2
  let G := s.filter (fun wt => X * Y / (p : ℝ) ^ 2 < Q wt)
  have hW (wt : Coordinate) : 0 ≤ W wt := by dsimp [W]; positivity
  have hshort_lower (wt : Coordinate) (hwt : wt ∈ s)
      (hs : Q wt ≤ X * Y / (p : ℝ) ^ 2) : 1 ≤ Real.sqrt (Q wt) := by
    obtain ⟨B, hB⟩ := hbasis wt hwt
    have hb := short_middle_vector_unit_coordinates hp hX hY hXY hYcut hAcut
      (hunit wt hwt).1 (hunit wt hwt).2 (U wt)
      (by rw [hB]; exact B.memR) (by rw [hB]; exact B.first_ne_zero hp2) hs
    have habs (z : ℤ) (hz : z ≠ 0) : 1 ≤ |(z : ℝ)| := by
      have hpos : 0 < |z| := abs_pos.mpr hz
      have hh : (1 : ℤ) ≤ |z| := by omega
      exact_mod_cast hh
    have hprod : 1 ≤ |((U wt).1 : ℝ)| * |((U wt).2 : ℝ)| := by
      nlinarith [mul_le_mul (habs _ hb.1) (habs _ hb.2.1)
        (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg ((U wt).1 : ℝ))]
    apply Real.le_sqrt_of_sq_le
    have hh := two_abs_product_le_weightedSq hX hY (U wt)
    dsimp [Q]
    nlinarith
  have hcover (wt : Coordinate) (hwt : wt ∈ s) :
      W wt ≤ (if X * Y / (p : ℝ) ^ 2 < Q wt then W wt else 0) +
        ∑ k ∈ Finset.range (N + 1), if P k wt then W wt else 0 := by
    have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), if P k wt then W wt else 0 :=
      Finset.sum_nonneg (fun _ _ => by split <;> positivity)
    by_cases hs : X * Y / (p : ℝ) ^ 2 < Q wt
    · simp only [if_pos hs]
      linarith
    · have hsQ : Q wt ≤ X * Y / (p : ℝ) ^ 2 := le_of_not_gt hs
      obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near (hshort_lower wt hwt hsQ)
        (by norm_num : (1 : ℝ) < 2)
      have hlen : Real.sqrt (Q wt) ≤ T := by
        apply (Real.sqrt_le_iff).mpr
        exact ⟨hT.le, by rw [hTsq]; exact hsQ⟩
      have hk : k < N + 1 := by
        have hh : (2 : ℝ) ^ k < 2 ^ (N + 1) := hklo.trans_lt (hlen.trans_lt hNhigh)
        exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hh
      have hQ0 : 0 ≤ Q wt := weightedSq_nonneg hX hY _
      have hPk : P k wt := by
        dsimp [P]
        have hsq := Real.sq_sqrt hQ0
        have hpow : 0 < (2 : ℝ) ^ k := by positivity
        have hlo := (sq_le_sq₀ hpow.le (Real.sqrt_nonneg _)).mpr hklo
        have hhi := (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hkhi
        have hpow_succ : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ _ _
        rw [hpow_succ] at hhi
        exact ⟨by nlinarith, by nlinarith, hsQ⟩
      have hh := Finset.single_le_sum (f := fun j => if P j wt then W wt else 0)
        (fun _ _ => by split <;> positivity) (Finset.mem_range.mpr hk)
      simpa only [if_pos hPk, if_neg hs, zero_add] using hh
  have hsplit : (∑ wt ∈ s, W wt) ≤ (∑ wt ∈ G, W wt) +
      ∑ k ∈ Finset.range (N + 1), ∑ wt ∈ s.filter (P k), W wt := by
    calc
      _ ≤ ∑ wt ∈ s, ((if X * Y / (p : ℝ) ^ 2 < Q wt then W wt else 0) +
          ∑ k ∈ Finset.range (N + 1), if P k wt then W wt else 0) :=
        Finset.sum_le_sum hcover
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp only [G, Finset.sum_filter]
  have hGcard : (G.card : ℝ) ≤ 9 * (X * Y) := by
    have hsub : G ⊆ integerRectangle X Y := by
      intro wt hwt
      exact mem_integerRectangle (hbox wt (Finset.mem_filter.mp hwt).1)
    have hh : (G.card : ℝ) ≤ (2 * X + 1) * (2 * Y + 1) :=
      (show (G.card : ℝ) ≤ ((integerRectangle X Y).card : ℝ) by
        exact_mod_cast Finset.card_le_card hsub).trans (integerRectangle_card hX.le hY.le)
    have hx : 2 * X + 1 ≤ 3 * X := by linarith
    have hy : 2 * Y + 1 ≤ 3 * Y := by linarith
    nlinarith [mul_le_mul hx hy (by positivity : 0 ≤ 2 * Y + 1) (by positivity : 0 ≤ 3 * X)]
  have hGweight : (∑ wt ∈ G, W wt) ≤ 18 * (X * Y) := by
    have hh (wt : Coordinate) (hwt : wt ∈ G) : W wt ≤ 2 := by
      have hsQ := (Finset.mem_filter.mp hwt).2
      have hlen : T ≤ Real.sqrt (Q wt) :=
        Real.le_sqrt_of_sq_le (by rw [hTsq]; exact hsQ.le)
      have hd : 0 < (p : ℝ) * Real.sqrt (Q wt) :=
        mul_pos hpR (hT.trans_le hlen)
      have he : H ≤ (p : ℝ) * Real.sqrt (Q wt) := by
        have hh := (div_le_iff₀ hpR).mp hlen
        simpa only [mul_comm] using hh
      have hr : H / ((p : ℝ) * Real.sqrt (Q wt)) ≤ 1 := (div_le_one₀ hd).mpr he
      dsimp [W]
      linarith
    calc
      _ ≤ ∑ _wt ∈ G, (2 : ℝ) := Finset.sum_le_sum hh
      _ = (G.card : ℝ) * 2 := by simp
      _ ≤ _ := by linarith
  have hscales : (∑ k ∈ Finset.range (N + 1), ∑ wt ∈ s.filter (P k), W wt) ≤
      512 * T * (2 * T + ((N + 1 : ℕ) : ℝ) * H +
        (X * Y / (p : ℝ) ^ 2) * (2 * T)) := by
    have hs (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
        (∑ wt ∈ s.filter (P k), W wt) ≤
          512 * T * ((2 : ℝ) ^ k + H + (X * Y / (p : ℝ) ^ 2) * (2 : ℝ) ^ k) := by
      apply actual_shortest_vector_scale_weight hp hX hY hXY hYcut hAcut hH hHsq
        (by positivity : 0 < (2 : ℝ) ^ k)
        ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans hNlow)
        (s.filter (P k))
        (by intro wt hwt; exact hbox wt (Finset.mem_filter.mp hwt).1)
        (by intro wt hwt; exact hunit wt (Finset.mem_filter.mp hwt).1) U
        (by intro wt hwt; exact hbasis wt (Finset.mem_filter.mp hwt).1)
        (by intro wt hwt; exact (Finset.mem_filter.mp hwt).2.1)
        (by intro wt hwt; exact (Finset.mem_filter.mp hwt).2.2.1.le)
        (by intro wt hwt; exact (Finset.mem_filter.mp hwt).2.2.2)
    calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), 512 * T *
          ((2 : ℝ) ^ k + H + (X * Y / (p : ℝ) ^ 2) * (2 : ℝ) ^ k) := Finset.sum_le_sum hs
      _ = 512 * T * ((∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ k) +
          ((N + 1 : ℕ) : ℝ) * H + (X * Y / (p : ℝ) ^ 2) *
          (∑ k ∈ Finset.range (N + 1), (2 : ℝ) ^ k)) := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by
        have hgeom := dyadic_sum_le hNlow
        gcongr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (2 * (p : ℝ)) := Real.log_nonneg (by nlinarith)
  have hNlog : ((N + 1 : ℕ) : ℝ) ≤ 1 + Real.log (2 * p) / Real.log 2 := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ N) (hNlow.trans hTcut.le)
    rw [Real.log_pow] at hh
    have hd := (le_div_iff₀ hlog2).mpr hh
    push_cast
    linarith
  have halg : 512 * T * (2 * T + ((N + 1 : ℕ) : ℝ) * H +
      (X * Y / (p : ℝ) ^ 2) * (2 * T)) =
      1024 * (X * Y) / (p : ℝ) ^ 2 +
        512 * (X * Y / p) * ((N + 1 : ℕ) : ℝ) +
        1024 * (X * Y) ^ 2 / (p : ℝ) ^ 4 := by
    dsimp [T]
    calc
      _ = 1024 * H ^ 2 / (p : ℝ) ^ 2 +
          512 * (H ^ 2 / p) * ((N + 1 : ℕ) : ℝ) +
          1024 * (H ^ 2 * (X * Y)) / (p : ℝ) ^ 4 := by field_simp; ring
      _ = _ := by rw [hHsq]; ring
  rw [halg] at hscales
  have hsmall : X * Y / (p : ℝ) ^ 2 ≤ X * Y :=
    div_le_self (by positivity) (one_le_pow₀ hp1)
  have hlogcost := mul_le_mul_of_nonneg_left hNlog
    (show 0 ≤ 512 * (X * Y / (p : ℝ)) by positivity)
  change (∑ wt ∈ s, W wt) ≤ _
  have hA : 0 ≤ X * Y := by positivity
  have hB : 0 ≤ (X * Y) ^ 2 / (p : ℝ) ^ 4 := by positivity
  have hL : 0 ≤ (X * Y / (p : ℝ)) * (1 + Real.log (2 * p) / Real.log 2) := by positivity
  simp only [mul_div_assoc] at hscales hsmall hlogcost hL hB ⊢
  nlinarith [hsplit, hGweight, hscales]

end

end D5.S3.Arith.CharacterSums.Original
