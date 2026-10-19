/- GID: D5/S3/Geometry/Hyperideal/PositiveFlatClassification
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/PositiveFlatClassification
   mirror-E: none(waiver:universal-positive-length-classification)
   anchors: []
   utility: none
   digest: Exhaustive native six-coordinate genuine and closed flat-sector classification. -/

import D5.S3.Geometry.Hyperideal.TwoLengthAngleSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.PositiveFlatClassification

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum

/-- Original opposite pairs, in the order (12,13,14,34,24,23). -/
def opposite (q : Fin 6) : Fin 6 := ![3,4,5,0,1,2] q

def Genuine (x : Fin 6 → ℝ) : Prop := ∀ q, -1 < rawCos x q ∧ rawCos x q < 1

def Sector (x : Fin 6 → ℝ) (k : Fin 3) : Prop := rawCos x (k.castAdd 3) ≤ -1

private def delta (x : Fin 6 → ℝ) : ℝ :=
  x 1 ^ 2 * x 4 ^ 2 - x 1 ^ 2 - 2*x 1*x 2*x 4*x 5 - 2*x 1*x 2*x 3
    - 2*x 1*x 4*x 3*x 0 - 2*x 1*x 5*x 0 + x 2 ^ 2 * x 5 ^ 2 - x 2 ^ 2
    - 2*x 2*x 4*x 0 - 2*x 2*x 5*x 3*x 0 - x 4 ^ 2
    - 2*x 4*x 5*x 3 - x 5 ^ 2 + x 3 ^ 2 * x 0 ^ 2 - x 3 ^ 2 - x 0 ^ 2 + 1

private theorem square_gap (x : Fin 6 → ℝ) (q : Fin 6) :
    (rawNum x q)^2 - leftRad x q * rightRad x q = (x q ^ 2 - 1) * delta x := by
  fin_cases q <;>
    simp only [rawNum, leftRad, rightRad, frame, numerator, rad, delta, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue] <;> norm_num <;> ring

private theorem num_frame (x : Fin 6 → ℝ) (q j : Fin 6) :
    rawNum (x ∘ frame q) j = rawNum x (frame q j) := by
  fin_cases q <;> fin_cases j <;>
    simp only [rawNum, frame, numerator, Function.comp_def, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue] <;> norm_num <;> ring

private theorem delta_frame (x : Fin 6 → ℝ) (q : Fin 6) :
    delta (x ∘ frame q) = delta x := by
  fin_cases q <;> simp only [delta, frame, Function.comp_def, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue] <;> norm_num <;> ring

private theorem denominator_pos (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q) (q : Fin 6) :
    0 < Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q) := by
  exact mul_pos
    (Real.sqrt_pos.mpr (rad_positive _ _ _ (hx _) (hx _) (hx _)))
    (Real.sqrt_pos.mpr (rad_positive _ _ _ (hx _) (hx _) (hx _)))

private theorem denominator_sq (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q) (q : Fin 6) :
    (Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q)) ^ 2 =
      leftRad x q * rightRad x q := by
  have hl : 0 < leftRad x q := rad_positive _ _ _ (hx _) (hx _) (hx _)
  have hr : 0 < rightRad x q := rad_positive _ _ _ (hx _) (hx _) (hx _)
  rw [mul_pow, Real.sq_sqrt hl.le, Real.sq_sqrt hr.le]

private theorem raw_quotient (x : Fin 6 → ℝ) (q : Fin 6) :
    rawCos x q = rawNum x q /
      (Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q)) := by
  change rawNum x q / Real.sqrt (leftRad x q) / Real.sqrt (rightRad x q) = _
  rw [div_div]

private theorem interior_of_negative (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hd : delta x < 0) : Genuine x := by
  intro q
  have hp : 0 < x q ^ 2 - 1 := by nlinarith [hx q]
  have hg := square_gap x q
  have hm := mul_neg_of_pos_of_neg hp hd
  have hs := denominator_sq x hx q
  have hpos := denominator_pos x hx q
  rw [raw_quotient]
  constructor
  · apply (lt_div_iff₀ hpos).mpr
    nlinarith [sq_nonneg (rawNum x q + Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q))]
  · apply (div_lt_iff₀ hpos).mpr
    nlinarith [sq_nonneg (rawNum x q - Real.sqrt (leftRad x q) * Real.sqrt (rightRad x q))]

private theorem outside_bounds (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hd : 0 ≤ delta x) (q : Fin 6) :
    (rawNum x q < 0 → rawCos x q ≤ -1) ∧
      (0 < rawNum x q → 1 ≤ rawCos x q) := by
  have hp : 0 < x q ^ 2 - 1 := by nlinarith [hx q]
  have hg := square_gap x q
  have hm := mul_nonneg hp.le hd
  have hs := denominator_sq x hx q
  have hpos := denominator_pos x hx q
  rw [raw_quotient]
  constructor
  · intro hn
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  · intro hn
    apply (le_div_iff₀ hpos).mpr
    nlinarith

private theorem cofactor_triangle (x : Fin 6 → ℝ) :
    rawNum x 0 * rawNum x 1 + leftRad x 0 * rawNum x 2 =
      -(x 1*x 0+x 5) * delta x := by
  simp only [rawNum, leftRad, frame, numerator, rad, delta, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue]
  ring

private theorem negative_exists (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hd : 0 ≤ delta x) : ∃ q, rawNum x q < 0 := by
  by_contra h
  push_neg at h
  have h2 : 0 < rawNum x 2 := by
    have hg := square_gap x 2
    have hrad : 0 < leftRad x 2 * rightRad x 2 := mul_pos
      (rad_positive _ _ _ (hx _) (hx _) (hx _))
      (rad_positive _ _ _ (hx _) (hx _) (hx _))
    have hm := mul_nonneg (show 0 ≤ x 2 ^ 2 - 1 by nlinarith [hx 2]) hd
    nlinarith [h 2]
  have hprod := mul_nonneg (h 0) (h 1)
  have hrad : 0 < leftRad x 0 := rad_positive _ _ _ (hx _) (hx _) (hx _)
  have hterm := mul_pos hrad h2
  have hcoeff : 0 < x 1*x 0+x 5 := by
    have h0 := hx 0; have h1 := hx 1; have h5 := hx 5
    positivity
  have hm := mul_nonneg hcoeff.le hd
  have hi := cofactor_triangle x
  nlinarith

private theorem base_signs (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hd : 0 ≤ delta x) (hn : rawNum x 0 < 0) :
    rawNum x 3 < 0 ∧ ∀ q, q ≠ 0 → q ≠ 3 → 0 < rawNum x q := by
  have hr : 0 < x 0 := lt_trans (by norm_num) (hx 0)
  have ho : 0 < x 3 := lt_trans (by norm_num) (hx 3)
  have ha : 0 < x 1 := lt_trans (by norm_num) (hx 1)
  have hb : 0 < x 2 := lt_trans (by norm_num) (hx 2)
  have hc : 0 < x 4 := lt_trans (by norm_num) (hx 4)
  have he : 0 < x 5 := lt_trans (by norm_num) (hx 5)
  have hdom : x 1*x 4+x 2*x 5 < x 0*x 3 := by
    have hn' : x 1*x 2+x 4*x 5+x 0*(x 1*x 4+x 2*x 5-x 0*x 3)+x 3 < 0 := by
      convert hn using 1 <;> simp only [rawNum, frame, numerator, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue] <;> norm_num <;> ring
    have haux : x 0*(x 1*x 4+x 2*x 5-x 0*x 3) < 0 := by
      nlinarith only [hn', mul_pos ha hb, mul_pos hc he, ho]
    apply sub_neg.mp
    by_contra h
    have hh := mul_nonneg hr.le (le_of_not_gt h)
    linarith
  have h1 : 0 < rawNum x 1 := by
    have hm := mul_pos ha (sub_pos.mpr hdom)
    have hm' : 0 < x 1*(x 0*x 3-x 1*x 4)+x 2*x 0+x 5*x 3+x 4+x 1*x 2*x 5 := by
      have hh : 0 < x 0*x 3-x 1*x 4 := by nlinarith [mul_pos hb he]
      positivity
    convert hm' using 1 <;> simp only [rawNum, frame, numerator, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue] <;> norm_num <;> ring
  have h2 : 0 < rawNum x 2 := by
    have hh : 0 < x 0*x 3-x 2*x 5 := by nlinarith [mul_pos ha hc]
    have hm : 0 < x 2*(x 0*x 3-x 2*x 5)+x 1*x 0+x 4*x 3+x 5+x 1*x 2*x 4 := by positivity
    convert hm using 1 <;> simp only [rawNum, frame, numerator, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue] <;> norm_num <;> ring
  have h4 : 0 < rawNum x 4 := by
    have hh : 0 < x 0*x 3-x 1*x 4 := by nlinarith [mul_pos hb he]
    have hm : 0 < x 4*(x 0*x 3-x 1*x 4)+x 2*x 3+x 5*x 0+x 1+x 2*x 4*x 5 := by positivity
    convert hm using 1 <;> simp only [rawNum, frame, numerator, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue] <;> norm_num <;> ring
  have h5 : 0 < rawNum x 5 := by
    have hh : 0 < x 0*x 3-x 2*x 5 := by nlinarith [mul_pos ha hc]
    have hm : 0 < x 5*(x 0*x 3-x 2*x 5)+x 1*x 3+x 4*x 0+x 2+x 1*x 4*x 5 := by positivity
    convert hm using 1 <;> simp only [rawNum, frame, numerator, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue] <;> norm_num <;> ring
  have hi : rawNum x 3 * rawNum x 1 + leftRad x 1 * rawNum x 5 =
      -(x 1*x 3+x 2) * delta x := by
    simp only [rawNum, leftRad, frame, numerator, rad, delta, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue]
    ring
  have hrad : 0 < leftRad x 1 := rad_positive _ _ _ (hx _) (hx _) (hx _)
  have hterm := mul_pos hrad h5
  have hm := mul_nonneg (show 0 ≤ x 1*x 3+x 2 by positivity) hd
  have h3 : rawNum x 3 < 0 := by nlinarith
  refine ⟨h3, ?_⟩
  intro q hq0 hq3
  fin_cases q <;> first | contradiction | assumption

private theorem frame_properties (q : Fin 6) :
    frame q 0 = q ∧ frame q 3 = opposite q ∧ Function.Bijective (frame q) := by
  fin_cases q <;> decide

private theorem num_pattern (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hd : 0 ≤ delta x) (q : Fin 6) (hn : rawNum x q < 0) :
    ∀ j, (j = q ∨ j = opposite q → rawNum x j < 0) ∧
      (j ≠ q → j ≠ opposite q → 0 < rawNum x j) := by
  obtain ⟨h0, h3, hbij⟩ := frame_properties q
  have hy : ∀ i, 1 < (x ∘ frame q) i := fun i => hx _
  have hd' : 0 ≤ delta (x ∘ frame q) := by rw [delta_frame]; exact hd
  have hn' : rawNum (x ∘ frame q) 0 < 0 := by rw [num_frame, h0]; exact hn
  obtain ⟨hb3, hrest⟩ := base_signs (x ∘ frame q) hy hd' hn'
  rw [num_frame, h3] at hb3
  intro j
  constructor
  · rintro (rfl | rfl)
    · exact hn
    · exact hb3
  · intro hj0 hj3
    obtain ⟨i, rfl⟩ := hbij.surjective j
    rw [← num_frame]
    apply hrest
    · intro hi; subst i; exact hj0 h0
    · intro hi; subst i; exact hj3 h3

private theorem sector_data (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (q : Fin 6) (hc : rawCos x q ≤ -1) : 0 ≤ delta x ∧ rawNum x q < 0 := by
  have hd := denominator_pos x hx q
  have hs := denominator_sq x hx q
  have hg := square_gap x q
  have hp : 0 < x q ^ 2 - 1 := by nlinarith [hx q]
  rw [raw_quotient, div_le_iff₀ hd] at hc
  constructor
  · by_contra h
    have hm := mul_neg_of_pos_of_neg hp (lt_of_not_ge h)
    nlinarith
  · nlinarith

private theorem opposite_first (k : Fin 3) : opposite (k.castAdd 3) = k.natAdd 3 := by
  fin_cases k <;> rfl

private theorem raw_pattern (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (k : Fin 3) (hk : Sector x k) :
    ∀ q, (q = k.castAdd 3 ∨ q = k.natAdd 3 → rawCos x q ≤ -1) ∧
      (q ≠ k.castAdd 3 → q ≠ k.natAdd 3 → 1 ≤ rawCos x q) := by
  obtain ⟨hd, hn⟩ := sector_data x hx (k.castAdd 3) hk
  have hsign := num_pattern x hx hd (k.castAdd 3) hn
  rw [opposite_first] at hsign
  intro q
  exact ⟨fun h => (outside_bounds x hx hd q).1 ((hsign q).1 h),
    fun h0 h3 => (outside_bounds x hx hd q).2 ((hsign q).2 h0 h3)⟩

private def pairIndex (q : Fin 6) : Fin 3 := ![0,1,2,0,1,2] q

private theorem pairIndex_first (q : Fin 6) :
    (pairIndex q).castAdd 3 = q ∨ (pairIndex q).castAdd 3 = opposite q := by
  fin_cases q <;> decide

private theorem first_pair_eq (j k : Fin 3) :
    (j.castAdd 3 = k.castAdd 3 ∨ j.castAdd 3 = k.natAdd 3) ↔ j = k := by
  fin_cases j <;> fin_cases k <;> decide

private theorem sector_exists (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hd : 0 ≤ delta x) : ∃ k, Sector x k := by
  obtain ⟨q, hn⟩ := negative_exists x hx hd
  refine ⟨pairIndex q, (outside_bounds x hx hd _).1 ?_⟩
  exact (num_pattern x hx hd q hn _).1 (pairIndex_first q)

private theorem sector_unique (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (k j : Fin 3) (hk : Sector x k) (hj : Sector x j) : j = k := by
  by_contra h
  have hn := not_or.mp (mt (first_pair_eq j k).mp h)
  have hh := (raw_pattern x hx k hk (j.castAdd 3)).2 hn.1 hn.2
  change rawCos x (j.castAdd 3) ≤ -1 at hj
  linarith

private theorem angle_pi (x : Fin 6 → ℝ) (q : Fin 6) :
    extendedAngle x q = Real.pi ↔ rawCos x q ≤ -1 := by
  simp [extendedAngle, Real.arccos_eq_pi, max_le_iff, min_le_iff]

private theorem angle_zero (x : Fin 6 → ℝ) (q : Fin 6) :
    extendedAngle x q = 0 ↔ 1 ≤ rawCos x q := by
  simp [extendedAngle, Real.arccos_eq_zero, le_max_iff, le_min_iff]

private theorem angle_interior (x : Fin 6 → ℝ) (q : Fin 6) :
    (0 < extendedAngle x q ∧ extendedAngle x q < Real.pi) ↔
      (-1 < rawCos x q ∧ rawCos x q < 1) := by
  simp only [extendedAngle, Real.arccos_pos, Real.arccos_lt_pi]
  simp [max_lt_iff, lt_min_iff, lt_max_iff, min_lt_iff, and_comm]

/-- Every positive six-coordinate input is genuine or has one unique closed
flat sector. The raw inequalities and clipped-angle pattern use the original
six-slot formula, including every sector boundary. -/
theorem positive_classification (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q) :
    (Genuine x ↔ ∀ q, 0 < extendedAngle x q ∧ extendedAngle x q < Real.pi) ∧
    (Genuine x ∨ ∃! k : Fin 3, Sector x k) ∧
    (∀ k : Fin 3,
      (Sector x k ↔ rawCos x (k.natAdd 3) ≤ -1) ∧
      (Sector x k ↔ ∀ q, extendedAngle x q =
        if q = k.castAdd 3 ∨ q = k.natAdd 3 then Real.pi else 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact forall_congr' (fun q => (angle_interior x q).symm)
  · by_cases hd : delta x < 0
    · exact Or.inl (interior_of_negative x hx hd)
    · obtain ⟨k, hk⟩ := sector_exists x hx (le_of_not_gt hd)
      exact Or.inr ⟨k, hk, fun j hj => sector_unique x hx k j hk hj⟩
  · intro k
    constructor
    · constructor
      · intro hk
        exact (raw_pattern x hx k hk _).1 (Or.inr rfl)
      · intro hk
        obtain ⟨hd, hn⟩ := sector_data x hx (k.natAdd 3) hk
        have ho : opposite (k.natAdd 3) = k.castAdd 3 := by fin_cases k <;> rfl
        apply (outside_bounds x hx hd _).1
        apply (num_pattern x hx hd (k.natAdd 3) hn _).1
        exact Or.inr ho.symm
    · constructor
      · intro hk q
        split_ifs with h
        · exact (angle_pi x q).mpr ((raw_pattern x hx k hk q).1 h)
        · exact (angle_zero x q).mpr ((raw_pattern x hx k hk q).2
            (not_or.mp h).1 (not_or.mp h).2)
      · intro hk
        apply (angle_pi x (k.castAdd 3)).mp
        simpa using hk (k.castAdd 3)

#print axioms positive_classification

private theorem cauchy_lower (r a b c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d) :
    r^2-1+(a-d)*(c-b)+2*(r+1)*Real.sqrt (a*b*c*d) ≤
      Real.sqrt (rad r a d) * Real.sqrt (rad r b c) := by
  let U : Fin 3 → ℝ := ![Real.sqrt (r^2-1), a-d, Real.sqrt (2*(r+1)*a*d)]
  let V : Fin 3 → ℝ := ![Real.sqrt (r^2-1), c-b, Real.sqrt (2*(r+1)*b*c)]
  have hr2 : 0 ≤ r^2-1 := by nlinarith
  have hp : 0 ≤ 2*(r+1)*a*d := by positivity
  have hq : 0 ≤ 2*(r+1)*b*c := by positivity
  have hprod : 0 ≤ a*b*c*d := by positivity
  have hs : Real.sqrt (2*(r+1)*a*d) * Real.sqrt (2*(r+1)*b*c) =
      2*(r+1)*Real.sqrt (a*b*c*d) := by
    have hs1 := Real.sq_sqrt hp
    have hs2 := Real.sq_sqrt hq
    have hs3 := Real.sq_sqrt hprod
    have he : (Real.sqrt (2*(r+1)*a*d) * Real.sqrt (2*(r+1)*b*c))^2 =
        (2*(r+1)*Real.sqrt (a*b*c*d))^2 := by
      rw [mul_pow, hs1, hs2]
      nlinarith [hs3]
    have hpos1 : 0 ≤ Real.sqrt (2*(r+1)*a*d) * Real.sqrt (2*(r+1)*b*c) := by positivity
    have hpos2 : 0 ≤ 2*(r+1)*Real.sqrt (a*b*c*d) := by positivity
    nlinarith
  have hU : ∑ i : Fin 3, U i ^ 2 = rad r a d := by
    simp [U, Fin.sum_univ_succ, Real.sq_sqrt hr2, Real.sq_sqrt hp, rad]
    <;> ring
  have hV : ∑ i : Fin 3, V i ^ 2 = rad r b c := by
    simp [V, Fin.sum_univ_succ, Real.sq_sqrt hr2, Real.sq_sqrt hq, rad]
    <;> ring
  have hUV : ∑ i : Fin 3, U i * V i =
      r^2-1+(a-d)*(c-b)+2*(r+1)*Real.sqrt (a*b*c*d) := by
    simp only [U, V, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.val_zero, Fin.val_one, Fin.val_two,
      Fin.sum_univ_zero, add_zero]
    rw [← pow_two, Real.sq_sqrt hr2, hs]
    ring
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ U V
  simpa only [hU, hV, hUV] using h

private theorem flat_product_bound (r a b o c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hc : 1 < c) (hd : 1 < d) (hflat : cosine r a b o c d ≤ -1) :
    16*a*b*c*d ≤ (r-1)^2*(o-1)^2 := by
  have hA := rad_positive r a d hr ha hd
  have hB := rad_positive r b c hr hb hc
  have hden := mul_pos (Real.sqrt_pos.mpr hA) (Real.sqrt_pos.mpr hB)
  have hC := cauchy_lower r a b c d hr ha hb hc hd
  rw [cosine, div_div, div_le_iff₀ hden] at hflat
  have hcore : 0 ≤ (r+1)*((r-1)*(o-1) -
      (a*c+b*d+2*Real.sqrt (a*b*c*d))) := by
    dsimp [numerator] at hflat
    nlinarith only [hflat, hC]
  have hgap : a*c+b*d+2*Real.sqrt (a*b*c*d) ≤ (r-1)*(o-1) := by
    have hrp : 0 < r+1 := by linarith
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hrp).mp hcore)
  have hp : 0 ≤ a*c := by positivity
  have hq : 0 ≤ b*d := by positivity
  have hs : Real.sqrt (a*c) * Real.sqrt (b*d) = Real.sqrt (a*b*c*d) := by
    rw [← Real.sqrt_mul hp]
    congr 1
    ring
  have hAM : 2*Real.sqrt (a*b*c*d) ≤ a*c+b*d := by
    have hs1 := Real.sq_sqrt hp
    have hs2 := Real.sq_sqrt hq
    nlinarith [sq_nonneg (Real.sqrt (a*c)-Real.sqrt (b*d))]
  have hgap' : 4*Real.sqrt (a*b*c*d) ≤ (r-1)*(o-1) := by linarith
  have hp4 : 0 ≤ a*b*c*d := by positivity
  have hs4 := Real.sq_sqrt hp4
  have hpos : 0 ≤ (r-1)*(o-1) := mul_nonneg (by linarith) (by linarith)
  have hsquare := mul_self_le_mul_self (by positivity : 0 ≤ 4*Real.sqrt (a*b*c*d)) hgap'
  nlinarith only [hsquare, hs4]

/-- The full source local budget, with both strictly positive correction
terms, for six independent coordinates and inclusive flat boundaries. -/
theorem native_flat_budget (r a b o c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hc : 1 < c) (hd : 1 < d) (hflat : cosine r a b o c d ≤ -1) :
    Real.log 16+2*Real.log (r/(r-1))+2*Real.log (o/(o-1)) ≤
      2*Real.log r+2*Real.log o-Real.log a-Real.log b-Real.log c-Real.log d ∧
    Real.log 16 < Real.log 16+2*Real.log (r/(r-1))+2*Real.log (o/(o-1)) := by
  have hp := flat_product_bound r a b o c d hr ha hb ho hc hd hflat
  have hr0 : 0 < r := by linarith
  have ho0 : 0 < o := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hd0 : 0 < d := by linarith
  have hr1 : 0 < r-1 := by linarith
  have ho1 : 0 < o-1 := by linarith
  have hlog : Real.log 16+Real.log a+Real.log b+Real.log c+Real.log d ≤
      2*Real.log (r-1)+2*Real.log (o-1) := by
    calc
      _ = Real.log (16*a*b*c*d) := by
        rw [Real.log_mul (by positivity : (16*a*b*c : ℝ) ≠ 0) hd0.ne',
          Real.log_mul (by positivity : (16*a*b : ℝ) ≠ 0) hc0.ne',
          Real.log_mul (by positivity : (16*a : ℝ) ≠ 0) hb0.ne',
          Real.log_mul (by norm_num : (16:ℝ) ≠ 0) ha0.ne']
      _ ≤ Real.log ((r-1)^2*(o-1)^2) := Real.log_le_log (by positivity) hp
      _ = _ := by
        rw [Real.log_mul (pow_ne_zero _ hr1.ne') (pow_ne_zero _ ho1.ne'),
          Real.log_pow, Real.log_pow]
        norm_num
  have hrr := Real.log_div hr0.ne' hr1.ne'
  have hoo := Real.log_div ho0.ne' ho1.ne'
  have hpr : 0 < Real.log (r/(r-1)) := Real.log_pos ((one_lt_div₀ hr1).mpr (by linarith))
  have hpo : 0 < Real.log (o/(o-1)) := Real.log_pos ((one_lt_div₀ ho1).mpr (by linarith))
  constructor <;> linarith

#print axioms native_flat_budget

end D5.S3.Geometry.Hyperideal.PositiveFlatClassification
