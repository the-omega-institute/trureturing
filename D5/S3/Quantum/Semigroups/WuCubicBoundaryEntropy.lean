import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import D5.S3.Quantum.Semigroups.WuCubicCornerInterpolation
import D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor
import D5.S3.Quantum.Semigroups.WuCubicThermalDerivatives
import OmegaBuild.Commands

/-! The entropy contribution to fixed-frame interpolation on the Wu cubic boundary. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped Topology

namespace D5.S3.Quantum.Semigroups.WuCubicBoundaryEntropy

open WuCubicAngularCertificate (thermalCenter)
open WuCubicOccupationTaylor (alpha_bounds_of_one_le)
open WuCubicThermalDerivatives (hasDerivAt_deriv_mul)
open WuRepeatedMiddleCubic (alpha)
open private h from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private totalAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

/-- The entropy summand of the exact centered deficit when the first middle
level varies and the second middle level is fixed at `s`. -/
def middleEntropy (r s x : ℝ) : ℝ :=
  thermalCenter r (2 / 3) x s - h r * totalAt (2 / 3) x s

/-- The same slice represents the other middle coordinate. -/
theorem middleEntropy_eq_other_middle (r s x : ℝ) :
    middleEntropy r s x = thermalCenter r (2 / 3) s x - h r * totalAt (2 / 3) s x := by
  have hmass : totalAt (2 / 3) x s = totalAt (2 / 3) s x := by
    unfold totalAt
    ring
  unfold middleEntropy thermalCenter
  rw [hmass]
  ring

private def massEntropy (A x : ℝ) : ℝ :=
  (A + x ^ 3) * Real.log ((A + x ^ 3) / 4) - x ^ 3 * Real.log (x ^ 3)

private theorem massEntropy_hasDerivAt {A x : ℝ} (hA : 0 ≤ A) (hx : 0 < x) :
    HasDerivAt (massEntropy A) (3 * x ^ 2 * Real.log ((A + x ^ 3) / (4 * x ^ 3))) x := by
  have hm : 0 < A + x ^ 3 := by positivity
  have hm4 : 0 < (A + x ^ 3) / 4 := by positivity
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  have hpow := hasDerivAt_pow 3 x
  have hmass := hpow.const_add A
  have hlog := (hmass.div_const 4).log hm4.ne'
  have hlogx := hpow.log hx3.ne'
  rw [← div_div, Real.log_div hm4.ne' hx3.ne']
  convert (hmass.fun_mul hlog).sub (hpow.fun_mul hlogx) using 1
  · rfl
  · push_cast
    field_simp [hm.ne', hx.ne']
    ring

private theorem massEntropy_profile_hasDerivAt {A x : ℝ} (hA : 0 ≤ A) (hx : 0 < x) :
    HasDerivAt (fun y => 3 * y ^ 2 * Real.log ((A + y ^ 3) / (4 * y ^ 3)))
      (x * (6 * Real.log ((A + x ^ 3) / (4 * x ^ 3)) +
        9 / (4 * ((A + x ^ 3) / (4 * x ^ 3))) - 9)) x := by
  have hm : 0 < A + x ^ 3 := by positivity
  have hm4 : 0 < (A + x ^ 3) / 4 := by positivity
  have hlog := (((hasDerivAt_pow 3 x).const_add A).div_const 4).log hm4.ne'
  have hlogx := (hasDerivAt_pow 3 x).log (pow_pos hx 3).ne'
  have hprod := ((hasDerivAt_pow 2 x).const_mul 3).fun_mul (hlog.sub hlogx)
  refine (hprod.congr_deriv ?_).congr_of_eventuallyEq ?_
  · rw [← div_div, Real.log_div hm4.ne' (pow_pos hx 3).ne', Pi.sub_apply]
    push_cast
    field_simp [hm.ne', hx.ne']
    ring
  · filter_upwards [lt_mem_nhds hx] with y hy
    have hm4y : 0 < (A + y ^ 3) / 4 := by positivity
    rw [← div_div, Real.log_div hm4y.ne' (pow_pos hy 3).ne', Pi.sub_apply]

private def fixedMass (s : ℝ) : ℝ := (2 / 3) ^ 3 + s ^ 3 + 1

private theorem middleEntropy_eq (r s : ℝ) :
    middleEntropy r s = fun x => alpha r * (massEntropy (fixedMass s) x -
      ((2 / 3) ^ 3 * Real.log ((2 / 3) ^ 3) + s ^ 3 * Real.log (s ^ 3))) := by
  funext x
  have hmass : totalAt (2 / 3) x s = fixedMass s + x ^ 3 := by
    unfold totalAt fixedMass
    ring
  unfold middleEntropy thermalCenter massEntropy
  rw [hmass]
  ring

private theorem middleEntropy_differentiableAt {r s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) :
    DifferentiableAt ℝ (middleEntropy r s) x := by
  have hA : 0 ≤ fixedMass s := by unfold fixedMass; positivity
  rw [middleEntropy_eq]
  exact (((massEntropy_hasDerivAt hA hx).sub_const _).const_mul _).differentiableAt

/-- Exact second derivative of the entropy contribution at any positive
free level. The fixed middle level can lie on either side of it. -/
theorem middleEntropy_hasDerivAt_deriv {r s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) :
    let z := ((2 / 3 : ℝ) ^ 3 + x ^ 3 + s ^ 3 + 1) / (4 * x ^ 3)
    HasDerivAt (deriv (middleEntropy r s))
      (alpha r * x * (6 * Real.log z + 9 / (4 * z) - 9)) x := by
  have hA : 0 ≤ fixedMass s := by unfold fixedMass; positivity
  let K : ℝ := (2 / 3) ^ 3 * Real.log ((2 / 3) ^ 3) + s ^ 3 * Real.log (s ^ 3)
  have hfirst : ∀ᶠ y in 𝓝 x, HasDerivAt (fun t => massEntropy (fixedMass s) t - K)
      (3 * y ^ 2 * Real.log ((fixedMass s + y ^ 3) / (4 * y ^ 3))) y := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact (massEntropy_hasDerivAt hA hy).sub_const K
  have hscaled := hasDerivAt_deriv_mul
    (Filter.Eventually.of_forall fun y => hasDerivAt_const y (alpha r)) hfirst
    (hasDerivAt_const x (0 : ℝ)) (massEntropy_profile_hasDerivAt hA hx)
  rw [middleEntropy_eq]
  dsimp only
  rw [show (2 / 3 : ℝ) ^ 3 + x ^ 3 + s ^ 3 + 1 = fixedMass s + x ^ 3 by
    unfold fixedMass; ring]
  convert hscaled using 1
  ring

private def entropyBracket (z : ℝ) : ℝ :=
  6 * Real.log z + 9 / (4 * z) - 9

private theorem entropyBracket_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt entropyBracket ((6 * z - 9 / 4) / z ^ 2) z := by
  have h := (((Real.hasDerivAt_log hz.ne').const_mul 6).add
    ((hasDerivAt_inv hz.ne').const_mul (9 / 4))).sub_const 9
  convert h using 1
  · funext y
    simp only [entropyBracket, Pi.add_apply, div_eq_mul_inv, mul_inv_rev]
    ring
  · field_simp [hz.ne']
    ring

/-- The entropy bracket decreases up to `3/8` and increases thereafter.
The two endpoint estimates use `log z ≤ z - 1`. -/
private theorem entropyBracket_le {z Z : ℝ} (hz : 1 / 4 ≤ z) (hZ : z ≤ Z) :
    entropyBracket z ≤ max (-6) (6 * (Z - 1) + 9 / (4 * Z) - 9) := by
  by_cases ht : z ≤ 3 / 8
  · have hd (u : ℝ) (hu : u ∈ Icc (1 / 4 : ℝ) (3 / 8)) :=
      entropyBracket_hasDerivAt (lt_of_lt_of_le (by norm_num) hu.1)
    have hmono : AntitoneOn entropyBracket (Icc (1 / 4 : ℝ) (3 / 8)) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
      · exact fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
      · intro u hu
        have hu' := interior_subset hu
        rw [(hd u hu').deriv]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hu'.2]) (sq_nonneg _)
    have hquarter : entropyBracket (1 / 4) ≤ -6 := by
      have hhalf := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      have hlog : Real.log (1 / 4) = 2 * Real.log (1 / 2) := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.log_pow]
        norm_num
      norm_num [entropyBracket, hlog]
      linarith only [hhalf]
    exact (hmono ⟨le_rfl, by norm_num⟩ ⟨hz, ht⟩ hz).trans
      (hquarter.trans (le_max_left _ _))
  · have ht' : 3 / 8 ≤ z := le_of_not_ge ht
    have hd (u : ℝ) (hu : u ∈ Icc (3 / 8 : ℝ) Z) :=
      entropyBracket_hasDerivAt (lt_of_lt_of_le (by norm_num) hu.1)
    have hmono : MonotoneOn entropyBracket (Icc (3 / 8 : ℝ) Z) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · exact fun u hu => (hd u hu).continuousAt.continuousWithinAt
      · exact fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
      · intro u hu
        have hu' := interior_subset hu
        rw [(hd u hu').deriv]
        exact div_nonneg (by linarith only [hu'.1]) (sq_nonneg _)
    have hlog := Real.log_le_sub_one_of_pos ((by norm_num : (0 : ℝ) < 1 / 4).trans_le
      (hz.trans hZ))
    have hupper : entropyBracket Z ≤ 6 * (Z - 1) + 9 / (4 * Z) - 9 := by
      unfold entropyBracket
      linarith only [hlog]
    exact (hmono ⟨ht', hZ⟩ ⟨ht'.trans hZ, le_rfl⟩ hZ).trans
      (hupper.trans (le_max_right _ _))

private theorem one_third_le_alpha {r : ℝ} (hr : 1 ≤ r) (hrhi : r ≤ 6 / 5) :
    1 / 3 ≤ alpha r := by
  rcases eq_or_lt_of_le hr with h | h
  · subst r
    norm_num [alpha]
  simp only [alpha, h.ne', ↓reduceIte]
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans h)
  have hlog₀ := Real.log_pos h
  have hpoly : 0 < r ^ 2 + r + 1 := by nlinarith only [hr, sq_nonneg r]
  have hr₂ := pow_le_pow_left₀ (zero_le_one.trans hr) hrhi 2
  have hpoly' : (1 / 3 : ℝ) * (4 * (r ^ 2 + r + 1)) ≤ 3 * (r + 1) := by
    linarith only [hr, hrhi, hr₂]
  apply (le_div_iff₀ (by positivity)).2
  calc
    _ = (1 / 3 : ℝ) * (4 * (r ^ 2 + r + 1)) * Real.log r := (mul_assoc _ _ _).symm
    _ ≤ (1 / 3 : ℝ) * (4 * (r ^ 2 + r + 1)) * (r - 1) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ 3 * (r + 1) * (r - 1) := mul_le_mul_of_nonneg_right hpoly' (sub_nonneg.mpr hr)
    _ = _ := by ring

/-- The entropy term in `box_curvatures` for a free middle coordinate in
`[a,b]`, with the other coordinate bounded above by `sHi`. The two
coordinates may be unsorted and may coincide. -/
theorem middleEntropy_deriv2_le {r s sHi a b x : ℝ}
    (hr : 1 ≤ r) (hrhi : r ≤ 6 / 5)
    (hs : 0 ≤ s) (hsHi : s ≤ sHi) (ha : 0 < a) (hx : x ∈ Icc a b) :
    let Z := ((2 / 3 : ℝ) ^ 3 + b ^ 3 + sHi ^ 3 + 1) / (4 * a ^ 3)
    let E := max (-6) (6 * (Z - 1) + 9 / (4 * Z) - 9)
    deriv (deriv (middleEntropy r s)) x ≤ E * (if E < 0 then a / 3 else b / 2) := by
  let z := ((2 / 3 : ℝ) ^ 3 + x ^ 3 + s ^ 3 + 1) / (4 * x ^ 3)
  intro Z E
  have hx₀ := ha.trans_le hx.1
  have hz : (1 / 4 : ℝ) ≤ z := by
    apply (le_div_iff₀ (show 0 < 4 * x ^ 3 by positivity)).2
    have hs₃ : 0 ≤ s ^ 3 := by positivity
    linarith only [hs₃]
  have hZ : z ≤ Z := by
    have hb₀ := hx₀.le.trans hx.2
    have hsHi₀ := hs.trans hsHi
    apply div_le_div₀ (by positivity)
    · have hxb := pow_le_pow_left₀ hx₀.le hx.2 3
      have hss := pow_le_pow_left₀ hs hsHi 3
      linarith only [hxb, hss]
    · positivity
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hx.1 3) (by norm_num)
  have hbr : entropyBracket z ≤ E := entropyBracket_le hz hZ
  obtain ⟨hα₀, hαhi⟩ := alpha_bounds_of_one_le hr
  have hαlo := one_third_le_alpha hr hrhi
  rw [(middleEntropy_hasDerivAt_deriv (r := r) hs hx₀).deriv]
  change alpha r * x * entropyBracket z ≤ _
  apply (mul_le_mul_of_nonneg_left hbr (mul_nonneg hα₀ hx₀.le)).trans
  rw [mul_comm (alpha r * x)]
  split_ifs with hE
  · apply mul_le_mul_of_nonpos_left _ hE.le
    calc
      a / 3 = 1 / 3 * a := by ring
      _ ≤ alpha r * x := mul_le_mul hαlo hx.1 ha.le hα₀
  · apply mul_le_mul_of_nonneg_left _ (le_of_not_gt hE)
    calc
      alpha r * x ≤ 1 / 2 * b := mul_le_mul hαhi hx.2 hx₀.le (by norm_num)
      _ = b / 2 := by ring

/-- The entropy slice has the signed chord correction given by its
box curvature bound. -/
theorem middleEntropy_chord_le {r s sHi a b x : ℝ}
    (hr : 1 ≤ r) (hrhi : r ≤ 6 / 5)
    (hs : 0 ≤ s) (hsHi : s ≤ sHi) (ha : 0 < a) (hab : a < b) (hx : x ∈ Icc a b) :
    let Z := ((2 / 3 : ℝ) ^ 3 + b ^ 3 + sHi ^ 3 + 1) / (4 * a ^ 3)
    let E := max (-6) (6 * (Z - 1) + 9 / (4 * Z) - 9)
    let C := E * (if E < 0 then a / 3 else b / 2)
    ((b - x) / (b - a)) * middleEntropy r s a + ((x - a) / (b - a)) * middleEntropy r s b -
      (C / 2) * (x - a) * (b - x) ≤ middleEntropy r s x := by
  intro Z E C
  refine WuCubicCornerInterpolation.corner_interpolation C a b x hab ?_ ?_ ?_ ?_ hx.1 hx.2
  · exact fun y hy => (middleEntropy_differentiableAt hs (ha.trans_le hy.1)).continuousAt
      |>.continuousWithinAt
  · exact fun y hy => (middleEntropy_differentiableAt hs (ha.trans hy.1)).differentiableWithinAt
  · exact fun y hy => (middleEntropy_hasDerivAt_deriv hs (ha.trans hy.1)).differentiableAt
      |>.differentiableWithinAt
  · intro y hy
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      middleEntropy_deriv2_le hr hrhi hs hsHi ha (Ioo_subset_Icc_self hy)

end D5.S3.Quantum.Semigroups.WuCubicBoundaryEntropy

namespace D5.S3.Quantum.Semigroups.WuCubicBoundaryFixedFrame

open _root_.Matrix
open scoped BigOperators _root_.Matrix
open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate (physicalFrame normalizedDeficit thermalCenter)
open WuCubicBoundaryEntropy
open WuCubicOccupationTaylor (alpha_bounds_of_one_le)
open WuRepeatedMiddleCubic (Frame alpha weight imbalance)
open private physicalFrame_columns physicalFrame_rows from
  D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open private levelsAt totalAt cubic source_centered_at from
  D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private row_weight col_weight h c e bias gamma gibbsLow gibbsHigh from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private cubic_coefficient_bounds from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

/-- Both middle slices of the actual normalized deficit in the same unitary
frame, with the outer levels fixed at 2/3 and 1. -/
def middleDeficit (axis : Bool) (r : ℝ) (U : unitary Mat) (s x : ℝ) : ℝ :=
  if axis then normalizedDeficit r U (2 / 3) x s
  else normalizedDeficit r U (2 / 3) s x

private def middleIndex (axis : Bool) : Fin 4 := if axis then 1 else 2
private def otherIndex (axis : Bool) : Fin 4 := if axis then 2 else 1

private theorem weight_nonneg (V : Frame) (i j : Fin 4) : 0 ≤ weight V i j :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

private theorem coefficient_bounds {r rHi : ℝ} (hr : 1 ≤ r)
    (hrHi : r ≤ rHi) (hrband : r ≤ 6 / 5) :
    h r ≤ 9 / 4 * (rHi - 1)^2 ∧
    0 ≤ bias r ∧ bias r ≤ 3 * (rHi - 1) / 2 ∧
    1 ≤ c r ∧ c r ≤ 9 / 8 ∧
    0 ≤ e r ∧ e r ≤ 3 * (rHi - 1) / 16 := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have ht : 0 ≤ r - 1 := sub_nonneg.mpr hr
  have htHi : r - 1 ≤ rHi - 1 := by linarith only [hrHi]
  have hd : 0 < 1 + r ^ 3 := by positivity
  have hr2 := pow_le_pow_left₀ zero_le_one hr 2
  have hgamma : gamma r * (r + 1) ≤ 9 / 4 := by
    have hp : r ≤ r ^ 3 := by nlinarith only [mul_nonneg hr0 (show 0 ≤ r^2 - 1 by linarith only [hr2])]
    unfold gamma
    calc
      _ = 9 / 4 * ((r + 1) / (1 + r ^ 3)) := by
        field_simp [hd.ne']
      _ ≤ 9 / 4 * 1 := mul_le_mul_of_nonneg_left ((div_le_one hd).2 (by linarith only [hp])) (by norm_num)
      _ = _ := by ring
  have hlog : Real.log (4 * gibbsLow r * gibbsHigh r) ≤ 0 := by
    have heq : 4 * gibbsLow r * gibbsHigh r = 4 * r^3 / (1 + r^3)^2 := by
      unfold gibbsHigh gibbsLow
      field_simp [hd.ne']
    rw [heq]
    apply Real.log_nonpos
    · positivity
    · apply (div_le_one (by positivity)).2
      nlinarith only [sq_nonneg (r^3 - 1)]
  have hh : h r ≤ 9 / 4 * (rHi - 1)^2 := by
    have hα := (alpha_bounds_of_one_le hr).1
    unfold h
    calc
      _ ≤ (gamma r * (r + 1)) * (r - 1)^2 := by
        nlinarith only [mul_nonpos_of_nonneg_of_nonpos hα hlog]
      _ ≤ (9 / 4) * (r - 1)^2 := mul_le_mul_of_nonneg_right hgamma (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htHi 2) (by norm_num)
  have hpoly : 0 ≤ r ^ 5 + r ^ 4 - 3 * r ^ 2 + 1 := by
    rw [show r ^ 5 + r ^ 4 - 3 * r ^ 2 + 1 =
      (r - 1) * ((r - 1) ^ 4 + 6 * (r - 1) ^ 3 + 14 * (r - 1) ^ 2 + 13 * (r - 1) + 3) by ring]
    positivity
  have hb : bias r ≤ 3 * (r - 1) / 2 := by
    rw [bias, div_le_iff₀ (show 0 < 3 * (r ^ 2 + r + 1) by positivity)]
    apply sub_nonneg.mp
    rw [show (3 * (r - 1) / 2) * (3 * (r ^ 2 + r + 1)) -
      2 * gamma r * r * (r - 1) * (r ^ 2 + 4 * r + 1) =
      9 * (r - 1) * (r ^ 5 + r ^ 4 - 3 * r ^ 2 + 1) / (2 * (1 + r ^ 3)) by
        unfold gamma
        field_simp [hd.ne']
        ring]
    positivity
  have hc : 1 ≤ c r := by
    have hden : 0 < r ^ 2 - r + 1 := by nlinarith only [sq_nonneg (r - 1)]
    have hfac : c r = (9 / 8 : ℝ) * r / (r^2 - r + 1) := by
      unfold c gamma
      field_simp [hd.ne', hden.ne']
      ring
    rw [hfac, le_div_iff₀ hden]
    have hs := pow_le_pow_left₀ ht (show r - 1 ≤ 1 / 5 by linarith only [hrband]) 2
    nlinarith only [hs, hr]
  have he : e r ≤ 3 * (r - 1) / 16 := by
    have her : 2 * r ≤ 1 + r ^ 3 := by
      nlinarith only [mul_nonneg ht (show 0 ≤ r ^ 2 + r - 1 by linarith only [hr2, hr])]
    have heq : e r = (3 / 8 : ℝ) * (r / (1 + r ^ 3)) * (r - 1) := by
      unfold e gamma
      field_simp [hd.ne']
      ring
    rw [heq]
    have he' : r / (1 + r ^ 3) ≤ 1 / 2 := (div_le_iff₀ hd).2 (by linarith only [her])
    calc
      _ ≤ (3 / 8 : ℝ) * (1 / 2) * (r - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he' (by norm_num)) ht
      _ = _ := by ring
  obtain ⟨_, hcHi, he0, _⟩ := cubic_coefficient_bounds hr (by linarith only [hrband])
  exact ⟨hh, by unfold bias gamma; positivity, by linarith only [hb, htHi],
    hc, hcHi, he0, by linarith only [he, htHi]⟩

private def edge (r : ℝ) (V : Frame) (i j : Fin 4) (y x : ℝ) : ℝ :=
  weight V i j * cubic (c r) (e r) x y + weight V j i * cubic (c r) (e r) y x

private def edgeSecond (r : ℝ) (V : Frame) (i j : Fin 4) (y x : ℝ) : ℝ :=
  (weight V i j + weight V j i) * c r * (6 * x - 2 * y) +
    (weight V i j - weight V j i) * 6 * e r * (x - y)

private theorem edge_second_le {r t low b x y : ℝ} (V : Frame) (i j : Fin 4)
    (hc : 1 ≤ c r) (hcHi : c r ≤ 9 / 8) (he : 0 ≤ e r)
    (heHi : e r ≤ 3 * t / 16) (hl : 0 ≤ low)
    (hx : low ≤ x) (hxb : x ≤ b) (hx1 : x ≤ 1) (hy : low ≤ y) (hy1 : y ≤ 1) :
    edgeSecond r V i j y x ≤ (weight V i j + weight V j i) *
      (27 / 4 * b - 2 * low + 9 / 8 * t * (1 - low)) := by
  have hx0 := hl.trans hx
  have hy0 := hl.trans hy
  have hb0 := hx0.trans hxb
  have hspread : 0 ≤ 1 - low := by linarith only [hx, hx1]
  have hc0 : 0 ≤ c r := by linarith only [hc]
  have hs : c r * (6 * x - 2 * y) ≤ 27 / 4 * b - 2 * low := by
    have hpos := mul_le_mul hcHi hxb hx0 (by norm_num : (0 : ℝ) ≤ 9 / 8)
    have hneg := mul_le_mul hc hy (by exact hl) hc0
    nlinarith only [hpos, hneg]
  have hp : 6 * e r * (x - y) ≤ 9 / 8 * t * (1 - low) := by
    calc
      _ ≤ 6 * e r * (1 - low) :=
        mul_le_mul_of_nonneg_left (by linarith only [hx1, hy]) (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right heHi hspread
        nlinarith only [hh]
  have hn : 6 * e r * (y - x) ≤ 9 / 8 * t * (1 - low) := by
    calc
      _ ≤ 6 * e r * (1 - low) :=
        mul_le_mul_of_nonneg_left (by linarith only [hy1, hx]) (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right heHi hspread
        nlinarith only [hh]
  have hi := mul_le_mul_of_nonneg_left (add_le_add hs hp) (weight_nonneg V i j)
  have hj := mul_le_mul_of_nonneg_left (add_le_add hs hn) (weight_nonneg V j i)
  unfold edgeSecond
  nlinarith only [hi, hj]

private def fixedPart (axis : Bool) (r : ℝ) (V : Frame) (s : ℝ) : ℝ :=
  h r * totalAt (2 / 3) 0 s +
    bias r * (imbalance V 0 * (2 / 3)^3 + imbalance V (otherIndex axis) * s^3 + imbalance V 3) +
    edge r V 0 (otherIndex axis) s (2 / 3) +
    edge r V 0 3 1 (2 / 3) + edge r V (otherIndex axis) 3 1 s

private def middlePolynomial (axis : Bool) (r : ℝ) (V : Frame) (s x : ℝ) : ℝ :=
  (h r + bias r * imbalance V (middleIndex axis)) * x^3 +
    edge r V (middleIndex axis) 0 (2 / 3) x +
    edge r V (middleIndex axis) (otherIndex axis) s x +
    edge r V (middleIndex axis) 3 1 x + fixedPart axis r V s

private def polynomialSecond (axis : Bool) (r : ℝ) (V : Frame) (s x : ℝ) : ℝ :=
  6 * x * (h r + bias r * imbalance V (middleIndex axis)) +
    edgeSecond r V (middleIndex axis) 0 (2 / 3) x +
    edgeSecond r V (middleIndex axis) (otherIndex axis) s x +
    edgeSecond r V (middleIndex axis) 3 1 x

private theorem middleDeficit_eq {r : ℝ} (hr : 1 ≤ r) (axis : Bool) (U : unitary Mat)
    {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) :
    middleDeficit axis r U s x =
      middlePolynomial axis r (physicalFrame U) s x + middleEntropy r s x := by
  cases axis
  · rw [middleDeficit, ite_eq_right Bool.false_ne_true, normalizedDeficit,
      source_centered_at hr _ (physicalFrame_columns U) (physicalFrame_rows U) (by norm_num) hs hx,
      middleEntropy_eq_other_middle]
    simp [middlePolynomial, fixedPart, middleIndex, otherIndex, edge, Fin.sum_univ_four,
      levelsAt, totalAt, thermalCenter, cubic]
    ring
  · rw [middleDeficit, ite_eq_left rfl, normalizedDeficit,
      source_centered_at hr _ (physicalFrame_columns U) (physicalFrame_rows U) (by norm_num) hx hs,
      middleEntropy]
    simp [middlePolynomial, fixedPart, middleIndex, otherIndex, edge, Fin.sum_univ_four,
      levelsAt, totalAt, thermalCenter, cubic]
    ring

private def edgeFirst (r : ℝ) (V : Frame) (i j : Fin 4) (y x : ℝ) : ℝ :=
  (weight V i j + weight V j i) * c r * (3*x^2 - 2*x*y - y^2) +
    (weight V i j - weight V j i) * 3 * e r * (x-y)^2

private theorem edge_hasDerivAt (r : ℝ) (V : Frame) (i j : Fin 4) (y x : ℝ) :
    HasDerivAt (edge r V i j y) (edgeFirst r V i j y x) x := by
  let A := (weight V i j + weight V j i) * c r
  let B := (weight V i j - weight V j i) * e r
  have hpoly := (((((hasDerivAt_pow 3 x).const_mul (A + B)).add
    ((hasDerivAt_pow 2 x).const_mul ((-A - 3*B)*y))).add
    ((hasDerivAt_id x).const_mul ((-A + 3*B)*y^2))).add
    (hasDerivAt_const x ((A - B)*y^3)))
  convert hpoly using 1
  · funext z
    dsimp [edge, cubic, A, B]
    ring
  · simp [edgeFirst, A, B]
    ring

private theorem edgeFirst_hasDerivAt (r : ℝ) (V : Frame) (i j : Fin 4) (y x : ℝ) :
    HasDerivAt (edgeFirst r V i j y) (edgeSecond r V i j y x) x := by
  let A := (weight V i j + weight V j i) * c r
  let B := (weight V i j - weight V j i) * e r
  have hpoly := ((((hasDerivAt_pow 2 x).const_mul (3*(A+B))).add
    ((hasDerivAt_id x).const_mul ((-2*A-6*B)*y))).add
    (hasDerivAt_const x ((-A+3*B)*y^2)))
  convert hpoly using 1
  · funext z
    dsimp [edgeFirst, A, B]
    ring
  · simp [edgeSecond, A, B]
    ring

private def polynomialFirst (axis : Bool) (r : ℝ) (V : Frame) (s x : ℝ) : ℝ :=
  (h r + bias r * imbalance V (middleIndex axis)) * (3*x^2) +
    edgeFirst r V (middleIndex axis) 0 (2 / 3) x +
    edgeFirst r V (middleIndex axis) (otherIndex axis) s x +
    edgeFirst r V (middleIndex axis) 3 1 x

private theorem middlePolynomial_hasDerivAt (axis : Bool) (r : ℝ) (V : Frame) (s x : ℝ) :
    HasDerivAt (middlePolynomial axis r V s) (polynomialFirst axis r V s x) x := by
  have hd := ((((hasDerivAt_pow 3 x).const_mul
      (h r + bias r * imbalance V (middleIndex axis))).add
    (edge_hasDerivAt r V (middleIndex axis) 0 (2 / 3) x)).add
    (edge_hasDerivAt r V (middleIndex axis) (otherIndex axis) s x)).add
    (edge_hasDerivAt r V (middleIndex axis) 3 1 x)
  convert hd.add_const (fixedPart axis r V s) using 1
  · rfl
  · simp [polynomialFirst]

private theorem polynomialFirst_hasDerivAt (axis : Bool) (r : ℝ) (V : Frame) (s x : ℝ) :
    HasDerivAt (polynomialFirst axis r V s) (polynomialSecond axis r V s x) x := by
  have hd := ((((hasDerivAt_pow 2 x).const_mul (3 *
      (h r + bias r * imbalance V (middleIndex axis)))).add
    (edgeFirst_hasDerivAt r V (middleIndex axis) 0 (2 / 3) x)).add
    (edgeFirst_hasDerivAt r V (middleIndex axis) (otherIndex axis) s x)).add
    (edgeFirst_hasDerivAt r V (middleIndex axis) 3 1 x)
  convert hd using 1
  · funext z
    dsimp [polynomialFirst]
    ring
  · simp [polynomialSecond]
    ring

private theorem middlePolynomial_hasDerivAt_deriv (axis : Bool) (r : ℝ) (V : Frame) (s x : ℝ) :
    HasDerivAt (deriv (middlePolynomial axis r V s)) (polynomialSecond axis r V s x) x := by
  have hf : deriv (middlePolynomial axis r V s) = polynomialFirst axis r V s :=
    funext fun y => (middlePolynomial_hasDerivAt axis r V s y).deriv
  rw [hf]
  exact polynomialFirst_hasDerivAt axis r V s x

private theorem incidence_le (axis : Bool) (U : unitary Mat) :
    let V := physicalFrame U
    let i := middleIndex axis
    let j := otherIndex axis
    (weight V i 0 + weight V 0 i) + (weight V i j + weight V j i) +
      (weight V i 3 + weight V 3 i) ≤ 2 := by
  intro V i j
  have hrow := row_weight V (physicalFrame_columns U) (physicalFrame_rows U) i
  have hcol := col_weight V (physicalFrame_columns U) (physicalFrame_rows U) i
  have hdiag := weight_nonneg V i i
  cases axis <;> simp [i, j, middleIndex, otherIndex, Fin.sum_univ_four] at hrow hcol hdiag ⊢ <;>
    linarith only [hrow, hcol, hdiag]

private theorem imbalance_le_one (V : Frame) (hV : Vᴴ * V = 1) (hVV : V * Vᴴ = 1)
    (i : Fin 4) : imbalance V i ≤ 1 := by
  have hc := col_weight V hV hVV i
  have hnon : 0 ≤ ∑ j, weight V j i := Finset.sum_nonneg fun j _ => weight_nonneg V j i
  linarith only [hc, hnon]

/-- The non-entropy pure curvature from the fixed-frame box bound in Wu (3.54). -/
def nonEntropyCurvature (rHi low b : ℝ) : ℝ :=
  let t := rHi - 1
  ((27 / 2) * (1 + t^2) + 9*t) * b - 4*low + (9 / 4)*t*(1-low)

private theorem polynomialSecond_le (axis : Bool) (U : unitary Mat)
    {r rHi low s b x : ℝ} (hr : 1 ≤ r) (hrHi : r ≤ rHi) (hrband : r ≤ 6 / 5)
    (hl : 0 ≤ low) (hlm : low ≤ 2 / 3) (hls : low ≤ s) (hs1 : s ≤ 1)
    (hlx : low ≤ x) (hxb : x ≤ b) (hb1 : b ≤ 1) :
    polynomialSecond axis r (physicalFrame U) s x ≤ nonEntropyCurvature rHi low b := by
  let V := physicalFrame U
  let i := middleIndex axis
  let j := otherIndex axis
  let t := rHi - 1
  let K : ℝ := 27 / 4 * b - 2 * low + 9 / 8 * t * (1-low)
  have ht : 0 ≤ t := by dsimp [t]; linarith only [hr, hrHi]
  have hx0 := hl.trans hlx
  have hb0 := hx0.trans hxb
  have hx1 := hxb.trans hb1
  have hlow1 := hlx.trans hx1
  have hK : 0 ≤ K := by
    have hspread := sub_nonneg.mpr hlow1
    have hprod := mul_nonneg ht hspread
    dsimp [K]
    nlinarith only [hprod, hl, hlx, hxb]
  obtain ⟨hh, hb, hbHi, hc, hcHi, he, heHi⟩ := coefficient_bounds hr hrHi hrband
  have himb := imbalance_le_one V (physicalFrame_columns U) (physicalFrame_rows U) i
  have hco : h r + bias r * imbalance V i ≤ 9 / 4 * t^2 + 3 * t / 2 := by
    have hmul := mul_le_mul_of_nonneg_left himb hb
    dsimp [t]
    nlinarith only [hh, hbHi, hmul]
  have hsc : 6*x*(h r + bias r * imbalance V i) ≤
      6*b*(9 / 4*t^2 + 3*t/2) := by
    calc
      _ ≤ 6*x*(9 / 4*t^2 + 3*t/2) := mul_le_mul_of_nonneg_left hco (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hxb]) (by positivity)
  have h₀ := edge_second_le V i 0 hc hcHi he heHi hl hlx hxb hx1 hlm (by norm_num : (2/3 : ℝ) ≤ 1)
  have h₁ := edge_second_le V i j hc hcHi he heHi hl hlx hxb hx1 hls hs1
  have h₂ := edge_second_le V i 3 hc hcHi he heHi hl hlx hxb hx1 hlow1 le_rfl
  have hinc := incidence_le axis U
  change (weight V i 0 + weight V 0 i) + (weight V i j + weight V j i) +
    (weight V i 3 + weight V 3 i) ≤ 2 at hinc
  have hsum := mul_le_mul_of_nonneg_right hinc hK
  change edgeSecond r V i 0 (2/3) x ≤ (weight V i 0 + weight V 0 i) * K at h₀
  change edgeSecond r V i j s x ≤ (weight V i j + weight V j i) * K at h₁
  change edgeSecond r V i 3 1 x ≤ (weight V i 3 + weight V 3 i) * K at h₂
  change _ ≤ nonEntropyCurvature rHi low b
  have heq : polynomialSecond axis r V s x =
      6*x*(h r + bias r * imbalance V i) + edgeSecond r V i 0 (2/3) x +
      edgeSecond r V i j s x + edgeSecond r V i 3 1 x := rfl
  rw [heq]
  calc
    _ ≤ 6*b*(9 / 4*t^2 + 3*t/2) + 2*K := by linarith only [hsc, h₀, h₁, h₂, hsum]
    _ = _ := by unfold nonEntropyCurvature; dsimp [t, K]; ring

/-- The full signed curvature upper bound, with the entropy term from the same
fixed-frame box and its sign-dependent multiplier. -/
def middleCurvature (rHi low sHi a b : ℝ) : ℝ :=
  let Z := ((2 / 3 : ℝ)^3 + b^3 + sHi^3 + 1) / (4*a^3)
  let E := max (-6) (6*(Z-1) + 9/(4*Z) - 9)
  nonEntropyCurvature rHi low b + E * (if E < 0 then a/3 else b/2)

private theorem middleDeficit_eventuallyEq {r : ℝ} (hr : 1 ≤ r) (axis : Bool)
    (U : unitary Mat) {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) :
    middleDeficit axis r U s =ᶠ[𝓝 x]
      (fun y => middlePolynomial axis r (physicalFrame U) s y + middleEntropy r s y) := by
  filter_upwards [lt_mem_nhds hx] with y hy
  exact middleDeficit_eq hr axis U hs hy.le

private theorem middleDeficit_differentiableAt {r : ℝ} (hr : 1 ≤ r)
    (axis : Bool) (U : unitary Mat) {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) :
    DifferentiableAt ℝ (middleDeficit axis r U s) x :=
  ((middlePolynomial_hasDerivAt axis r (physicalFrame U) s x).differentiableAt.add
    (middleEntropy_differentiableAt hs hx)).congr_of_eventuallyEq
      (middleDeficit_eventuallyEq hr axis U hs hx)

private theorem middleDeficit_hasDerivAt_deriv {r : ℝ} (hr : 1 ≤ r)
    (axis : Bool) (U : unitary Mat) {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) :
    HasDerivAt (deriv (middleDeficit axis r U s))
      (polynomialSecond axis r (physicalFrame U) s x +
        deriv (deriv (middleEntropy r s)) x) x := by
  have he := middleEntropy_hasDerivAt_deriv (r := r) hs hx
  have hd := (middlePolynomial_hasDerivAt_deriv axis r (physicalFrame U) s x).add
    (he.congr_deriv he.deriv.symm)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(middleDeficit_eventuallyEq hr axis U hs hx).deriv, lt_mem_nhds hx] with y hy hypos
  rw [hy]
  change deriv (middlePolynomial axis r (physicalFrame U) s + middleEntropy r s) y = _
  rw [deriv_add (middlePolynomial_hasDerivAt axis r (physicalFrame U) s y).differentiableAt
    (middleEntropy_differentiableAt hs hypos)]
  rfl

/-- Non-entropy curvature of the actual deficit on either middle slice. -/
theorem middleDeficit_sub_entropy_deriv2_le (axis : Bool) (U : unitary Mat)
    {r rHi low s b x : ℝ} (hr : 1 ≤ r) (hrHi : r ≤ rHi) (hrband : r ≤ 6 / 5)
    (hl : 0 ≤ low) (hlm : low ≤ 2 / 3) (hls : low ≤ s) (hs1 : s ≤ 1)
    (hlx : low ≤ x) (hx : 0 < x) (hxb : x ≤ b) (hb1 : b ≤ 1) :
    deriv (deriv (fun y => middleDeficit axis r U s y - middleEntropy r s y)) x ≤
      nonEntropyCurvature rHi low b := by
  have hlocal : (fun y => middleDeficit axis r U s y - middleEntropy r s y) =ᶠ[𝓝 x]
      middlePolynomial axis r (physicalFrame U) s := by
    filter_upwards [middleDeficit_eventuallyEq hr axis U (hl.trans hls) hx] with y hy
    rw [hy, add_sub_cancel_right]
  rw [hlocal.deriv.deriv_eq, (middlePolynomial_hasDerivAt_deriv axis r (physicalFrame U) s x).deriv]
  exact polynomialSecond_le axis U hr hrHi hrband hl hlm hls hs1 hlx hxb hb1

/-- Pure middle-axis curvature for the actual fixed unitary frame, including
crossing and coincident levels. -/
theorem middleDeficit_deriv2_le (axis : Bool) (U : unitary Mat)
    {r rHi low s sHi a b x : ℝ} (hr : 1 ≤ r) (hrHi : r ≤ rHi) (hrband : r ≤ 6 / 5)
    (hl : 0 ≤ low) (hlm : low ≤ 2 / 3) (hls : low ≤ s) (hsHi : s ≤ sHi) (hs1 : s ≤ 1)
    (hla : low ≤ a) (ha : 0 < a) (hb1 : b ≤ 1) (hx : x ∈ Icc a b) :
    deriv (deriv (middleDeficit axis r U s)) x ≤ middleCurvature rHi low sHi a b := by
  have hs := hl.trans hls
  rw [(middleDeficit_hasDerivAt_deriv hr axis U hs (ha.trans_le hx.1)).deriv]
  exact add_le_add (polynomialSecond_le axis U hr hrHi hrband hl hlm hls hs1
    (hla.trans hx.1) hx.2 hb1) (middleEntropy_deriv2_le hr hrband hs hsHi ha hx)

/-- The actual deficit lies above its endpoint chord with the signed curvature
correction on either middle coordinate. -/
theorem middleDeficit_chord_le (axis : Bool) (U : unitary Mat)
    {r rHi low s sHi a b x : ℝ} (hr : 1 ≤ r) (hrHi : r ≤ rHi) (hrband : r ≤ 6 / 5)
    (hl : 0 ≤ low) (hlm : low ≤ 2 / 3) (hls : low ≤ s) (hsHi : s ≤ sHi) (hs1 : s ≤ 1)
    (hla : low ≤ a) (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1) (hx : x ∈ Icc a b) :
    ((b-x)/(b-a)) * middleDeficit axis r U s a + ((x-a)/(b-a)) * middleDeficit axis r U s b -
      (middleCurvature rHi low sHi a b / 2) * (x-a)*(b-x) ≤ middleDeficit axis r U s x := by
  have hs := hl.trans hls
  refine WuCubicCornerInterpolation.corner_interpolation _ a b x hab ?_ ?_ ?_ ?_ hx.1 hx.2
  · exact fun y hy => (middleDeficit_differentiableAt hr axis U hs (ha.trans_le hy.1)).continuousAt
      |>.continuousWithinAt
  · exact fun y hy => (middleDeficit_differentiableAt hr axis U hs (ha.trans hy.1)).differentiableWithinAt
  · exact fun y hy => (middleDeficit_hasDerivAt_deriv hr axis U hs (ha.trans hy.1)).differentiableAt
      |>.differentiableWithinAt
  · intro y hy
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      middleDeficit_deriv2_le axis U hr hrHi hrband hl hlm hls hsHi hs1 hla ha hb1 (Ioo_subset_Icc_self hy)

end D5.S3.Quantum.Semigroups.WuCubicBoundaryFixedFrame
