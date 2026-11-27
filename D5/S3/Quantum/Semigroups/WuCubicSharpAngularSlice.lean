import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicSharpAngularSlice

open WuCubicDirectedOccupationCap (Mat frameVector oddProbability)
open WuCubicCoupledCuts
open WuCubicRankTwoCut (cutImbalance cutEvenOffset forwardCutWeight reverseCutWeight)
open WuCubicAngularCertificate
open WuCubicOccupationEnvelope (sym)
open WuCubicSharpLongCrossing (singletonPairWeight_ge_radical)
open private oddPairMass_eq singletonCutWeight_eq adjacentCutWeight_ge_local from
  D5.S3.Quantum.Semigroups.WuCubicCoupledCuts
open private odd_mass_mem from D5.S3.Quantum.Semigroups.WuCubicSharpLongCrossing
open private radical_unscaled weighted_charge spectral_coefficients_nonneg centered_retained_le from
  D5.S3.Quantum.Semigroups.WuCubicAngularCertificate

/-- The sharp slice energy at the physical imbalance and singleton tilts, after
eliminating the signed even offset. The two adjacent weights and the two charge
weights are independently admissible. The remaining variables can be minimized
on the imbalance interval and the singleton square as in `sliced_energy`. -/
theorem sharp_slice_le_normalizedDeficit {r m n q lo L R μ₀ μ₂ : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1)
    (hlo : 0 ≤ lo) (hlo1 : lo < 1) (hv : lo ≤ |cutImbalance U|)
    (hL : L ∈ Set.Icc 0 (lowerCoeff r m n q)) (hR : R ∈ Set.Icc 0 (upperCoeff r n q))
    (hμ₀ : μ₀ ∈ Set.Icc 0 (cutBias r m n q 0)) (hμ₂ : μ₂ ∈ Set.Icc 0 (cutBias r m n q 2)) :
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let Z₀ := lowerCoeff r m n q
    let Z₂ := upperCoeff r n q
    let κ := longCoeff r m n q / 4
    let v := |cutImbalance U|
    let y₀ := 1 - oddTilt U 0
    let y₃ := 1 - oddTilt U 3
    let surplus := 2 * lo ^ 2 / (1 - lo ^ 2)
    let H := A 1 + (L + R) / 2
    let K := 2 * A 1 + (1 + surplus) * H
    let C := A 1 + (Z₀ + Z₂) / 2 + (3 * (A 0 + A 2) - B 0 - B 2) / 2
    let g := μ₀ - μ₂
    let I := if K = 0 then 0 else 1 / (4 * K)
    let loss := if K = 0 then |g| else I * g ^ 2
    thermalCenter r m n q +
      (C - loss + (H * v ^ 2 - (B 1 + μ₀ + μ₂) * v) +
        ((A 0 + Z₀ - L) / 2 + κ - I * L ^ 2) * y₀ ^ 2 +
        ((A 2 + Z₂ - R) / 2 + κ - I * R ^ 2) * y₃ ^ 2 +
        2 * (I * L * R - κ) * y₀ * y₃ -
        (B 0 / 2 - μ₀ - 2 * I * L * g) * y₀ -
        (B 2 / 2 - μ₂ + 2 * I * R * g) * y₃) ≤ normalizedDeficit r U m n q := by
  let A := cutEnergy r m n q
  let B := cutBias r m n q
  let Z₀ := lowerCoeff r m n q
  let Z₂ := upperCoeff r n q
  let Zlong := longCoeff r m n q
  let κ := Zlong / 4
  let t := fun i => oddProbability (frameVector U i)
  let u := -cutEvenOffset U
  let v := |cutImbalance U|
  let y₀ := 1 - oddTilt U 0
  let y₃ := 1 - oddTilt U 3
  let surplus := 2 * lo ^ 2 / (1 - lo ^ 2)
  let H := A 1 + (L + R) / 2
  let K := 2 * A 1 + (1 + surplus) * H
  let C := A 1 + (Z₀ + Z₂) / 2 + (3 * (A 0 + A 2) - B 0 - B 2) / 2
  let g := μ₀ - μ₂
  let I := if K = 0 then 0 else 1 / (4 * K)
  let loss := if K = 0 then |g| else I * g ^ 2
  let p := L * y₀ - R * y₃ - g
  obtain ⟨hA, hB, hZlong⟩ := spectral_coefficients_nonneg hr hm hmn hnq hq1
  change (∀ i, 0 ≤ A i) at hA
  change (∀ i, 0 ≤ B i) at hB
  change 0 ≤ Zlong at hZlong
  have hMiddle : 1 + v ^ 2 + 3 * u ^ 2 + surplus * u ^ 2 ≤
      forwardCutWeight U + reverseCutWeight U := by
    simpa only [u, neg_sq] using middleCutWeight_ge_sqrt_surplus U hlo hlo1 hv
  obtain ⟨hPair₀, hPair₂⟩ := oddPairMass_eq U
  change t 0 + t 1 = 1 + u at hPair₀
  change t 2 + t 3 = 1 - u at hPair₂
  have hCorrection₀ : t 1 * (1 - t 1) - t 0 * (1 - t 0) = -y₀ * u - u ^ 2 := by
    rw [show t 1 = 1 + u - t 0 by linarith only [hPair₀]]
    change _ = -(1 - 2 * t 0) * u - u ^ 2
    ring
  have hCorrection₂ : t 2 * (1 - t 2) - t 3 * (1 - t 3) = y₃ * u - u ^ 2 := by
    rw [show t 2 = 1 - u - t 3 by linarith only [hPair₂]]
    change _ = (1 - 2 * t 3) * u - u ^ 2
    ring
  obtain ⟨hAdj₀, hAdj₂⟩ := adjacentCutWeight_eq U
  change _ = (forwardCutWeight U + reverseCutWeight U) / 2 +
    t 1 * (1 - t 1) - t 0 * (1 - t 0) at hAdj₀
  change _ = (forwardCutWeight U + reverseCutWeight U) / 2 +
    t 2 * (1 - t 2) - t 3 * (1 - t 3) at hAdj₂
  have hSigned₀ : (1 + v ^ 2) / 2 - y₀ * u + (1 + surplus) * u ^ 2 / 2 ≤
      lowerAdjacentCutWeight U := by linarith only [hMiddle, hAdj₀, hCorrection₀]
  have hSigned₂ : (1 + v ^ 2) / 2 + y₃ * u + (1 + surplus) * u ^ 2 / 2 ≤
      upperAdjacentCutWeight U := by linarith only [hMiddle, hAdj₂, hCorrection₂]
  obtain ⟨hLocal₀, hLocal₂⟩ := adjacentCutWeight_ge_local U
  have hLocal₀' : (1 + y₀ ^ 2) / 2 ≤ lowerAdjacentCutWeight U := by
    change (1 + (1 - 2 * t 0) ^ 2) / 2 ≤ _
    change 1 - 2 * t 0 * (1 - t 0) ≤ _ at hLocal₀
    linarith only [hLocal₀]
  have hLocal₂' : (1 + y₃ ^ 2) / 2 ≤ upperAdjacentCutWeight U := by
    change (1 + (1 - 2 * t 3) ^ 2) / 2 ≤ _
    change 1 - 2 * t 3 * (1 - t 3) ≤ _ at hLocal₂
    linarith only [hLocal₂]
  obtain ⟨hSingle₀, hSingle₂⟩ := singletonCutWeight_eq U
  change _ = 3 / 2 + y₀ ^ 2 / 2 at hSingle₀
  change _ = 3 / 2 + y₃ ^ 2 / 2 at hSingle₂
  obtain ⟨hEnd₀, hEnd₂⟩ := endCutCharge_abs_le U
  change |-endCharge U 0| ≤ min ((1 + y₀) / 2) (v + (1 - y₀) / 2 - u) at hEnd₀
  change |endCharge U 3| ≤ min ((1 + y₃) / 2) (v + (1 - y₃) / 2 + u) at hEnd₂
  have hCharge₀ := weighted_charge hEnd₀ hμ₀.1 hμ₀.2
  have hCharge₂ := weighted_charge (R := endCharge U 3) (y := y₃) (v := v) (u := -u)
    (by simpa only [sub_neg_eq_add] using hEnd₂) hμ₂.1 hμ₂.2
  have hCharge₁ : B 1 * (-v) ≤ B 1 * (-cutImbalance U) :=
    mul_le_mul_of_nonneg_left (neg_le_neg (le_abs_self _)) (hB 1)
  have hLong : (y₀ - y₃) ^ 2 / 4 ≤ longCrossing U := by
    have h := (radical_unscaled (odd_mass_mem U 0) (odd_mass_mem U 3)).trans
      (singletonPairWeight_ge_radical U 0 3)
    unfold y₀ y₃ oddTilt longCrossing sym
    linarith only [h]
  have hPhysical : C + (H * v ^ 2 - (B 1 + μ₀ + μ₂) * v) +
      (K * u ^ 2 - p * u) + (A 0 + Z₀ - L) / 2 * y₀ ^ 2 +
      (A 2 + Z₂ - R) / 2 * y₃ ^ 2 + κ * (y₀ - y₃) ^ 2 -
      (B 0 / 2 - μ₀) * y₀ - (B 2 / 2 - μ₂) * y₃ ≤ retainedCost U A B Z₀ Z₂ Zlong := by
    unfold C K H p g κ retainedCost
    linarith only [mul_le_mul_of_nonneg_left hSingle₀.ge (hA 0),
      mul_le_mul_of_nonneg_left hMiddle (hA 1), mul_le_mul_of_nonneg_left hSingle₂.ge (hA 2),
      mul_le_mul_of_nonneg_left hSigned₀ hL.1, mul_le_mul_of_nonneg_left hSigned₂ hR.1,
      mul_le_mul_of_nonneg_left hLocal₀' (sub_nonneg.mpr hL.2),
      mul_le_mul_of_nonneg_left hLocal₂' (sub_nonneg.mpr hR.2),
      hCharge₀, hCharge₁, hCharge₂, mul_le_mul_of_nonneg_left hLong hZlong]
  have hSurplus : 0 ≤ surplus := by
    have hden := mul_pos (sub_pos.mpr hlo1) (show 0 < 1 + lo by linarith only [hlo])
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg lo)) (by nlinarith only [hden])
  have hH : 0 ≤ H := by
    exact add_nonneg (hA 1) (div_nonneg (add_nonneg hL.1 hR.1) (by norm_num))
  have hHK : H ≤ K := by
    unfold K
    linarith only [hA 1, mul_nonneg hSurplus hH]
  have hEliminate : -loss - I * (p ^ 2 - g ^ 2) ≤ K * u ^ 2 - p * u := by
    by_cases hzero : K = 0
    · have hHzero : H = 0 := le_antisymm (hHK.trans_eq hzero) hH
      have hLzero : L = 0 := by
        unfold H at hHzero
        linarith only [hHzero, hA 1, hL.1, hR.1]
      have hRzero : R = 0 := by
        unfold H at hHzero
        linarith only [hHzero, hA 1, hL.1, hR.1]
      have hu : |u| ≤ 1 := by
        have h : |u| + v ≤ 1 := by
          simpa only [u, v, abs_neg] using abs_cutEvenOffset_add_abs_cutImbalance_le_one U
        have hv₀ : 0 ≤ v := abs_nonneg _
        linarith only [h, hv₀]
      have hProduct : -|g| ≤ g * u := calc
        -|g| = -(|g| * 1) := by rw [mul_one]
        _ ≤ -|g * u| := by
          rw [abs_mul]
          exact neg_le_neg (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
        _ ≤ g * u := neg_abs_le _
      simpa [loss, I, hzero, p, hLzero, hRzero] using hProduct
    · have hSquare : 0 ≤ K * (u - p / (2 * K)) ^ 2 :=
        mul_nonneg (hH.trans hHK) (sq_nonneg _)
      have hIdentity : K * (u - p / (2 * K)) ^ 2 = K * u ^ 2 - p * u + I * p ^ 2 := by
        simp only [I, ite_eq_right hzero]
        field_simp [hzero]
        ring
      rw [hIdentity] at hSquare
      simp only [loss, ite_eq_right hzero]
      linarith only [hSquare]
  change thermalCenter r m n q + (C - loss + (H * v ^ 2 - (B 1 + μ₀ + μ₂) * v) +
      ((A 0 + Z₀ - L) / 2 + κ - I * L ^ 2) * y₀ ^ 2 +
      ((A 2 + Z₂ - R) / 2 + κ - I * R ^ 2) * y₃ ^ 2 +
      2 * (I * L * R - κ) * y₀ * y₃ - (B 0 / 2 - μ₀ - 2 * I * L * g) * y₀ -
      (B 2 / 2 - μ₂ + 2 * I * R * g) * y₃) ≤ _
  refine (add_le_add (le_refl _) ?_).trans (centered_retained_le U hr hm hmn hnq hq1)
  unfold p at hEliminate hPhysical
  linarith only [hEliminate, hPhysical]


/-- The exact imbalance contribution on a closed slice in the Wu (3.54) replay.
When the quadratic weight is zero, the penalty selects an endpoint. -/
def imbalanceSliceMin (weight penalty lo hi : ℝ) : ℝ :=
  if penalty ≤ 2 * weight * lo then weight * lo ^ 2 - penalty * lo
  else if 2 * weight * hi ≤ penalty then weight * hi ^ 2 - penalty * hi
  else -(penalty ^ 2) / (4 * weight)

/-- The clipped vertex gives the attained minimum of the replay's imbalance
polynomial, including a signed penalty and a vanishing quadratic weight. -/
theorem imbalanceSliceMin_isLeast {weight penalty lo hi : ℝ}
    (hweight : 0 ≤ weight) (hinterval : lo ≤ hi) :
    IsLeast ((fun v : ℝ => weight * v ^ 2 - penalty * v) '' Set.Icc lo hi)
      (imbalanceSliceMin weight penalty lo hi) := by
  unfold imbalanceSliceMin
  by_cases hleft : penalty ≤ 2 * weight * lo
  · rw [ite_eq_left hleft]
    refine ⟨⟨lo, ⟨le_rfl, hinterval⟩, rfl⟩, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have h₁ : 0 ≤ v - lo := sub_nonneg.mpr hv.1
    have h₂ : 0 ≤ weight * (v - lo) + (2 * weight * lo - penalty) :=
      add_nonneg (mul_nonneg hweight h₁) (sub_nonneg.mpr hleft)
    linarith only [mul_nonneg h₁ h₂]
  · rw [ite_eq_right hleft]
    by_cases hright : 2 * weight * hi ≤ penalty
    · rw [ite_eq_left hright]
      refine ⟨⟨hi, ⟨hinterval, le_rfl⟩, rfl⟩, ?_⟩
      rintro _ ⟨v, hv, rfl⟩
      have h₁ : 0 ≤ hi - v := sub_nonneg.mpr hv.2
      have h₂ : 0 ≤ weight * (hi - v) + (penalty - 2 * weight * hi) :=
        add_nonneg (mul_nonneg hweight h₁) (sub_nonneg.mpr hright)
      linarith only [mul_nonneg h₁ h₂]
    · rw [ite_eq_right hright]
      have hpos : 0 < weight := by
        by_contra! h
        have hzero := le_antisymm h hweight
        rw [hzero] at hleft hright
        linarith only [lt_of_not_ge hleft, lt_of_not_ge hright]
      have hden : 0 < 2 * weight := mul_pos (by norm_num) hpos
      let vertex := penalty / (2 * weight)
      have hvtx : vertex ∈ Set.Icc lo hi :=
        ⟨(le_div_iff₀ hden).2 (by linarith only [lt_of_not_ge hleft]),
          (div_le_iff₀ hden).2 (by linarith only [lt_of_not_ge hright])⟩
      have hsquare (v : ℝ) : weight * v ^ 2 - penalty * v =
          -(penalty ^ 2) / (4 * weight) + weight * (v - vertex) ^ 2 := by
        dsimp only [vertex]
        field_simp [ne_of_gt hpos]
        ring
      refine ⟨⟨vertex, hvtx, ?_⟩, ?_⟩
      · simp only [hsquare vertex, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
      · rintro _ ⟨v, _, rfl⟩
        dsimp only
        rw [hsquare]
        exact le_add_of_nonneg_right (mul_nonneg hweight (sq_nonneg _))

private abbrev unitInterval : Set ℝ := Set.Icc (-1) 1

private theorem mem_unitInterval {x : ℝ} : x ∈ unitInterval ↔ |x| ≤ 1 := abs_le.symm

/-- The minimum on a unit interval, using the better endpoint for negative curvature. -/
def squareEdgeMin (weight penalty : ℝ) : ℝ :=
  if 0 ≤ weight then imbalanceSliceMin weight penalty (-1) 1 else weight - |penalty|

private theorem squareEdgeMin_isLeast (weight penalty : ℝ) :
    IsLeast ((fun t : ℝ => weight * t ^ 2 - penalty * t) '' unitInterval)
      (squareEdgeMin weight penalty) := by
  unfold squareEdgeMin
  split_ifs with hweight
  · exact imbalanceSliceMin_isLeast hweight (by norm_num)
  · refine ⟨?_, ?_⟩
    · by_cases hp : 0 ≤ penalty
      · exact ⟨1, by norm_num [unitInterval], by simp [abs_of_nonneg hp]⟩
      · refine ⟨-1, by norm_num [unitInterval], ?_⟩
        rw [abs_of_neg (lt_of_not_ge hp)]
        ring
    · rintro _ ⟨t, ht, rfl⟩
      have hsquare : t ^ 2 ≤ 1 := by
        linarith only [mul_nonneg (show 0 ≤ 1 + t by linarith only [ht.1])
          (sub_nonneg.mpr ht.2)]
      have hpenalty : penalty * t ≤ |penalty| := calc
        _ ≤ |penalty * t| := le_abs_self _
        _ = |penalty| * |t| := abs_mul _ _
        _ ≤ |penalty| := mul_le_of_le_one_right (abs_nonneg _) (mem_unitInterval.mp ht)
      have hquadratic : weight ≤ weight * t ^ 2 := by
        simpa only [mul_one] using mul_le_mul_of_nonpos_left hsquare (le_of_not_ge hweight)
      exact sub_le_sub hquadratic hpenalty

private def squareQuadratic (a b c p q : ℝ) (x y : ℝ) : ℝ :=
  a * x ^ 2 + b * y ^ 2 + c * x * y - p * x - q * y

/-- The least of the four edge minima for the quadratic on the unit square. -/
def squareBoundaryMin (a b c p q : ℝ) : ℝ :=
  min (min (a + p + squareEdgeMin b (q + c)) (a - p + squareEdgeMin b (q - c)))
      (min (b + q + squareEdgeMin a (p + c)) (b - q + squareEdgeMin a (p - c)))

private theorem squareBoundaryMin_isLeast (a b c p q : ℝ) :
    IsLeast
      (((fun y => squareQuadratic a b c p q (-1) y) '' unitInterval ∪
        (fun y => squareQuadratic a b c p q 1 y) '' unitInterval) ∪
       ((fun x => squareQuadratic a b c p q x (-1)) '' unitInterval ∪
        (fun x => squareQuadratic a b c p q x 1) '' unitInterval))
      (squareBoundaryMin a b c p q) := by
  have shift (offset weight penalty : ℝ) :
      IsLeast ((fun t : ℝ => offset + (weight * t ^ 2 - penalty * t)) '' unitInterval)
        (offset + squareEdgeMin weight penalty) := by
    obtain ⟨⟨t, ht, heq⟩, hmin⟩ := squareEdgeMin_isLeast weight penalty
    refine ⟨⟨t, ht, congrArg (offset + ·) heq⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact add_le_add (le_refl offset) (hmin ⟨s, hs, rfl⟩)
  have left (y : ℝ) :
      a + p + (b * y ^ 2 - (q + c) * y) = squareQuadratic a b c p q (-1) y := by
    unfold squareQuadratic
    ring
  have right (y : ℝ) :
      a - p + (b * y ^ 2 - (q - c) * y) = squareQuadratic a b c p q 1 y := by
    unfold squareQuadratic
    ring
  have bottom (x : ℝ) :
      b + q + (a * x ^ 2 - (p + c) * x) = squareQuadratic a b c p q x (-1) := by
    unfold squareQuadratic
    ring
  have top (x : ℝ) :
      b - q + (a * x ^ 2 - (p - c) * x) = squareQuadratic a b c p q x 1 := by
    unfold squareQuadratic
    ring
  simpa only [squareBoundaryMin, left, right, bottom, top] using
    (((shift (a + p) b (q + c)).union (shift (a - p) b (q - c))).union
      ((shift (b + q) a (p + c)).union (shift (b - q) a (p - c))))

/-- The exact minimum of `a*x² + b*y² + c*x*y - p*x - q*y` on the unit square.
The four edge minima are compared with the feasible positive definite stationary point. -/
def squareSliceMin (a b c p q : ℝ) : ℝ :=
  let det := 4 * a * b - c ^ 2
  let x := (2 * b * p - c * q) / det
  let y := (2 * a * q - c * p) / det
  let edge := squareBoundaryMin a b c p q
  if 0 < a ∧ 0 < det ∧ |x| ≤ 1 ∧ |y| ≤ 1 then min edge (-(p * x + q * y) / 2)
  else edge

private theorem squareQuadratic_at_stationary {a b c p q x y : ℝ}
    (hx : 2 * a * x + c * y - p = 0) (hy : 2 * b * y + c * x - q = 0) :
    squareQuadratic a b c p q x y = -(p * x + q * y) / 2 := by
  unfold squareQuadratic
  linear_combination (x / 2) * hx + (y / 2) * hy

/-- An affine ray with positive second component reaches the square boundary. -/
private theorem square_ray_reaches_boundary {x y u v : ℝ}
    (hx : x ∈ unitInterval) (hy : y ∈ unitInterval) (hv : 0 < v) :
    ∃ t : ℝ, max |x + t * u| |y + t * v| = 1 := by
  let stop := (1 - y) / v
  let radius := fun t : ℝ => max |x + t * u| |y + t * v|
  have hstop : 0 ≤ stop := div_nonneg (sub_nonneg.mpr hy.2) hv.le
  have hzero : radius 0 ≤ 1 := by
    simpa [radius] using max_le (mem_unitInterval.mp hx) (mem_unitInterval.mp hy)
  have hend : 1 ≤ radius stop := by
    have h : y + stop * v = 1 := by
      dsimp only [stop]
      rw [div_mul_cancel₀ _ hv.ne']
      ring
    simp [radius, h]
  have hcont : Continuous radius := by
    dsimp [radius]
    fun_prop
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hstop hcont.continuousOn
    (show 1 ∈ Set.Icc (radius 0) (radius stop) from ⟨hzero, hend⟩)
  exact ⟨t, ht⟩

/-- The scalar formula attains its value and bounds the polynomial from below
for all real coefficients, including indefinite and singular Hessians. -/
theorem squareSliceMin_isLeast (a b c p q : ℝ) :
    IsLeast ((fun xy : ℝ × ℝ => a * xy.1 ^ 2 + b * xy.2 ^ 2 +
      c * xy.1 * xy.2 - p * xy.1 - q * xy.2) ''
      (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1))
      (squareSliceMin a b c p q) := by
  let f := squareQuadratic a b c p q
  let F := fun xy : ℝ × ℝ => f xy.1 xy.2
  let box := unitInterval ×ˢ unitInterval
  change IsLeast (F '' box) _
  let det := 4 * a * b - c ^ 2
  let sx := (2 * b * p - c * q) / det
  let sy := (2 * a * q - c * p) / det
  let edge := squareBoundaryMin a b c p q
  let stationary := -(p * sx + q * sy) / 2
  let feasible := 0 < a ∧ 0 < det ∧ |sx| ≤ 1 ∧ |sy| ≤ 1
  have hedge := squareBoundaryMin_isLeast a b c p q
  change IsLeast _ edge at hedge
  have hedge_mem : edge ∈ F '' box := by
    rcases hedge.1 with (⟨t, ht, he⟩ | ⟨t, ht, he⟩) | (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
    · exact ⟨(-1, t), ⟨by norm_num [unitInterval], ht⟩, he⟩
    · exact ⟨(1, t), ⟨by norm_num [unitInterval], ht⟩, he⟩
    · exact ⟨(t, -1), ⟨ht, by norm_num [unitInterval]⟩, he⟩
    · exact ⟨(t, 1), ⟨ht, by norm_num [unitInterval]⟩, he⟩
  have hle_edge : squareSliceMin a b c p q ≤ edge := by
    change (if feasible then min edge stationary else edge) ≤ edge
    split_ifs
    · exact min_le_left _ _
    · exact le_rfl
  have hboundary (x y : ℝ) (h : max |x| |y| = 1) : squareSliceMin a b c p q ≤ f x y := by
    have hx : x ∈ unitInterval := mem_unitInterval.mpr ((le_max_left _ _).trans_eq h)
    have hy : y ∈ unitInterval := mem_unitInterval.mpr ((le_max_right _ _).trans_eq h)
    apply hle_edge.trans
    rcases max_choice |x| |y| with hleft | hright
    · have hx' : |x| = 1 := hleft.symm.trans h
      rcases abs_choice x with hpos | hneg
      · rw [show x = 1 by linarith only [hx', hpos]]
        exact hedge.2 (Or.inl (Or.inr ⟨y, hy, rfl⟩))
      · rw [show x = -1 by linarith only [hx', hneg]]
        exact hedge.2 (Or.inl (Or.inl ⟨y, hy, rfl⟩))
    · have hy' : |y| = 1 := hright.symm.trans h
      rcases abs_choice y with hpos | hneg
      · rw [show y = 1 by linarith only [hy', hpos]]
        exact hedge.2 (Or.inr (Or.inr ⟨x, hx, rfl⟩))
      · rw [show y = -1 by linarith only [hy', hneg]]
        exact hedge.2 (Or.inr (Or.inl ⟨x, hx, rfl⟩))
  refine ⟨?_, ?_⟩
  · change (if feasible then min edge stationary else edge) ∈ F '' box
    split_ifs with h
    · rcases min_choice edge stationary with he | hs
      · rw [he]
        exact hedge_mem
      · rw [hs]
        have hdet : det ≠ 0 := h.2.1.ne'
        refine ⟨(sx, sy), ⟨mem_unitInterval.mpr h.2.2.1, mem_unitInterval.mpr h.2.2.2⟩, ?_⟩
        change f sx sy = _
        apply squareQuadratic_at_stationary
        · dsimp only [sx, sy]
          field_simp [hdet]
          dsimp only [det]
          ring
        · dsimp only [sx, sy]
          field_simp [hdet]
          dsimp only [det]
          ring
    · exact hedge_mem
  · have hcompact : IsCompact box := isCompact_Icc.prod isCompact_Icc
    have hnonempty : box.Nonempty := ⟨(0, 0), by norm_num [box, unitInterval]⟩
    have hcont : Continuous F := by
      dsimp [F, f, squareQuadratic]
      fun_prop
    obtain ⟨⟨x, y⟩, hxy, hmin⟩ := hcompact.exists_isMinOn hnonempty hcont.continuousOn
    obtain ⟨hx, hy⟩ : x ∈ unitInterval ∧ y ∈ unitInterval := hxy
    rintro _ ⟨z, hz, rfl⟩
    refine le_trans ?_ (hmin hz)
    change squareSliceMin a b c p q ≤ f x y
    by_cases hbd : max |x| |y| = 1
    · exact hboundary x y hbd
    have hinterior := lt_of_le_of_ne
      (max_le (mem_unitInterval.mp hx) (mem_unitInterval.mp hy)) hbd
    have hx' := abs_lt.mp ((le_max_left |x| |y|).trans_lt hinterior)
    have hy' := abs_lt.mp ((le_max_right |x| |y|).trans_lt hinterior)
    have hlocal := hmin.isLocalMin (prod_mem_nhds
      (Icc_mem_nhds hx'.1 hx'.2) (Icc_mem_nhds hy'.1 hy'.2))
    -- Restrict the polynomial at the interior minimizer to an arbitrary line.
    have hline (u v : ℝ) :
        (2 * a * x + c * y - p) * u + (2 * b * y + c * x - q) * v = 0 ∧
          0 ≤ a * u ^ 2 + b * v ^ 2 + c * u * v := by
      let line := fun t : ℝ => (x + t * u, y + t * v)
      let curvature := a * u ^ 2 + b * v ^ 2 + c * u * v
      let slope := (2 * a * x + c * y - p) * u + (2 * b * y + c * x - q) * v
      have heq : F ∘ line = fun t => curvature * t ^ 2 + slope * t + f x y := by
        funext t
        dsimp [F, line, f, squareQuadratic, curvature, slope]
        ring
      have hcontLine : Continuous line := by
        dsimp [line]
        fun_prop
      have hlocalLine : IsLocalMin (F ∘ line) 0 := by
        apply IsLocalMin.comp_continuous _ hcontLine.continuousAt
        simpa [line] using hlocal
      rw [heq] at hlocalLine
      have hderiv : HasDerivAt (fun t : ℝ => curvature * t ^ 2 + slope * t + f x y) slope 0 := by
        simpa using (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul curvature |>.add
          ((hasDerivAt_id (0 : ℝ)).const_mul slope)).add_const (f x y)
      have hslope := hlocalLine.hasDerivAt_eq_zero hderiv
      refine ⟨hslope, ?_⟩
      have hevent : ∀ᶠ t in nhds (0 : ℝ), f x y ≤ curvature * t ^ 2 + f x y := by
        simpa [IsLocalMin, IsMinFilter, hslope] using hlocalLine
      obtain ⟨l, r, hzero, hnear⟩ := hevent.exists_Ioo_subset
      obtain ⟨t, ht, htr⟩ := exists_between hzero.2
      have hstep := hnear (show t ∈ Set.Ioo l r from ⟨hzero.1.trans ht, htr⟩)
      change f x y ≤ curvature * t ^ 2 + f x y at hstep
      exact nonneg_of_mul_nonneg_left (show 0 ≤ curvature * t ^ 2 by linarith only [hstep])
        (sq_pos_of_pos ht)
    have hdx : 2 * a * x + c * y - p = 0 := by simpa using (hline 1 0).1
    have hdy : 2 * b * y + c * x - q = 0 := by simpa using (hline 0 1).1
    have ha : 0 ≤ a := by simpa using (hline 1 0).2
    by_cases hpos : 0 < a
    · have hdir := (hline (-c) (2 * a)).2
      have hfactor : 0 ≤ a * det := by
        dsimp only [det]
        linarith only [hdir]
      have hdet : 0 ≤ det := nonneg_of_mul_nonneg_right hfactor hpos
      by_cases hdetpos : 0 < det
      · have hsx : sx = x := by
          apply (div_eq_iff hdetpos.ne').2
          dsimp only [det]
          linear_combination -(2 * b) * hdx + c * hdy
        have hsy : sy = y := by
          apply (div_eq_iff hdetpos.ne').2
          dsimp only [det]
          linear_combination -(2 * a) * hdy + c * hdx
        have hfeasible : feasible := ⟨hpos, hdetpos, hsx ▸ mem_unitInterval.mp hx,
          hsy ▸ mem_unitInterval.mp hy⟩
        change (if feasible then min edge stationary else edge) ≤ f x y
        rw [ite_eq_left hfeasible]
        change min edge stationary ≤ squareQuadratic a b c p q x y
        rw [squareQuadratic_at_stationary hdx hdy]
        simpa only [stationary, hsx, hsy] using min_le_right edge stationary
      · have hdetzero : det = 0 := le_antisymm (le_of_not_gt hdetpos) hdet
        have hzero : a * (-c) ^ 2 + b * (2 * a) ^ 2 + c * (-c) * (2 * a) = 0 := by
          dsimp only [det] at hdetzero
          linear_combination a * hdetzero
        obtain ⟨t, ht⟩ := square_ray_reaches_boundary hx hy (show 0 < 2 * a by positivity)
          (u := -c)
        have hflat : f (x + t * (-c)) (y + t * (2 * a)) = f x y := by
          dsimp only [f, squareQuadratic]
          linear_combination (t * (-c)) * hdx + (t * (2 * a)) * hdy + t ^ 2 * hzero
        exact (hboundary _ _ ht).trans_eq hflat
    · have hazero := le_antisymm (le_of_not_gt hpos) ha
      have hcross : c = 0 := by
        have h := (hline (-(b + 1) / c) 1).2
        by_contra hc
        rw [hazero] at h
        have heq : c * (-(b + 1) / c) = -(b + 1) := by field_simp
        simp only [zero_mul, one_pow, zero_add, mul_one, heq] at h
        linarith only [h]
      have hp : p = 0 := by simpa [hazero, hcross] using hdx
      have hflat : f 1 y = f x y := by simp [f, squareQuadratic, hazero, hcross, hp]
      have hbd' : max |(1 : ℝ)| |y| = 1 := by
        simpa only [abs_one] using max_eq_left (mem_unitInterval.mp hy)
      exact (hboundary 1 y hbd').trans_eq hflat

/-- Substitute both attained scalar minima into the ordinary-trace bound of
Wu (3.54). At `m = 2 / 3` this gives the sliced bound in the boundary certificate. -/
theorem sharp_slice_min_le_normalizedDeficit {r m n q lo hi L R μ₀ μ₂ : ℝ} (U : unitary Mat)
    (hr : 1 ≤ r) (hm : 0 ≤ m) (hmn : m ≤ n) (hnq : n ≤ q) (hq1 : q ≤ 1)
    (hlo : 0 ≤ lo) (hlo1 : lo < 1) (hv : |cutImbalance U| ∈ Set.Icc lo hi)
    (hL : L ∈ Set.Icc 0 (lowerCoeff r m n q)) (hR : R ∈ Set.Icc 0 (upperCoeff r n q))
    (hμ₀ : μ₀ ∈ Set.Icc 0 (cutBias r m n q 0)) (hμ₂ : μ₂ ∈ Set.Icc 0 (cutBias r m n q 2)) :
    let A := cutEnergy r m n q
    let B := cutBias r m n q
    let Z₀ := lowerCoeff r m n q
    let Z₂ := upperCoeff r n q
    let κ := longCoeff r m n q / 4
    let surplus := 2 * lo ^ 2 / (1 - lo ^ 2)
    let H := A 1 + (L + R) / 2
    let K := 2 * A 1 + (1 + surplus) * H
    let C := A 1 + (Z₀ + Z₂) / 2 + (3 * (A 0 + A 2) - B 0 - B 2) / 2
    let g := μ₀ - μ₂
    let I := if K = 0 then 0 else 1 / (4 * K)
    let loss := if K = 0 then |g| else I * g ^ 2
    thermalCenter r m n q +
      (C - loss + imbalanceSliceMin H (B 1 + μ₀ + μ₂) lo hi +
        squareSliceMin ((A 0 + Z₀ - L) / 2 + κ - I * L ^ 2)
          ((A 2 + Z₂ - R) / 2 + κ - I * R ^ 2)
          (2 * (I * L * R - κ)) (B 0 / 2 - μ₀ - 2 * I * L * g)
          (B 2 / 2 - μ₂ + 2 * I * R * g)) ≤ normalizedDeficit r U m n q := by
  let H := cutEnergy r m n q 1 + (L + R) / 2
  let penalty := cutBias r m n q 1 + μ₀ + μ₂
  obtain ⟨hA, _, _⟩ := spectral_coefficients_nonneg hr hm hmn hnq hq1
  have hH : 0 ≤ H :=
    add_nonneg (hA 1) (div_nonneg (add_nonneg hL.1 hR.1) (by norm_num))
  have hmin : imbalanceSliceMin H penalty lo hi ≤
      H * |cutImbalance U| ^ 2 - penalty * |cutImbalance U| :=
    (imbalanceSliceMin_isLeast hH (hv.1.trans hv.2)).2 ⟨|cutImbalance U|, hv, rfl⟩
  have hsharp := sharp_slice_le_normalizedDeficit U hr hm hmn hnq hq1 hlo hlo1 hv.1
    hL hR hμ₀ hμ₂
  have htilt (i : Fin 4) : 1 - oddTilt U i ∈ unitInterval := by
    have hi := odd_mass_mem U i
    constructor <;> unfold oddTilt <;> linarith only [hi.1, hi.2]
  let A := cutEnergy r m n q
  let B := cutBias r m n q
  let K := 2 * A 1 + (1 + 2 * lo ^ 2 / (1 - lo ^ 2)) * H
  let I := if K = 0 then 0 else 1 / (4 * K)
  let g := μ₀ - μ₂
  let κ := longCoeff r m n q / 4
  have hsquare := (squareSliceMin_isLeast
    ((A 0 + lowerCoeff r m n q - L) / 2 + κ - I * L ^ 2)
    ((A 2 + upperCoeff r n q - R) / 2 + κ - I * R ^ 2)
    (2 * (I * L * R - κ)) (B 0 / 2 - μ₀ - 2 * I * L * g)
    (B 2 / 2 - μ₂ + 2 * I * R * g)).2
    ⟨(1 - oddTilt U 0, 1 - oddTilt U 3), ⟨htilt 0, htilt 3⟩, rfl⟩
  dsimp only at hsharp ⊢
  dsimp only [H, penalty] at hmin
  dsimp only [A, B, κ, I, K, H, g] at hsquare
  linarith only [hsharp, hmin, hsquare]

end D5.S3.Quantum.Semigroups.WuCubicSharpAngularSlice
