/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortJointLower
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Taylor models of the short-gap joint and marginal quadratures. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMarginalQuadratureParameter
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortJointCore
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.HalfGapSlope
import D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth
import Batteries.Tactic.OpenPrivate

/-! Taylor enclosures of the reflected joint quadrature and the three marginal inputs. -/

namespace RefinedBMV.PositiveCenter

open scoped BigOperators

noncomputable section

open private quadratureTailTerm from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMarginalQuadrature
open private marginalQuadratureWeight marginalQuadratureWeight_abs_le marginalQuadratureCoefficient
  compactClosedQuadrature_parameter_series compactClosedQuadrature_monomial_abs_le_geometric
  summable_factorial_quadrature_series from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMarginalQuadratureParameter
open private coeffAdd coeffScale coeffSum horner_add horner_scale horner_sum
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial
open private rationalHorner abs_momentHorner_le from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.HalfGapSlope

open SmallCorner (momentHorner)

/-- The finite parameter-series coefficient for closed quadrature of a weighted
exponential density, before translation to the center of the parameter interval. -/
def compactClosedQuadratureSeriesCoeff (h : ℝ) (degree : ℕ) (weight : ℕ → ℝ) (n : ℕ) : ℝ :=
  weight n / (n.factorial : ℝ) * compactClosedQuadrature h (fun x ↦ x ^ (n + degree))

/-- A centered polynomial enclosure for a closed quadrature. Its two error bounds
control the infinite tail and the discarded terms of the translated polynomial. -/
theorem compactClosedQuadrature_shiftedSeries_sound
    {s t z h C center offset radius width : ℝ} {degree terms order : ℕ}
    {X : CompactTaylorModel.Model} (hb : CompactTaylorModel.InBox s t z)
    (hx : X.Encloses s t z offset) (hh : 0 ≤ h)
    (horder : order ≤ terms) (hterms : 3 ≤ terms)
    (hr : |center| + |offset| ≤ radius) (hratio : 2 * radius < (terms : ℝ) - 2)
    (hw : |offset| ≤ width) {weight : ℕ → ℝ} (hweight : ∀ n, |weight n| ≤ C)
    (models : ℕ → CompactTaylorModel.Model)
    (hmodels : ∀ m < order, (models m).Encloses s t z
      (CompactTaylorModel.shiftedSeriesCoeff
        (compactClosedQuadratureSeriesCoeff h degree weight) terms center m))
    {shiftError tailError : ℚ}
    (hshift : width ^ order * ∑ n ∈ Finset.Ico order terms,
        |compactClosedQuadratureSeriesCoeff h degree weight n| *
          (n.choose order : ℝ) * radius ^ (n - order) ≤ (shiftError : ℝ))
    (htail : C * ((3 + h) * quadratureTailTerm degree 0 radius terms +
        h ^ 2 / 6 * quadratureTailTerm degree 1 radius terms +
        h ^ 4 / 360 * quadratureTailTerm degree 3 radius terms) /
        (1 - 2 * radius / ((terms : ℝ) - 2)) ≤ (tailError : ℝ)) :
    (((CompactTaylorModel.Model.series order models X).widen shiftError).widen tailError).Encloses
      s t z (compactClosedQuadrature h (fun x ↦ ∑' n : ℕ,
        (weight n * ((center + offset) ^ n / n.factorial)) * x ^ (n + degree))) := by
  have hseries := CompactTaylorModel.Model.shiftedSeries_sound hb hx horder hr hw
    (compactClosedQuadratureSeriesCoeff h degree weight) models hmodels hshift
  apply CompactTaylorModel.Model.widen_sound hseries
  have habs : |center + offset| ≤ radius := (abs_add_le _ _).trans hr
  have herror := compactClosedQuadrature_taylor_error_le
    (offset := degree) hh habs hterms hratio hweight
  have heq (n : ℕ) :
      weight n * ((center + offset) ^ n / (n.factorial : ℝ)) *
        compactClosedQuadrature h (fun x ↦ x ^ (n + degree)) =
      compactClosedQuadratureSeriesCoeff h degree weight n * (center + offset) ^ n := by
    simp only [compactClosedQuadratureSeriesCoeff, div_eq_mul_inv]
    ring
  simpa only [heq] using herror.trans htail

/-- Multiply an ascending spacing row by a power of the spacing. -/
private def spacingMonomialMul (degree : ℕ) (row : List ℚ) : List ℚ :=
  List.replicate degree 0 ++ row

private theorem spacingMonomialMul_eval (h : ℝ) (degree : ℕ) (row : List ℚ) :
    momentHorner h (spacingMonomialMul degree row) = h ^ degree * momentHorner h row := by
  induction degree with
  | zero => simp [spacingMonomialMul]
  | succ degree ih =>
      simp only [spacingMonomialMul, List.replicate_succ, List.cons_append, momentHorner,
        Rat.cast_zero, zero_add] at ih ⊢
      rw [ih, pow_succ']
      ring

/-- A density entry records the degree in the integration variable, the degree in
the spacing and a rational scalar. These rows are evaluated before the Taylor model. -/
private def quadratureDensityRow (offset : ℕ) : List (ℕ × ℕ × ℚ) → List ℚ
  | [] => []
  | (power, spacingPower, scalar) :: terms =>
      let monomial := List.ofFn (compactQuadratureMonomialCoefficients (offset + power))
      coeffAdd (coeffScale scalar (spacingMonomialMul spacingPower monomial))
        (quadratureDensityRow offset terms)

private theorem quadratureDensityRow_eval (h : ℝ) (offset : ℕ)
    (density : List (ℕ × ℕ × ℚ)) :
    momentHorner h (quadratureDensityRow offset density) =
      (density.map fun (power, spacingPower, scalar) =>
        (scalar : ℝ) * h ^ spacingPower *
          compactClosedQuadrature h (fun x ↦ x ^ (offset + power))).sum := by
  induction density with
  | nil => rfl
  | cons item density ih =>
      rcases item with ⟨power, spacingPower, scalar⟩
      have hrow :
          momentHorner h (List.ofFn (compactQuadratureMonomialCoefficients (offset + power))) =
            compactClosedQuadrature h (fun x ↦ x ^ (offset + power)) := by
        rw [compactClosedQuadrature_monomial]
        simp only [List.ofFn_succ, List.ofFn_zero,
          Fin.sum_univ_succ, Fin.sum_univ_zero,
          momentHorner, Fin.val_zero, Fin.val_succ, pow_zero]
        ring
      simp only [quadratureDensityRow, horner_add, horner_scale, spacingMonomialMul_eval, hrow,
        List.map_cons, List.sum_cons, ih]
      ring

/-- Compute a parameter Taylor coefficient as a rational polynomial in the spacing,
with the factorial weight included. -/
private def quadratureParameterRow (density : List (ℕ × ℕ × ℚ)) (offset : ℕ)
    (weight : ℕ → ℚ) (n : ℕ) : List ℚ :=
  coeffScale (weight n / n.factorial) (quadratureDensityRow (n + offset) density)

/-- First translate a finite parameter series, then evaluate its coefficients in the
spacing. This keeps the arithmetic in the certificate rational until model rounding. -/
def shiftedQuadratureParameterRow (density : List (ℕ × ℕ × ℚ)) (offset terms : ℕ)
    (weight : ℕ → ℚ) (center : ℚ) (m : ℕ) : List ℚ :=
  coeffSum (fun j =>
    let n := m + j
    coeffScale ((n.choose m : ℚ) * center ^ (n - m))
      (quadratureParameterRow density offset weight n)) (terms - m)

theorem shiftedQuadratureParameterRow_eval (h : ℝ) (density : List (ℕ × ℕ × ℚ))
    (offset terms : ℕ) (weight : ℕ → ℚ) (center : ℚ) (m : ℕ) :
    momentHorner h (shiftedQuadratureParameterRow density offset terms weight center m) =
      CompactTaylorModel.shiftedSeriesCoeff (fun n =>
        ((weight n : ℝ) / n.factorial) *
          (density.map fun (power, spacingPower, scalar) =>
            (scalar : ℝ) * h ^ spacingPower *
              compactClosedQuadrature h (fun x ↦ x ^ (n + offset + power))).sum)
        terms center m := by
  rw [shiftedQuadratureParameterRow, horner_sum, CompactTaylorModel.shiftedSeriesCoeff,
    Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [quadratureParameterRow, horner_scale, quadratureDensityRow_eval, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_pow]
  ring

private def marginalDensity : List (ℕ × ℕ × ℚ) := [(0, 0, 2), (0, 1, 1), (1, 0, -1)]

private def marginalWeight (j n : ℕ) : ℚ := 1 / ((((j + n : ℕ) : ℚ) + 1) *
  (((j + n : ℕ) : ℚ) + 2))

private theorem cast_marginalWeight (j n : ℕ) :
    (marginalWeight j n : ℝ) = marginalQuadratureWeight (j + n) := by
  simp only [marginalWeight, marginalQuadratureWeight, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat]

private theorem marginalQuadratureParameterRow_eval (h : ℝ) (j n : ℕ) :
    momentHorner h (quadratureParameterRow marginalDensity (j + 2) (marginalWeight j) n) =
      marginalQuadratureCoefficient h (j + n) / (n.factorial : ℝ) := by
  simp only [quadratureParameterRow, horner_scale, quadratureDensityRow_eval, Rat.cast_div,
    Rat.cast_natCast, cast_marginalWeight, marginalDensity, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, marginalQuadratureCoefficient]
  norm_num [show n + (j + 2) + 0 = j + n + 2 by omega,
    show n + (j + 2) + 1 = j + n + 3 by omega]
  ring

/-- The same three density terms give the scaled marginal and each of its
parameter derivatives. This identifies the exact rational row used in a box. -/
theorem shiftedMarginalQuadratureRow_eval (h : ℝ) (j terms : ℕ) (center : ℚ) (m : ℕ) :
    momentHorner h (shiftedQuadratureParameterRow marginalDensity (j + 2) terms
      (marginalWeight j) center m) =
      CompactTaylorModel.shiftedSeriesCoeff
        (fun n => marginalQuadratureCoefficient h (j + n) / (n.factorial : ℝ))
        terms center m := by
  rw [shiftedQuadratureParameterRow, horner_sum, CompactTaylorModel.shiftedSeriesCoeff,
    Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n _
  simp only [horner_scale, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    marginalQuadratureParameterRow_eval]
  ring

private def shortQuadratureTail (h radius : ℝ) (offset terms : ℕ) : ℝ :=
  ((3 + h) * quadratureTailTerm offset 0 radius terms +
    h ^ 2 / 6 * quadratureTailTerm offset 1 radius terms +
    h ^ 4 / 360 * quadratureTailTerm offset 3 radius terms) /
    (1 - 2 * radius / ((terms : ℝ) - 2))

private theorem marginalClosedQuadrature_tail_le {h t radius : ℝ} {terms : ℕ}
    (hh : 0 ≤ h) (ht : |t| ≤ radius) (hterms : 3 ≤ terms)
    (hr : 2 * radius < (terms : ℝ) - 2) (j : ℕ) :
    |compactClosedQuadrature h
        (fun x ↦ iteratedDeriv j (fun y ↦ regularizedMarginalIntegrand h y x) t) -
      ∑ n ∈ Finset.range terms, (marginalQuadratureCoefficient h (j + n) / n.factorial) *
        t ^ n| ≤ (2 + h) * shortQuadratureTail h radius (j + 2) terms +
      shortQuadratureTail h radius (j + 3) terms := by
  let w (n : ℕ) := marginalQuadratureWeight (j + n)
  let A (offset n : ℕ) := w n * (t ^ n / n.factorial) *
    compactClosedQuadrature h (fun x ↦ x ^ (n + offset))
  have hw (n : ℕ) : |w n| ≤ 1 := marginalQuadratureWeight_abs_le (j + n)
  have hs (offset : ℕ) : Summable (A offset) := by
    let a (n : ℕ) := w n * compactClosedQuadrature h (fun x ↦ x ^ (n + offset))
    have ha (n : ℕ) : |a n| ≤
        ((3 + h + h ^ 2 / 6 + h ^ 4 / 60) * 4 ^ offset) * 4 ^ n := by
      dsimp only [a]
      rw [abs_mul]
      calc
        _ ≤ 1 * ((3 + h + h ^ 2 / 6 + h ^ 4 / 60) * 4 ^ (n + offset)) :=
          mul_le_mul (hw n) (compactClosedQuadrature_monomial_abs_le_geometric hh _)
            (abs_nonneg _) zero_le_one
        _ = _ := by rw [pow_add]; ring
    have he : A offset = fun n ↦ a n * t ^ n / n.factorial := by
      funext n
      dsimp only [A, a]
      ring
    rw [he]
    exact summable_factorial_quadrature_series ha t
  have htail (offset : ℕ) :
      |(∑' n, A offset n) - ∑ n ∈ Finset.range terms, A offset n| ≤
        shortQuadratureTail h radius offset terms := by
    have he := compactClosedQuadrature_taylor_error_le (offset := offset) hh ht hterms hr hw
    have hQ : compactClosedQuadrature h (fun x ↦ ∑' n : ℕ,
        w n * (t ^ n / n.factorial) * x ^ (n + offset)) = ∑' n, A offset n := by
      simpa only [A, mul_div_assoc] using compactClosedQuadrature_tsum h t offset w hw
    dsimp only at he
    rw [hQ] at he
    simpa only [shortQuadratureTail, A, one_mul] using he
  have he (n : ℕ) :
      (marginalQuadratureCoefficient h (j + n) / n.factorial) * t ^ n =
        (2 + h) * A (j + 2) n - A (j + 3) n := by
    simp only [A, w, marginalQuadratureCoefficient,
      show n + (j + 2) = j + n + 2 by omega, show n + (j + 3) = j + n + 3 by omega]
    ring
  rw [compactClosedQuadrature_parameter_series hh]
  simp_rw [show ∀ n : ℕ, marginalQuadratureCoefficient h (j + n) * t ^ n / n.factorial =
    (marginalQuadratureCoefficient h (j + n) / n.factorial) * t ^ n from fun n => by ring, he]
  rw [((hs (j + 2)).mul_left (2 + h)).tsum_sub (hs (j + 3)), tsum_mul_left,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  have he' (a b c d : ℝ) :
      ((2 + h) * a - b) - ((2 + h) * c - d) = (2 + h) * (a - c) - (b - d) := by ring
  rw [he']
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (show 0 ≤ 2 + h by positivity)]
  exact add_le_add (mul_le_mul_of_nonneg_left (htail (j + 2)) (by positivity)) (htail (j + 3))

/-- The rational spacing rows give a centered enclosure of the closed quadrature
for a marginal derivative, including the errors of both Taylor truncations. -/
theorem marginalClosedQuadrature_model_sound
    {s t z h offset : ℝ} {center radius width : ℚ} {j terms order : ℕ}
    {H X : CompactTaylorModel.Model} (hb : CompactTaylorModel.InBox s t z)
    (hH : H.Encloses s t z h) (hX : X.Encloses s t z offset)
    (hh : 0 ≤ h) (horder : order ≤ terms) (hterms : 3 ≤ terms)
    (hr : |(center : ℝ)| + |offset| ≤ radius) (hw : |offset| ≤ (width : ℝ))
    (hratio : 2 * (radius : ℝ) < (terms : ℝ) - 2)
    {shiftError tailError : ℚ}
    (hshift : (width : ℝ) ^ order * ∑ n ∈ Finset.Ico order terms,
        |marginalQuadratureCoefficient h (j + n) / n.factorial| *
          (n.choose order : ℝ) * (radius : ℝ) ^ (n - order) ≤ (shiftError : ℝ))
    (htail : (2 + h) * shortQuadratureTail h radius (j + 2) terms +
        shortQuadratureTail h radius (j + 3) terms ≤ (tailError : ℝ)) :
    (((CompactTaylorModel.Model.series order (fun m =>
      CompactTaylorModel.Model.horner
        (shiftedQuadratureParameterRow marginalDensity (j + 2) terms (marginalWeight j) center m)
        H) X).widen shiftError).widen tailError).Encloses s t z
      (compactClosedQuadrature h (fun x ↦
        iteratedDeriv j (fun y ↦ regularizedMarginalIntegrand h y x) ((center : ℝ) + offset))) := by
  refine CompactTaylorModel.Model.widen_sound
    (CompactTaylorModel.Model.shiftedSeries_sound hb hX horder hr hw
      (fun n => marginalQuadratureCoefficient h (j + n) / n.factorial) _ ?_ hshift) ?_
  · intro m _
    rw [← shiftedMarginalQuadratureRow_eval h j terms center m]
    exact CompactTaylorModel.Model.horner_sound hb hH _
  · exact (marginalClosedQuadrature_tail_le hh
      ((abs_add_le _ _).trans hr) hterms hratio j).trans htail

private def quadratureShiftBound (upper radius width : ℚ) (rows : ℕ → List ℚ)
    (terms order : ℕ) : ℚ :=
  width ^ order * ∑ n ∈ Finset.Ico order terms,
    rationalHorner upper ((rows n).map abs) *
      (n.choose order : ℚ) * radius ^ (n - order)

private theorem quadratureShiftBound_sound {h : ℝ} {upper radius width : ℚ}
    (hh : 0 ≤ h) (hupper : h ≤ upper) (hr : 0 ≤ (radius : ℝ)) (hw : 0 ≤ (width : ℝ))
    {rows : ℕ → List ℚ} {coeff : ℕ → ℝ} (heval : ∀ n, momentHorner h (rows n) = coeff n)
    (terms order : ℕ) :
    (width : ℝ) ^ order * ∑ n ∈ Finset.Ico order terms,
        |coeff n| * (n.choose order : ℝ) * (radius : ℝ) ^ (n - order) ≤
      (quadratureShiftBound upper radius width rows terms order : ℝ) := by
  simp only [quadratureShiftBound, Rat.cast_mul, Rat.cast_sum, Rat.cast_natCast,
    Rat.cast_pow]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hw _)
  apply Finset.sum_le_sum
  intro n _
  rw [← heval]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (abs_momentHorner_le hh hupper _) (Nat.cast_nonneg _)) (pow_nonneg hr _)

private def shortQuadratureTailRat (upper radius : ℚ) (offset terms : ℕ) : ℚ :=
  let b (order : ℕ) : ℚ :=
    ((terms + offset).descFactorial order : ℚ) * 2 ^ (terms + offset - order) *
      radius ^ terms / terms.factorial
  ((3 + upper) * b 0 + upper ^ 2 / 6 * b 1 + upper ^ 4 / 360 * b 3) /
    (1 - 2 * radius / ((terms : ℚ) - 2))

private theorem shortQuadratureTailRat_cast (upper radius : ℚ) (offset terms : ℕ) :
    (shortQuadratureTailRat upper radius offset terms : ℝ) =
      shortQuadratureTail upper radius offset terms := by
  simp only [shortQuadratureTailRat, shortQuadratureTail, quadratureTailTerm, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_one]

private theorem shortQuadratureTail_spacing_mono {h upper radius : ℝ} (hh : 0 ≤ h)
    (hupper : h ≤ upper) (hradius : 0 ≤ radius) {terms : ℕ} (hterms : 3 ≤ terms)
    (hratio : 2 * radius < (terms : ℝ) - 2) (offset : ℕ) :
    shortQuadratureTail h radius offset terms ≤ shortQuadratureTail upper radius offset terms := by
  have hterm : (3 : ℝ) ≤ terms := by exact_mod_cast hterms
  have hdenom : 0 < (terms : ℝ) - 2 := by linarith
  have hpos : 0 ≤ 1 - 2 * radius / ((terms : ℝ) - 2) :=
    sub_nonneg.mpr ((div_lt_one hdenom).mpr hratio).le
  have hb (k : ℕ) : 0 ≤ quadratureTailTerm offset k radius terms := by
    unfold quadratureTailTerm
    positivity
  unfold shortQuadratureTail
  apply div_le_div_of_nonneg_right _ hpos
  gcongr <;> exact hb _

private theorem shortQuadratureTail_nonneg {h radius : ℝ} (hh : 0 ≤ h)
    (hradius : 0 ≤ radius) {terms : ℕ} (hterms : 3 ≤ terms)
    (hratio : 2 * radius < (terms : ℝ) - 2) (offset : ℕ) :
    0 ≤ shortQuadratureTail h radius offset terms := by
  have hterm : (3 : ℝ) ≤ terms := by exact_mod_cast hterms
  have hdenom : 0 < (terms : ℝ) - 2 := by linarith
  have hpos : 0 ≤ 1 - 2 * radius / ((terms : ℝ) - 2) :=
    sub_nonneg.mpr ((div_lt_one hdenom).mpr hratio).le
  unfold shortQuadratureTail quadratureTailTerm
  exact div_nonneg (by positivity) hpos

private def marginalQuadratureTailBound (upper radius : ℚ) (j terms : ℕ) : ℚ :=
  (2 + upper) * shortQuadratureTailRat upper radius (j + 2) terms +
    shortQuadratureTailRat upper radius (j + 3) terms

private theorem marginalQuadratureTailBound_sound {h : ℝ} {upper radius : ℚ} {terms : ℕ}
    (hh : 0 ≤ h) (hupper : h ≤ upper) (hradius : 0 ≤ (radius : ℝ))
    (hterms : 3 ≤ terms) (hratio : 2 * (radius : ℝ) < (terms : ℝ) - 2) (j : ℕ) :
    (2 + h) * shortQuadratureTail h radius (j + 2) terms +
        shortQuadratureTail h radius (j + 3) terms ≤
      (marginalQuadratureTailBound upper radius j terms : ℝ) := by
  simp only [marginalQuadratureTailBound, Rat.cast_add, Rat.cast_ofNat, Rat.cast_mul,
    shortQuadratureTailRat_cast]
  exact add_le_add (mul_le_mul (by linarith : 2 + h ≤ 2 + (upper : ℝ))
    (shortQuadratureTail_spacing_mono hh hupper hradius hterms hratio _)
    (shortQuadratureTail_nonneg hh hradius hterms hratio _) (by linarith))
    (shortQuadratureTail_spacing_mono hh hupper hradius hterms hratio _)

/-- Build the exact model for the closed quadrature used by the short-gap score. -/
def marginalClosedQuadratureModel (upper radius width center : ℚ) (j terms order : ℕ)
    (H X : CompactTaylorModel.Model) : CompactTaylorModel.Model :=
  ((CompactTaylorModel.Model.series order (fun m =>
    CompactTaylorModel.Model.horner
      (shiftedQuadratureParameterRow marginalDensity (j + 2) terms (marginalWeight j) center m)
      H) X).widen (quadratureShiftBound upper radius width
        (quadratureParameterRow marginalDensity (j + 2) (marginalWeight j)) terms order)).widen
        (marginalQuadratureTailBound upper radius j terms)

theorem marginalClosedQuadratureModel_sound
    {s t z h offset : ℝ} {upper center radius width : ℚ} {j terms order : ℕ}
    {H X : CompactTaylorModel.Model} (hb : CompactTaylorModel.InBox s t z)
    (hH : H.Encloses s t z h) (hX : X.Encloses s t z offset)
    (hh : 0 ≤ h) (hupper : h ≤ upper) (horder : order ≤ terms) (hterms : 3 ≤ terms)
    (hr : |(center : ℝ)| + |offset| ≤ radius) (hw : |offset| ≤ (width : ℝ))
    (hratio : 2 * (radius : ℝ) < (terms : ℝ) - 2) :
    (marginalClosedQuadratureModel upper radius width center j terms order H X).Encloses s t z
      (compactClosedQuadrature h (fun x ↦
        iteratedDeriv j (fun y ↦ regularizedMarginalIntegrand h y x) ((center : ℝ) + offset))) := by
  have hradius : 0 ≤ (radius : ℝ) := (by positivity : 0 ≤ |(center : ℝ)| + |offset|).trans hr
  apply marginalClosedQuadrature_model_sound hb hH hX hh horder hterms hr hw hratio
  · exact quadratureShiftBound_sound hh hupper hradius ((abs_nonneg offset).trans hw)
      (marginalQuadratureParameterRow_eval h j) terms order
  · exact marginalQuadratureTailBound_sound hh hupper hradius hterms hratio j

private theorem firstShortMarginalMeshBound {p : ℕ} (hp : 0 < p) {u : ℝ}
    (hu : 0 ≤ u) (hu₄ : u ≤ 4) (hupper : 3 / (p : ℝ) ≤ 3 / 22) :
    let h : ℝ := 3 / (p : ℝ)
    |D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth.meshRemainder (-1) h p
      (fun x ↦ (-u) ^ 3 * Real.exp (-u * x) * ((-u) * (2 + h - x) - 6))| ≤ 1 / 1000 := by
  let h : ℝ := 3 / (p : ℝ)
  let f (x : ℝ) : ℝ := (-u) ^ 3 * Real.exp (-u * x) * ((-u) * (2 + h - x) - 6)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hspan : (-1 : ℝ) + (p : ℝ) * h = 2 := by
    dsimp [h]
    rw [mul_div_cancel₀ _ hpR.ne']
    norm_num
  have hc : Continuous f := by unfold f; fun_prop
  have hexp : Real.exp 4 ≤ 81 := by
    have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one, show (3 : ℝ) ^ 4 = 81 by norm_num]
      using he
  have hf (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 2) : |f x| ≤ 110000 := by
    have hy : 0 ≤ 2 + h - x := by linarith [hx.2]
    have hyu : 2 + h - x ≤ 7 / 2 := by
      change h ≤ (3 / 22 : ℝ) at hupper
      linarith [hx.1]
    have hbracket : |(-u) * (2 + h - x) - 6| ≤ 20 := by
      rw [abs_of_nonpos (by nlinarith [mul_nonneg hu hy])]
      have huweight := mul_le_mul hu₄ hyu hy (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    have hex : Real.exp (-u * x) ≤ 81 := by
      refine (Real.exp_le_exp.mpr ?_).trans hexp
      calc
        _ ≤ (-u) * (-1) := mul_le_mul_of_nonpos_left hx.1 (neg_nonpos.mpr hu)
        _ ≤ 4 := by linarith
    unfold f
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hu,
      abs_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ (4 : ℝ) ^ 3 * 81 * 20 :=
        mul_le_mul (mul_le_mul (pow_le_pow_left₀ hu hu₄ 3) hex (Real.exp_nonneg _)
          (by norm_num)) hbracket (abs_nonneg _) (by positivity)
      _ ≤ _ := by norm_num
  have hi : (∫ x in (-1 : ℝ)..2, |f x|) ≤ (330000 : ℝ) := by
    have hm := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (f := fun x ↦ |f x|)
      (g := fun _ ↦ (110000 : ℝ)) (by norm_num : (-1 : ℝ) ≤ 2)
      (hc.abs.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hf
    norm_num [intervalIntegral.integral_const, smul_eq_mul] at hm
    exact hm
  have hm := D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth.abs_meshRemainder_le
    (a := -1) (n := p) hh hc
  rw [hspan] at hm
  change |D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth.meshRemainder (-1) h p f| ≤ _
  calc
    _ ≤ h ^ 6 / 15360 * (∫ x in (-1 : ℝ)..2, |f x|) := hm
    _ ≤ (3 / 22 : ℝ) ^ 6 / 15360 * 330000 := by
      change h ≤ (3 / 22 : ℝ) at hupper
      have hi₀ : 0 ≤ (∫ x in (-1 : ℝ)..2, |f x|) :=
        intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _)
      exact mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ hh hupper 6) (by norm_num))
        hi hi₀ (by positivity)
    _ ≤ _ := by norm_num

/-- The enclosure for the reflected value at the lower coordinate of the first
short-gap box, on its lower-spacing half. -/
def firstShortNegativeMarginalModel : CompactTaylorModel.Model :=
  (marginalClosedQuadratureModel (3 / 22) 4 (1 / 32) (-127 / 32) 0 55 5
    (CompactTaylorModel.Model.affineCoordinate 2 (3 / 44) (3 / 44))
    (CompactTaylorModel.Model.affineCoordinate 0 0 (-1 / 32))).widen (1 / 1000)

theorem firstShortNegativeMarginalModel_sound {p : ℕ} (hp : 22 ≤ p) {u t : ℝ}
    (hu₀ : 63 / 16 ≤ u) (hu₁ : u ≤ 4) (ht : |t| ≤ 1) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    firstShortNegativeMarginalModel.Encloses (32 * u - 127) t (44 * h / 3 - 1)
      ((J * compactKappa p) * compactZ p (-u)) := by
  let h : ℝ := 3 / (p : ℝ)
  let J := (3 + h) * (3 + 2 * h) / 2
  let s : ℝ := 32 * u - 127
  let z : ℝ := 44 * h / 3 - 1
  let offset : ℝ := (127 : ℝ) / 32 - u
  have hp₀ : 0 < p := by omega
  have hpR : (22 : ℝ) ≤ p := by exact_mod_cast hp
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hupper : h ≤ 3 / 22 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hb : CompactTaylorModel.InBox s t z := by
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, ht, abs_le.mpr ⟨?_, ?_⟩⟩
    · dsimp only [s]; linarith
    · dsimp only [s]; linarith
    · dsimp only [z]; linarith
    · dsimp only [z]; linarith
  have hH : (CompactTaylorModel.Model.affineCoordinate 2 (3 / 44) (3 / 44)).Encloses
      s t z h := by
    convert CompactTaylorModel.Model.affineCoordinate_sound hb 2 (3 / 44) (3 / 44) using 1
    norm_num [z]
    ring
  have hX : (CompactTaylorModel.Model.affineCoordinate 0 0 (-1 / 32)).Encloses s t z offset := by
    convert CompactTaylorModel.Model.affineCoordinate_sound hb 0 0 (-1 / 32) using 1
    norm_num [s, offset]
    ring
  have hw : |offset| ≤ 1 / 32 := by
    apply abs_le.mpr
    dsimp only [offset]
    constructor <;> linarith
  have hQ := marginalClosedQuadratureModel_sound (upper := 3 / 22) (center := -127 / 32)
    (radius := 4) (width := 1 / 32) (j := 0) (terms := 55) (order := 5)
    hb hH hX hh (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hupper) (by decide) (by decide)
    (by norm_num; linarith) (by simpa using hw) (by norm_num)
  have htarg : ((-127 / 32 : ℚ) : ℝ) + offset = -u := by
    norm_num [offset]
    ring
  rw [htarg] at hQ
  change (firstShortNegativeMarginalModel.Encloses s t z
    ((J * compactKappa p) * compactZ p (-u)))
  apply CompactTaylorModel.Model.widen_sound hQ
  have hscaled := (compactScaledMarginal_eq_closed_add_remainder hp₀ (-u)).1
  change (J * compactKappa p) * compactZ p (-u) = _ at hscaled
  rw [hscaled, add_sub_cancel_left]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    firstShortMarginalMeshBound hp₀ (by linarith) hu₁ hupper

/-- The checker's `JOINT_DENSITIES`, in order of the gap powers 0, 2 and 4.
Each entry is (degree in the reflected variable, degree in the spacing, coefficient). -/
def shortJointDensityRow : Fin 3 → List (ℕ × ℕ × ℚ)
  | 0 => [(0, 1, 1), (0, 0, 2), (1, 0, -1)]
  | 1 => [(0, 2, 1 / 6), (1, 2, -1 / 12),
          (0, 1, 1 / 2), (1, 1, -1 / 2), (2, 1, 1 / 8),
          (0, 0, 1 / 3), (1, 0, -1 / 2), (2, 0, 1 / 4), (3, 0, -1 / 24)]
  | 2 => [(0, 4, -1 / 360), (1, 4, 1 / 720),
          (0, 2, 1 / 36), (1, 2, -1 / 24), (2, 2, 1 / 48), (3, 2, -1 / 288),
          (0, 1, 1 / 24), (1, 1, -1 / 12), (2, 1, 1 / 16), (3, 1, -1 / 48),
          (4, 1, 1 / 384),
          (0, 0, 1 / 60), (1, 0, -1 / 24), (2, 0, 1 / 24), (3, 0, -1 / 48),
          (4, 0, 1 / 192), (5, 0, -1 / 1920)]

private def jointDensityEval (density : List (ℕ × ℕ × ℚ)) (h x : ℝ) : ℝ :=
  (density.map fun (power, spacingPower, scalar) ↦
    (scalar : ℝ) * h ^ spacingPower * x ^ power).sum

/-- Evaluate one reflected polynomial density over the reals. -/
def shortJointDensity (i : Fin 3) (h x : ℝ) : ℝ :=
  jointDensityEval (shortJointDensityRow i) h x

/-- The constant term in the gap. -/
theorem shortJointDensity_zero (h x : ℝ) :
    shortJointDensity 0 h x = 2 + h - x := by
  norm_num [shortJointDensity, shortJointDensityRow, jointDensityEval]
  ring

/-- The coefficient of the squared gap in the reflected joint polynomial. -/
theorem shortJointDensity_two (h x : ℝ) :
    shortJointDensity 1 h x = (2 + h - x) * (2 - x) * (2 - x + 2 * h) / 24 := by
  norm_num [shortJointDensity, shortJointDensityRow, jointDensityEval]
  ring

/-- The coefficient of the fourth power of the gap in the reflected joint polynomial. -/
theorem shortJointDensity_four (h x : ℝ) :
    shortJointDensity 2 h x =
      (2 + h - x) * (2 - x) * (2 - x + 2 * h) *
        (3 * (2 - x) ^ 2 + 6 * h * (2 - x) - 4 * h ^ 2) / 5760 := by
  norm_num [shortJointDensity, shortJointDensityRow, jointDensityEval]
  ring

private theorem compactClosedQuadrature_add_const_mul (h c : ℝ) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    compactClosedQuadrature h (fun x ↦ f x + c * g x) =
      compactClosedQuadrature h f + c * compactClosedQuadrature h g := by
  have hderiv (k : ℕ) (x : ℝ) : iteratedDeriv k (fun y ↦ f y + c * g y) x =
      iteratedDeriv k f x + c * iteratedDeriv k g x := by
    rw [iteratedDeriv_fun_add, iteratedDeriv_const_mul_field]
    · exact (hf.of_le le_top).contDiffAt
    · exact (((contDiff_const (c := c)).mul hg).of_le le_top).contDiffAt
  unfold compactClosedQuadrature
  rw [intervalIntegral.integral_add (hf.continuous.intervalIntegrable _ _)
    ((hg.continuous.const_mul c).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, hderiv, hderiv, hderiv, hderiv]
  ring

private theorem jointDensityEval_exp_contDiff (density : List (ℕ × ℕ × ℚ)) (h t : ℝ) :
    ContDiff ℝ ⊤ (fun x ↦ jointDensityEval density h x * Real.exp (t * x)) := by
  induction density with
  | nil =>
      simp only [jointDensityEval, List.map_nil, List.sum_nil, zero_mul]
      exact contDiff_const
  | cons item density ih =>
      rcases item with ⟨power, spacingPower, scalar⟩
      have hsmooth : ContDiff ℝ ⊤ (fun x : ℝ ↦
          (scalar : ℝ) * h ^ spacingPower * (x ^ power * Real.exp (t * x))) := by
        fun_prop
      simpa only [jointDensityEval, List.map_cons, List.sum_cons, add_mul, mul_assoc] using
        hsmooth.add ih

/-- Closed quadrature of a single gap coefficient, with exponential parameter `t`. -/
def shortJointClosedQuadrature (i : Fin 3) (h t : ℝ) : ℝ :=
  compactClosedQuadrature h (fun x ↦ shortJointDensity i h x * Real.exp (t * x))

/-- The joint input of `shortQuadratureNegativeScore` decomposes into the
closed quadratures of the three reflected densities. -/
theorem shortJointFourthQuadrature_eq_density {h : ℝ} (hh : 0 ≤ h) (s d : ℝ) :
    (3 + h) * (3 + 2 * h) / 2 * shortJointFourthQuadrature h s d =
      shortJointClosedQuadrature 0 h (-s) + d ^ 2 * shortJointClosedQuadrature 1 h (-s) +
        d ^ 4 * shortJointClosedQuadrature 2 h (-s) := by
  let f (i : Fin 3) (x : ℝ) := shortJointDensity i h x * Real.exp (-s * x)
  have hsmooth (i : Fin 3) : ContDiff ℝ ⊤ (f i) :=
    jointDensityEval_exp_contDiff (shortJointDensityRow i) h (-s)
  have hpoint : (fun x ↦ (2 + h - x) * shortJointFourthPolynomial h d (2 - x) *
      Real.exp (-s * x)) = fun x ↦ f 0 x + d ^ 2 * (f 1 x + d ^ 2 * f 2 x) := by
    funext x
    simp only [f, shortJointDensity_zero, shortJointDensity_two, shortJointDensity_four,
      shortJointFourthPolynomial]
    ring
  change compactMarginalMeshDenominator h / 2 * shortJointFourthQuadrature h s d = _
  rw [shortJointFourthQuadrature_reflect hh, hpoint,
    compactClosedQuadrature_add_const_mul h _ (hsmooth 0)
      ((hsmooth 1).add (contDiff_const.mul (hsmooth 2))),
    compactClosedQuadrature_add_const_mul h _ (hsmooth 1) (hsmooth 2)]
  change _ = compactClosedQuadrature h (f 0) + d ^ 2 * compactClosedQuadrature h (f 1) +
    d ^ 4 * compactClosedQuadrature h (f 2)
  ring

private def jointDensitySeriesCoeff (density : List (ℕ × ℕ × ℚ)) (h : ℝ) (n : ℕ) : ℝ :=
  (density.map fun (power, spacingPower, scalar) ↦
    (scalar : ℝ) * h ^ spacingPower * compactClosedQuadratureSeriesCoeff h power (fun _ ↦ 1) n).sum

/-- The order-`n` exponential coefficient for the closed quadrature of one density. -/
def shortJointQuadratureSeriesCoeff (i : Fin 3) (h : ℝ) (n : ℕ) : ℝ :=
  jointDensitySeriesCoeff (shortJointDensityRow i) h n

/-- The checker's rational spacing row evaluates to the translated joint coefficient. -/
theorem shiftedShortJointQuadratureRow_eval (i : Fin 3) (h : ℝ) (terms : ℕ)
    (center : ℚ) (m : ℕ) :
    momentHorner h (shiftedQuadratureParameterRow (shortJointDensityRow i) 0 terms
      (fun _ ↦ 1) center m) =
      CompactTaylorModel.shiftedSeriesCoeff (shortJointQuadratureSeriesCoeff i h) terms center m := by
  rw [shiftedQuadratureParameterRow_eval]
  congr 1
  funext n
  unfold shortJointQuadratureSeriesCoeff jointDensitySeriesCoeff
  simp only [Rat.cast_one, add_zero]
  generalize shortJointDensityRow i = density
  induction density with
  | nil => simp
  | cons item density ih =>
      rcases item with ⟨power, spacingPower, scalar⟩
      simp only [List.map_cons, List.sum_cons, mul_add, ih, compactClosedQuadratureSeriesCoeff]
      ring

private theorem closedQuadrature_exp_monomial_tail_le {h t radius : ℝ} {terms : ℕ}
    (hh : 0 ≤ h) (ht : |t| ≤ radius) (hterms : 3 ≤ terms)
    (hratio : 2 * radius < (terms : ℝ) - 2) (power : ℕ) :
    |compactClosedQuadrature h (fun x ↦ x ^ power * Real.exp (t * x)) -
      ∑ n ∈ Finset.range terms, compactClosedQuadratureSeriesCoeff h power (fun _ ↦ 1) n *
        t ^ n| ≤ shortQuadratureTail h radius power terms := by
  have hwt (n : ℕ) : |(1 : ℝ)| ≤ 1 := by simp
  have hpoint : (fun x : ℝ ↦ ∑' n : ℕ, (1 : ℝ) * (t ^ n / n.factorial) *
      x ^ (n + power)) = fun x ↦ x ^ power * Real.exp (t * x) := by
    funext x
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div, ← tsum_mul_left]
    congr 1
    funext n
    rw [mul_pow, pow_add]
    ring
  have herr := compactClosedQuadrature_taylor_error_le (offset := power) hh ht hterms hratio
    (weight := fun _ ↦ 1) hwt
  dsimp only at herr
  rw [hpoint] at herr
  have hcoeff (n : ℕ) : (t ^ n / (n.factorial : ℝ)) *
      compactClosedQuadrature h (fun x ↦ x ^ (n + power)) =
      compactClosedQuadratureSeriesCoeff h power (fun _ ↦ 1) n * t ^ n := by
    unfold compactClosedQuadratureSeriesCoeff
    ring
  simp only [one_mul] at herr
  simpa only [shortQuadratureTail, hcoeff] using herr

private def jointDensityQuadratureTail (density : List (ℕ × ℕ × ℚ))
    (h radius : ℝ) (terms : ℕ) : ℝ :=
  (density.map fun (power, spacingPower, scalar) ↦
    |(scalar : ℝ) * h ^ spacingPower| * shortQuadratureTail h radius power terms).sum

private theorem jointDensityQuadrature_tail_le {h t radius : ℝ} {terms : ℕ}
    (hh : 0 ≤ h) (ht : |t| ≤ radius) (hterms : 3 ≤ terms)
    (hratio : 2 * radius < (terms : ℝ) - 2) (density : List (ℕ × ℕ × ℚ)) :
    |compactClosedQuadrature h (fun x ↦ jointDensityEval density h x * Real.exp (t * x)) -
      ∑ n ∈ Finset.range terms, jointDensitySeriesCoeff density h n * t ^ n| ≤
      jointDensityQuadratureTail density h radius terms := by
  induction density with
  | nil =>
      simp [compactClosedQuadrature, jointDensityEval, jointDensitySeriesCoeff,
        jointDensityQuadratureTail]
  | cons item density ih =>
      rcases item with ⟨power, spacingPower, scalar⟩
      let c : ℝ := (scalar : ℝ) * h ^ spacingPower
      let f (x : ℝ) := jointDensityEval density h x * Real.exp (t * x)
      let g (x : ℝ) := x ^ power * Real.exp (t * x)
      have hpoint : (fun x ↦ jointDensityEval ((power, spacingPower, scalar) :: density) h x *
          Real.exp (t * x)) = fun x ↦ f x + c * g x := by
        funext x
        simp only [jointDensityEval, List.map_cons, List.sum_cons, c, f, g]
        ring
      have hsmooth : ContDiff ℝ ⊤ g := by dsimp only [g]; fun_prop
      rw [hpoint, compactClosedQuadrature_add_const_mul h c
        (jointDensityEval_exp_contDiff density h t) hsmooth]
      have hsum : (∑ n ∈ Finset.range terms,
          jointDensitySeriesCoeff ((power, spacingPower, scalar) :: density) h n * t ^ n) =
          c * (∑ n ∈ Finset.range terms,
            compactClosedQuadratureSeriesCoeff h power (fun _ ↦ 1) n * t ^ n) +
          ∑ n ∈ Finset.range terms, jointDensitySeriesCoeff density h n * t ^ n := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _
        simp only [jointDensitySeriesCoeff, List.map_cons, List.sum_cons, c]
        ring
      rw [hsum]
      have hrearrange (a b C D : ℝ) :
          a + c * b - (c * C + D) = c * (b - C) + (a - D) := by ring
      rw [hrearrange]
      simp only [jointDensityQuadratureTail, List.map_cons, List.sum_cons]
      refine (abs_add_le _ _).trans (add_le_add ?_ ih)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (closedQuadrature_exp_monomial_tail_le hh ht hterms hratio power) (abs_nonneg _)

/-- The tail bound for one joint density, summed over the checker's monomials. -/
def shortJointQuadratureTail (i : Fin 3) (h radius : ℝ) (terms : ℕ) : ℝ :=
  jointDensityQuadratureTail (shortJointDensityRow i) h radius terms

/-- The translated rational rows enclose each joint quadrature when the shift and tail
errors are bounded on the model box. -/
theorem shortJointClosedQuadrature_model_sound
    {s t z h offset : ℝ} {center radius width : ℚ} {terms order : ℕ}
    {H X : CompactTaylorModel.Model} (i : Fin 3)
    (hb : CompactTaylorModel.InBox s t z)
    (hH : H.Encloses s t z h) (hX : X.Encloses s t z offset)
    (hh : 0 ≤ h) (horder : order ≤ terms) (hterms : 3 ≤ terms)
    (hr : |(center : ℝ)| + |offset| ≤ radius) (hw : |offset| ≤ (width : ℝ))
    (hratio : 2 * (radius : ℝ) < (terms : ℝ) - 2)
    {shiftError tailError : ℚ}
    (hshift : (width : ℝ) ^ order * ∑ n ∈ Finset.Ico order terms,
        |shortJointQuadratureSeriesCoeff i h n| * (n.choose order : ℝ) *
          (radius : ℝ) ^ (n - order) ≤ (shiftError : ℝ))
    (htail : shortJointQuadratureTail i h radius terms ≤ (tailError : ℝ)) :
    (((CompactTaylorModel.Model.series order (fun m ↦
      CompactTaylorModel.Model.horner
        (shiftedQuadratureParameterRow (shortJointDensityRow i) 0 terms (fun _ ↦ 1) center m)
        H) X).widen shiftError).widen tailError).Encloses s t z
      (shortJointClosedQuadrature i h ((center : ℝ) + offset)) := by
  refine CompactTaylorModel.Model.widen_sound
    (CompactTaylorModel.Model.shiftedSeries_sound hb hX horder hr hw
      (shortJointQuadratureSeriesCoeff i h) _ ?_ hshift) ?_
  · intro m _
    rw [← shiftedShortJointQuadratureRow_eval i h terms center m]
    exact CompactTaylorModel.Model.horner_sound hb hH _
  · exact (jointDensityQuadrature_tail_le hh ((abs_add_le _ _).trans hr) hterms hratio
      (shortJointDensityRow i)).trans htail

/-- Combine the three component enclosures into the scaled joint input of the score. -/
theorem shortJointFourthQuadrature_model_sound
    {s t z h u v : ℝ} {D Q₀ Q₂ Q₄ : CompactTaylorModel.Model}
    (hb : CompactTaylorModel.InBox s t z) (hh : 0 ≤ h)
    (hD : D.Encloses s t z (v - u))
    (hQ₀ : Q₀.Encloses s t z (shortJointClosedQuadrature 0 h (-((u + v) / 2))))
    (hQ₂ : Q₂.Encloses s t z (shortJointClosedQuadrature 1 h (-((u + v) / 2))))
    (hQ₄ : Q₄.Encloses s t z (shortJointClosedQuadrature 2 h (-((u + v) / 2)))) :
    let D₂ := D.mul D
    (Q₀.add (D₂.mul (Q₂.add (D₂.mul Q₄)))).Encloses s t z
      ((3 + h) * (3 + 2 * h) / 2 * shortJointFourthQuadrature h ((u + v) / 2) (v - u)) := by
  have hD₂ := CompactTaylorModel.Model.mul_sound hb hD hD
  have h := CompactTaylorModel.Model.add_sound hQ₀ (CompactTaylorModel.Model.mul_sound hb hD₂
    (CompactTaylorModel.Model.add_sound hQ₂ (CompactTaylorModel.Model.mul_sound hb hD₂ hQ₄)))
  rw [shortJointFourthQuadrature_eq_density hh]
  convert h using 1
  ring

private theorem shortJointQuadratureParameterRow_eval (i : Fin 3) (h : ℝ) (n : ℕ) :
    momentHorner h (quadratureParameterRow (shortJointDensityRow i) 0 (fun _ ↦ 1) n) =
      shortJointQuadratureSeriesCoeff i h n := by
  simp only [quadratureParameterRow, horner_scale, quadratureDensityRow_eval, one_div,
    Rat.cast_inv, Rat.cast_natCast, Nat.add_zero, shortJointQuadratureSeriesCoeff,
    jointDensitySeriesCoeff, compactClosedQuadratureSeriesCoeff]
  generalize shortJointDensityRow i = density
  induction density with
  | nil => simp
  | cons entry density ih =>
      rcases entry with ⟨power, spacingPower, scalar⟩
      simp only [List.map_cons, List.sum_cons, mul_add, ih]
      ring

private def jointDensityTailBound (density : List (ℕ × ℕ × ℚ)) (upper radius : ℚ)
    (terms : ℕ) : ℚ :=
  (density.map fun (power, spacingPower, scalar) ↦
    |scalar| * upper ^ spacingPower * shortQuadratureTailRat upper radius power terms).sum

private theorem jointDensityTailBound_sound {h : ℝ} {upper radius : ℚ} {terms : ℕ}
    (hh : 0 ≤ h) (hupper : h ≤ upper) (hr : 0 ≤ (radius : ℝ)) (hterms : 3 ≤ terms)
    (hratio : 2 * (radius : ℝ) < (terms : ℝ) - 2) (density : List (ℕ × ℕ × ℚ)) :
    jointDensityQuadratureTail density h radius terms ≤
      (jointDensityTailBound density upper radius terms : ℝ) := by
  induction density with
  | nil => simp [jointDensityQuadratureTail, jointDensityTailBound]
  | cons entry density ih =>
      rcases entry with ⟨power, spacingPower, scalar⟩
      simp only [jointDensityQuadratureTail, jointDensityTailBound, List.map_cons, List.sum_cons,
        Rat.cast_add, Rat.cast_mul, Rat.cast_abs, Rat.cast_pow, shortQuadratureTailRat_cast] at ih ⊢
      apply add_le_add _ ih
      rw [abs_mul, abs_of_nonneg (pow_nonneg hh _)]
      have hU : 0 ≤ (upper : ℝ) := hh.trans hupper
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh hupper _) (abs_nonneg _))
        (shortQuadratureTail_spacing_mono hh hupper hr hterms hratio _)
        (shortQuadratureTail_nonneg hh hr hterms hratio _) (by positivity)

def shortJointClosedQuadratureModel (i : Fin 3) (upper radius width center : ℚ) (terms order : ℕ)
    (H X : CompactTaylorModel.Model) : CompactTaylorModel.Model :=
  ((CompactTaylorModel.Model.series order (fun m ↦
    CompactTaylorModel.Model.horner
      (shiftedQuadratureParameterRow (shortJointDensityRow i) 0 terms (fun _ ↦ 1) center m)
      H) X).widen (quadratureShiftBound upper radius width
        (quadratureParameterRow (shortJointDensityRow i) 0 (fun _ ↦ 1)) terms order)).widen
        (jointDensityTailBound (shortJointDensityRow i) upper radius terms)

theorem shortJointClosedQuadratureModel_sound
    {s t z h offset : ℝ} {upper center radius width : ℚ} {terms order : ℕ}
    {H X : CompactTaylorModel.Model} (i : Fin 3)
    (hb : CompactTaylorModel.InBox s t z)
    (hH : H.Encloses s t z h) (hX : X.Encloses s t z offset)
    (hh : 0 ≤ h) (hupper : h ≤ upper) (horder : order ≤ terms) (hterms : 3 ≤ terms)
    (hr : |(center : ℝ)| + |offset| ≤ radius) (hw : |offset| ≤ (width : ℝ))
    (hratio : 2 * (radius : ℝ) < (terms : ℝ) - 2) :
    (shortJointClosedQuadratureModel i upper radius width center terms order H X).Encloses
      s t z (shortJointClosedQuadrature i h ((center : ℝ) + offset)) := by
  have hradius : 0 ≤ (radius : ℝ) := (by positivity : 0 ≤ |(center : ℝ)| + |offset|).trans hr
  apply shortJointClosedQuadrature_model_sound i hb hH hX hh horder hterms hr hw hratio
  · exact quadratureShiftBound_sound hh hupper hradius ((abs_nonneg offset).trans hw)
      (shortJointQuadratureParameterRow_eval i h) terms order
  · exact jointDensityTailBound_sound hh hupper hradius hterms hratio (shortJointDensityRow i)

end

end RefinedBMV.PositiveCenter
