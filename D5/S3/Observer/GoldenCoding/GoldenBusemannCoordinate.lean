/- GID: D5/S3/Observer/GoldenCoding/GoldenBusemannCoordinate
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenBusemannCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden null coordinates carry a nontrivial Busemann rapidity. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
import D5.S3.Observer.GoldenCoding.GoldenLorentzUpdate

/- Library-search audit trail (2026-09-01):
   * The target atom is residual-open with no formalization receipt and no
     coverage GID. Repository searches for `busemann` and `rapidity` found no
     declaration; body-shape searches found no golden null-basis expansion or
     half-log coefficient ratio.
   * `golden_lorentz_update` is the canonical source for the real form
     `x^2 - x*y - y^2` and its Fibonacci double-update invariance. Its `Q` is a
     theorem-local `let`, so this module imports the theorem and keeps the same
     expression inline rather than introducing a second global definition.
   * The adjacent golden fiber-coordinate modules concern integral Beatty
     readings, while the golden Mobius modules concern projective cross-ratios.
     Neither states the null expansion, rapidity law, or explicit witnesses.
   * Pinned Mathlib supplies `Real.goldenRatio_sq`, `Real.goldenConj_sq`,
     `Real.goldenRatio_add_goldenConj`,
     `Real.goldenRatio_mul_goldenConj`, `Real.log_mul`, and `Real.log_pow`.
     The exact period `goldenScalePeriod = 2 * log goldenRatio` is reused. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenCoding.GoldenBusemannCoordinate

open scoped goldenRatio Matrix
open D5.S1.Scale
open D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
open D5.S3.Observer.GoldenCoding.GoldenLorentzUpdate

/-- The state `a * (goldenRatio, 1) + b * (goldenConj, 1)` in the null basis. -/
def goldenNullCombination (a b : Real) : Fin 2 -> Real :=
  ![a * Real.goldenRatio + b * Real.goldenConj, a + b]

/-- Rapidity on the positive branch, expressed in null-basis coefficients. -/
def goldenRapidity (a b : Real) : Real :=
  (1 / 2 : Real) * Real.log (a / (-b))

/-- The positive-boundary Busemann cocycle is a rapidity difference. -/
def goldenBusemannCocycle
    (sourceA sourceB targetA targetB : Real) : Real :=
  goldenRapidity targetA targetB - goldenRapidity sourceA sourceB

/-- Both golden basis vectors are null for `x^2 - x*y - y^2`. -/
theorem golden_null_basis :
    Real.goldenRatio ^ 2 - Real.goldenRatio - 1 = 0 /\
      Real.goldenConj ^ 2 - Real.goldenConj - 1 = 0 := by
  constructor
  · nlinarith [Real.goldenRatio_sq]
  · nlinarith [Real.goldenConj_sq]

/-- In the golden null basis, the Lorentz form has only the cross term
`-5 * a * b`. -/
theorem golden_lorentz_null_combination (a b : Real) :
    (goldenNullCombination a b 0) ^ 2 -
        goldenNullCombination a b 0 * goldenNullCombination a b 1 -
        (goldenNullCombination a b 1) ^ 2 =
      -5 * a * b := by
  change
    (a * Real.goldenRatio + b * Real.goldenConj) ^ 2 -
        (a * Real.goldenRatio + b * Real.goldenConj) * (a + b) -
        (a + b) ^ 2 =
      -5 * a * b
  calc
    (a * Real.goldenRatio + b * Real.goldenConj) ^ 2 -
          (a * Real.goldenRatio + b * Real.goldenConj) * (a + b) -
          (a + b) ^ 2 =
        a ^ 2 * (Real.goldenRatio ^ 2 - Real.goldenRatio - 1) +
          b ^ 2 * (Real.goldenConj ^ 2 - Real.goldenConj - 1) +
          a * b *
            (2 * (Real.goldenRatio * Real.goldenConj) -
              (Real.goldenRatio + Real.goldenConj) - 2) := by ring
    _ = -5 * a * b := by
      rw [Real.goldenRatio_sq, Real.goldenConj_sq,
        Real.goldenRatio_mul_goldenConj,
        Real.goldenRatio_add_goldenConj]
      ring

/-- The branch inequalities make the logarithm argument strictly positive. -/
theorem golden_rapidity_argument_pos {a b : Real}
    (ha : 0 < a) (hb : b < 0) :
    0 < a / (-b) :=
  div_pos ha (neg_pos.mpr hb)

/-- Unit Lorentz level fixes the product of the two null coefficients. -/
theorem golden_unit_level_coefficient_product {a b : Real}
    (hUnit :
      (goldenNullCombination a b 0) ^ 2 -
          goldenNullCombination a b 0 * goldenNullCombination a b 1 -
          (goldenNullCombination a b 1) ^ 2 = 1) :
    a * (-b) = 1 / 5 := by
  rw [golden_lorentz_null_combination] at hUnit
  norm_num
  nlinarith

/-- On the positive unit branch, rapidity is the explicit logarithmic scale
`log (a * sqrt 5)`. -/
theorem golden_rapidity_on_unit_level {a b : Real}
    (ha : 0 < a) (hb : b < 0)
    (hUnit :
      (goldenNullCombination a b 0) ^ 2 -
          goldenNullCombination a b 0 * goldenNullCombination a b 1 -
          (goldenNullCombination a b 1) ^ 2 = 1) :
    goldenRapidity a b = Real.log (a * Real.sqrt 5) := by
  have hProduct : a * (-b) = 1 / 5 :=
    golden_unit_level_coefficient_product hUnit
  have hSqrtSq : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hNegBNe : -b ≠ 0 := ne_of_gt (neg_pos.mpr hb)
  have hRatio : a / (-b) = (a * Real.sqrt 5) ^ 2 := by
    apply (div_eq_iff hNegBNe).2
    have hFiveProduct : 5 * (a * (-b)) = 1 := by
      norm_num at hProduct
      nlinarith
    calc
      a = a * 1 := by ring
      _ = a * (5 * (a * (-b))) := by rw [hFiveProduct]
      _ = (a * Real.sqrt 5) ^ 2 * (-b) := by
        rw [mul_pow, hSqrtSq]
        ring
  have _hArgumentPositive := golden_rapidity_argument_pos ha hb
  unfold goldenRapidity
  rw [hRatio, Real.log_pow]
  norm_num
  ring

/-- A potential difference satisfies the additive Busemann cocycle law. -/
theorem golden_busemann_cocycle_add
    (a b c d e f : Real) :
    goldenBusemannCocycle a b c d +
        goldenBusemannCocycle c d e f =
      goldenBusemannCocycle a b e f := by
  unfold goldenBusemannCocycle
  ring

/-- Scaling the two null coefficients by reciprocal golden squares preserves
the positive branch and advances rapidity by one golden scale period. -/
theorem golden_rapidity_double_update {a b : Real}
    (ha : 0 < a) (hb : b < 0) :
    0 < Real.goldenRatio ^ 2 * a /\
      (Real.goldenRatio ^ 2)⁻¹ * b < 0 /\
      goldenRapidity (Real.goldenRatio ^ 2 * a)
          ((Real.goldenRatio ^ 2)⁻¹ * b) =
        goldenRapidity a b + goldenScalePeriod := by
  have hPhiSqPos : 0 < Real.goldenRatio ^ 2 :=
    pow_pos Real.goldenRatio_pos 2
  have hBaseRatioPos : 0 < a / (-b) :=
    golden_rapidity_argument_pos ha hb
  have hBaseRatioNe : a / (-b) ≠ 0 := ne_of_gt hBaseRatioPos
  have hRatio :
      (Real.goldenRatio ^ 2 * a) /
          (-((Real.goldenRatio ^ 2)⁻¹ * b)) =
        Real.goldenRatio ^ 4 * (a / (-b)) := by
    field_simp [Real.goldenRatio_ne_zero, ne_of_lt hb]
  refine
    ⟨mul_pos hPhiSqPos ha,
      mul_neg_of_pos_of_neg (inv_pos.mpr hPhiSqPos) hb, ?_⟩
  unfold goldenRapidity
  rw [hRatio,
    Real.log_mul (pow_ne_zero 4 Real.goldenRatio_ne_zero) hBaseRatioNe,
    Real.log_pow]
  unfold goldenScalePeriod
  norm_num
  ring

/-- Two explicit unit-level points have rapidities zero and `log 2`, proving
that rapidity is a nontrivial coordinate on the positive branch. -/
theorem golden_rapidity_nontrivial_witnesses :
    let s := Real.sqrt 5
    let baseA := 1 / s
    let baseB := -1 / s
    let movedA := 2 / s
    let movedB := -1 / (2 * s)
    ((goldenNullCombination baseA baseB 0) ^ 2 -
          goldenNullCombination baseA baseB 0 *
            goldenNullCombination baseA baseB 1 -
          (goldenNullCombination baseA baseB 1) ^ 2 = 1) /\
      goldenRapidity baseA baseB = 0 /\
      ((goldenNullCombination movedA movedB 0) ^ 2 -
          goldenNullCombination movedA movedB 0 *
            goldenNullCombination movedA movedB 1 -
          (goldenNullCombination movedA movedB 1) ^ 2 = 1) /\
      goldenRapidity movedA movedB = Real.log 2 /\
      goldenRapidity baseA baseB ≠ goldenRapidity movedA movedB := by
  dsimp only
  have hSqrtPos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hSqrtNe : Real.sqrt 5 ≠ 0 := ne_of_gt hSqrtPos
  have hSqrtSq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hBaseScalar :
      -5 * (1 / Real.sqrt 5) * (-1 / Real.sqrt 5) = 1 := by
    field_simp [hSqrtNe]
    nlinarith
  have hMovedScalar :
      -5 * (2 / Real.sqrt 5) * (-1 / (2 * Real.sqrt 5)) = 1 := by
    field_simp [hSqrtNe]
    nlinarith
  have hBaseRatio :
      (1 / Real.sqrt 5) / (-(-1 / Real.sqrt 5)) = 1 := by
    field_simp [hSqrtNe]
  have hMovedRatio :
      (2 / Real.sqrt 5) / (-(-1 / (2 * Real.sqrt 5))) = 4 := by
    field_simp [hSqrtNe]
    ring
  have hBaseRapidity :
      goldenRapidity (1 / Real.sqrt 5) (-1 / Real.sqrt 5) = 0 := by
    unfold goldenRapidity
    rw [hBaseRatio, Real.log_one]
    ring
  have hMovedRapidity :
      goldenRapidity (2 / Real.sqrt 5) (-1 / (2 * Real.sqrt 5)) =
        Real.log 2 := by
    unfold goldenRapidity
    rw [hMovedRatio, show (4 : Real) = 2 ^ 2 by norm_num,
      Real.log_pow]
    norm_num
    ring
  refine
    ⟨golden_lorentz_null_combination (1 / Real.sqrt 5)
        (-1 / Real.sqrt 5) |>.trans hBaseScalar,
      hBaseRapidity,
      golden_lorentz_null_combination (2 / Real.sqrt 5)
        (-1 / (2 * Real.sqrt 5)) |>.trans hMovedScalar,
      hMovedRapidity, ?_⟩
  rw [hBaseRapidity, hMovedRapidity]
  exact ne_of_lt (Real.log_pos (by norm_num))

/-- The atom's complete computable core: golden nullity, the `-5ab` form,
positive rapidity, the unit-level closed form, the Busemann cocycle law,
Fibonacci double-step translation, and two distinct rapidity witnesses. -/
theorem golden_busemann_coordinate :
    (Real.goldenRatio ^ 2 - Real.goldenRatio - 1 = 0 /\
      Real.goldenConj ^ 2 - Real.goldenConj - 1 = 0) /\
    (forall a b : Real,
      (goldenNullCombination a b 0) ^ 2 -
          goldenNullCombination a b 0 * goldenNullCombination a b 1 -
          (goldenNullCombination a b 1) ^ 2 = -5 * a * b) /\
    (forall {a b : Real}, 0 < a -> b < 0 -> 0 < a / (-b)) /\
    (forall {a b : Real}, 0 < a -> b < 0 ->
      (goldenNullCombination a b 0) ^ 2 -
          goldenNullCombination a b 0 * goldenNullCombination a b 1 -
          (goldenNullCombination a b 1) ^ 2 = 1 ->
        goldenRapidity a b = Real.log (a * Real.sqrt 5)) /\
    (forall a b c d e f : Real,
      goldenBusemannCocycle a b c d + goldenBusemannCocycle c d e f =
        goldenBusemannCocycle a b e f) /\
    (forall {a b : Real}, 0 < a -> b < 0 ->
      0 < Real.goldenRatio ^ 2 * a /\
        (Real.goldenRatio ^ 2)⁻¹ * b < 0 /\
        goldenRapidity (Real.goldenRatio ^ 2 * a)
            ((Real.goldenRatio ^ 2)⁻¹ * b) =
          goldenRapidity a b + 2 * Real.log Real.goldenRatio) /\
    (forall v : Fin 2 -> Real,
      ((fibonacciSubstitution ^ 2) *ᵥ v) 0 ^ 2 -
          ((fibonacciSubstitution ^ 2) *ᵥ v) 0 *
            ((fibonacciSubstitution ^ 2) *ᵥ v) 1 -
          ((fibonacciSubstitution ^ 2) *ᵥ v) 1 ^ 2 =
        v 0 ^ 2 - v 0 * v 1 - v 1 ^ 2) /\
    (let s := Real.sqrt 5
     let baseA := 1 / s
     let baseB := -1 / s
     let movedA := 2 / s
     let movedB := -1 / (2 * s)
     ((goldenNullCombination baseA baseB 0) ^ 2 -
          goldenNullCombination baseA baseB 0 *
            goldenNullCombination baseA baseB 1 -
          (goldenNullCombination baseA baseB 1) ^ 2 = 1) /\
      goldenRapidity baseA baseB = 0 /\
      ((goldenNullCombination movedA movedB 0) ^ 2 -
          goldenNullCombination movedA movedB 0 *
            goldenNullCombination movedA movedB 1 -
          (goldenNullCombination movedA movedB 1) ^ 2 = 1) /\
      goldenRapidity movedA movedB = Real.log 2 /\
      goldenRapidity baseA baseB ≠ goldenRapidity movedA movedB) := by
  refine
    ⟨golden_null_basis, golden_lorentz_null_combination,
      fun {_ _} ha hb => golden_rapidity_argument_pos ha hb,
      fun {_ _} ha hb hUnit => golden_rapidity_on_unit_level ha hb hUnit,
      golden_busemann_cocycle_add, ?_, ?_,
      golden_rapidity_nontrivial_witnesses⟩
  · intro a b ha hb
    simpa [goldenScalePeriod] using golden_rapidity_double_update ha hb
  · exact golden_lorentz_update.2.1

#print axioms golden_null_basis
#print axioms golden_lorentz_null_combination
#print axioms golden_rapidity_argument_pos
#print axioms golden_unit_level_coefficient_product
#print axioms golden_rapidity_on_unit_level
#print axioms golden_busemann_cocycle_add
#print axioms golden_rapidity_double_update
#print axioms golden_rapidity_nontrivial_witnesses
#print axioms golden_busemann_coordinate

end D5.S3.Observer.GoldenCoding.GoldenBusemannCoordinate
