/- GID: D5/S3/Quantum/Semigroups/WuCubicGibbsCheckedCoverCompact
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicGibbsCheckedCoverCompact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared rational expression replay for the refined lower Gibbs cut. -/

import D5.S3.Quantum.Semigroups.WuCubicGibbsNormalizedJoin
import D5.S0.Certificates.BoxCover.RationalIntervalExpression
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Box
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! Exact rational replay for the refined angular cut on sorted Gibbs rays. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Quantum.Semigroups.WuCubicGibbsCheckedCoverCompact

open _root_.Matrix
open D5.S0.Certificates.BoxCover.RationalIntervalExpression
open WuCubicDirectedOccupationCap (Mat)
open WuCubicAngularCertificate
open WuCubicOccupationTaylor
open WuCubicGibbsScaledCoefficients
open WuCubicGibbsNormalizedJoin
open RefinedBMV.FourSpectrumLift (roundDown roundUp roundDown_le le_roundUp)
open private gamma c e bias cutA cutB from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private adjacentFactor from D5.S3.Quantum.Semigroups.WuCubicGibbsScaledCoefficients

/-- Tests for the actual refined cut. A leaf supplies a common rational lower
bound for both positive weights and one for both signed endpoint costs. -/
def refinedRayTests (r d K weightFloor costFloor : ℝ) (h : Fin 4 → ℝ) : Prop :=
  let x := fun i => gibbsLevels r i + d * h i
  let m := x 0
  let n := x 1
  let q := x 2
  let E := cutEnergy r m n q
  let B := cutBias r m n q
  let L₀ := matchedMixture E B
  let κ := longCoeff r m n q / 4
  let P₀ := (E 0 + lowerCoeff r m n q - L₀) / 2
  let P₂ := (E 2 + upperCoeff r n q - L₀) / 2
  let p := P₀ + P₂ + B 1 / 2
  let Lgap := refinedMixtureScaled r m n q
  let ellgap := refinedExcessScaled r m n q
  let loss := (q - n) * (ellgap / 4 +
    Lgap ^ 2 / (4 * (3 * middleEnergyScaled r n q + Lgap)))
  let Jbar := κ + d * K * ((P₀ + P₂) / 4 - loss - (P₀ - P₂) ^ 2 / (4 * p))
  let G₀ := g0scaled r d h
  let G₂ := g2scaled r d h
  0 ≤ matchedMixtureScaled r n q ∧ 0 ≤ ellgap ∧
    refinedHScaled r m n q * (d * K) / 2 ≤ ellgap ∧
    (q - n) * ellgap ≤ B 0 ∧ (q - n) * ellgap ≤ B 2 ∧
    0 < weightFloor ∧ weightFloor ≤ P₀ ∧ weightFloor ≤ P₂ ∧
    costFloor ≤ 0 ∧ costFloor ≤ G₀ ∧ costFloor ≤ G₂ ∧
    -2 * costFloor ≤ K * weightFloor ∧
    0 < p ∧ L₀ / 4 ≤ κ ∧ 0 < Jbar ∧
    0 < occupationTaylorCoefficient r d h - (G₀ + G₂) ^ 2 / (4 * p) -
      d * K * (G₀ - G₂ - (P₀ - P₂) * (G₀ + G₂) / p) ^ 2 / (16 * Jbar)

private theorem divide_common_tilt {p : ℝ} (hp : 0 < p) (O G : ℝ) :
    (4 * p * O - G ^ 2) / (4 * p) = O - G ^ 2 / (4 * p) := by
  have hden : (4 : ℝ) * p ≠ 0 := mul_ne_zero (by norm_num) hp.ne'
  rw [sub_div, mul_comm (4 * p) O, mul_div_cancel_right₀ _ hden]

/-- Consume a refined certificate on a sorted Gibbs ray, allowing equality
of the two middle levels. The cutoff uses only rational floor comparisons. -/
theorem refined_positive_of_ray_tests {r d K weightFloor costFloor : ℝ}
    (U : unitary Mat) (h : Fin 4 → ℝ)
    (hr : 1 ≤ r) (hd : 0 < d) (hK : 1 ≤ K) (hh : h 3 = 0)
    (hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * h i)
    (hg : ∀ i, 1 / 2 ≤ gibbsLevels r i)
    (horder : let x := fun i => gibbsLevels r i + d * h i
              x 0 ≤ x 1 ∧ x 1 ≤ x 2 ∧ x 2 ≤ 1)
    (ht : refinedRayTests r d K weightFloor costFloor h) :
    let x := fun i => gibbsLevels r i + d * h i
    0 < normalizedDeficit r U (x 0) (x 1) (x 2) := by
  dsimp only [refinedRayTests] at ht
  dsimp only at horder ⊢
  obtain ⟨hmn, hnq, hq1⟩ := horder
  obtain ⟨hL₀, hell, hsmall, hleft, hright, hw, hw₀, hw₂, hc, hc₀, hc₂,
    hcut, hp, hκ, hJ, hmargin⟩ := ht
  refine refined_normalized_positive U hr hd hK h hh hx hg hmn hnq hq1
    hL₀ hell hsmall (le_min hleft hright) (hw.trans_le hw₀) (hw.trans_le hw₂)
    hp hκ ?_ hJ ?_
  · apply (div_le_iff₀ (hw.trans_le (le_min hw₀ hw₂))).2
    exact (mul_le_mul_of_nonpos_left (le_min hc (le_min hc₀ hc₂)) (by norm_num)).trans
      (hcut.trans (mul_le_mul_of_nonneg_left (le_min hw₀ hw₂)
        (zero_le_one.trans hK)))
  · rw [divide_common_tilt hp]
    exact hmargin

/-- Membership uses the closed real box with the same rational endpoints
as the expression checks. -/
def InBox (box : Fin 5 → ℚ × ℚ) (z : Fin 5 → ℝ) : Prop :=
  ∀ i, ((box i).1 : ℝ) ≤ z i ∧ z i ≤ ((box i).2 : ℝ)

def rayDirection (z : Fin 5 → ℝ) : Fin 4 → ℝ := ![z 2, z 3, z 4, 0]

/-- A lower-side subbox on the signed face h₀ = -1. Its middle intervals
meet on the repeated-middle ray. -/
def hotBox : Fin 5 → ℚ × ℚ :=
  ![(1049 / 1000, 21 / 20), (0, 1 / 256), (-1, -1),
    (-1, -19 / 20), (-19 / 20, -9 / 10)]

/-- Coordinates are (r,d,h₀,h₁,h₂). The same formulas use the cutoff of
each cell. -/
structure LowerCell where
  box : Fin 5 → ℚ × ℚ
  cutoff : ℚ

private structure ReplayCell where
  box : Fin 5 → ℚ × ℚ
  cutoff : ℚ
  gapCoordinates : Bool
  upperMin : Bool

private def LowerCell.replay (cell : LowerCell) (gapCoordinates upperMin : Bool) : ReplayCell :=
  ⟨cell.box, cell.cutoff, gapCoordinates, upperMin⟩

private def upperDirection (cell : ReplayCell) (z : Fin 5 → ℝ) : ℝ :=
  if cell.gapCoordinates then z 3 + z 4 else z 4

private def replayDirection (cell : ReplayCell) (z : Fin 5 → ℝ) : Fin 4 → ℝ :=
  ![z 2, z 3, upperDirection cell z, 0]

-- Each constructor proposes annotations and factors the proof of the existing
-- checker through its child checks. The only new numerical gate at a
-- reciprocal is the checker's same-sign test.
private structure Checked (box : Fin 5 → ℚ × ℚ) where
  expr : Expr 5
  ok : Bool
  sound : ok = true → check box expr = true ∧ (bounds expr).1 ≤ (bounds expr).2

private def Checked.lo {box : Fin 5 → ℚ × ℚ} (a : Checked box) : ℚ := (bounds a.expr).1
private def Checked.hi {box : Fin 5 → ℚ × ℚ} (a : Checked box) : ℚ := (bounds a.expr).2

section Annotation

variable {box : Fin 5 → ℚ × ℚ}

private def input (box : Fin 5 → ℚ × ℚ) (i : Fin 5) : Checked box where
  expr := .input i (box i).1 (box i).2
  ok := decide ((box i).1 ≤ (box i).2)
  sound h := by
    have ho : (box i).1 ≤ (box i).2 := of_decide_eq_true h
    exact ⟨decide_eq_true ⟨ho, le_rfl, le_rfl⟩, ho⟩

private def lit (q : ℚ) : Checked box where
  expr := .const q q q
  ok := true
  sound _ := ⟨decide_eq_true ⟨le_rfl, le_rfl, le_rfl⟩, le_rfl⟩

private def plus (a b : Checked box) : Checked box where
  expr := .add (a.lo + b.lo) (a.hi + b.hi) a.expr b.expr
  ok := a.ok && b.ok
  sound h := by
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨ca, oa⟩ := a.sound ha
    obtain ⟨cb, ob⟩ := b.sound hb
    have ho := add_le_add oa ob
    refine ⟨?_, ho⟩
    simp only [check, ca, cb, Bool.true_and, Checked.lo, Checked.hi]
    exact decide_eq_true ⟨ho, le_rfl, le_rfl⟩

private def minus (a : Checked box) : Checked box where
  expr := .neg (-a.hi) (-a.lo) a.expr
  ok := a.ok
  sound h := by
    obtain ⟨ca, oa⟩ := a.sound h
    refine ⟨?_, neg_le_neg oa⟩
    simp only [check, ca, Bool.true_and, Checked.lo, Checked.hi]
    exact decide_eq_true ⟨neg_le_neg oa, le_rfl, le_rfl⟩

private def times (a b : Checked box) : Checked box :=
  let ll := a.lo * b.lo
  let lu := a.lo * b.hi
  let ul := a.hi * b.lo
  let uu := a.hi * b.hi
  let l := roundDown (min (min ll lu) (min ul uu))
  let u := roundUp (max (max ll lu) (max ul uu))
  { expr := .mul l u a.expr b.expr
    ok := a.ok && b.ok
    sound := by
      intro h
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
      have lll : l ≤ ll := (roundDown_le _).trans
        ((min_le_left _ _).trans (min_le_left _ _))
      have llu : l ≤ lu := (roundDown_le _).trans
        ((min_le_left _ _).trans (min_le_right _ _))
      have lul : l ≤ ul := (roundDown_le _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
      have luu : l ≤ uu := (roundDown_le _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
      have ull : ll ≤ u := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_roundUp _)
      have ulu : lu ≤ u := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_roundUp _)
      have uul : ul ≤ u := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_roundUp _)
      have uuu : uu ≤ u := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_roundUp _)
      refine ⟨?_, lll.trans ull⟩
      simp only [check, (a.sound ha).1, (b.sound hb).1, Bool.true_and]
      exact decide_eq_true ⟨lll.trans ull, lll, llu, lul, luu, ull, ulu, uul, uuu⟩ }

private def sq (a : Checked box) : Checked box :=
  let lo := if 0 ≤ a.lo then a.lo ^ 2 else if a.hi ≤ 0 then a.hi ^ 2 else 0
  let hi := max (a.lo ^ 2) (a.hi ^ 2)
  let l := roundDown lo
  let u := roundUp hi
  { expr := .square l u a.expr
    ok := a.ok
    sound := by
      intro h
      have hl : lo ≤ hi := by
        dsimp only [lo, hi]
        split
        · exact le_max_left _ _
        · split
          · exact le_max_right _ _
          · exact (sq_nonneg a.lo).trans (le_max_left _ _)
      have hs : l ≤ 0 ∨ (0 ≤ a.lo ∧ l ≤ a.lo ^ 2) ∨ (a.hi ≤ 0 ∧ l ≤ a.hi ^ 2) := by
        have hd : l ≤ lo := roundDown_le _
        by_cases ha : 0 ≤ a.lo
        · exact Or.inr (Or.inl ⟨ha, by simpa only [lo, ite_eq_left ha] using hd⟩)
        by_cases hb : a.hi ≤ 0
        · exact Or.inr (Or.inr ⟨hb, by simpa only [lo, ite_eq_right ha, ite_eq_left hb] using hd⟩)
        · exact Or.inl (by simpa only [lo, ite_eq_right ha, ite_eq_right hb] using hd)
      have ho : l ≤ u := (roundDown_le _).trans (hl.trans (le_roundUp _))
      refine ⟨?_, ho⟩
      simp only [check, (a.sound h).1, Bool.true_and]
      exact decide_eq_true ⟨ho, hs, (le_max_left _ _).trans (le_roundUp _),
        (le_max_right _ _).trans (le_roundUp _)⟩ }

private def recip (a : Checked box) : Checked box :=
  let l := roundDown (1 / a.hi)
  let u := roundUp (1 / a.lo)
  { expr := .inv l u a.expr
    ok := a.ok && decide (a.hi < 0 ∨ 0 < a.lo)
    sound := by
      intro h
      obtain ⟨ha, hsign⟩ := Bool.and_eq_true_iff.mp h
      have hs : a.hi < 0 ∨ 0 < a.lo := of_decide_eq_true hsign
      obtain ⟨ca, oa⟩ := a.sound ha
      have hr : 1 / a.hi ≤ 1 / a.lo := hs.elim
        (fun hn => one_div_le_one_div_of_neg_of_le hn oa)
        (fun hp => one_div_le_one_div_of_le hp oa)
      have ho : l ≤ u := (roundDown_le _).trans (hr.trans (le_roundUp _))
      refine ⟨?_, ho⟩
      simp only [check, ca, Bool.true_and]
      exact decide_eq_true ⟨ho, hs, roundDown_le _, le_roundUp _⟩ }

private abbrev sub (a b : Checked box) : Checked box := plus a (minus b)
private abbrev div (a b : Checked box) : Checked box := times a (recip b)

variable (z : Fin 5 → ℝ)

private theorem eval_input (i : Fin 5) :
    value z (input box i).expr = z i := rfl
private theorem eval_lit (q : ℚ) :
    value z (lit (box := box) q).expr = (q : ℝ) := rfl
private theorem eval_plus (a b : Checked box) :
    value z (plus a b).expr = value z a.expr + value z b.expr := rfl
private theorem eval_minus (a : Checked box) :
    value z (minus a).expr = -value z a.expr := rfl
private theorem eval_times (a b : Checked box) :
    value z (times a b).expr = value z a.expr * value z b.expr := rfl
private theorem eval_sq (a : Checked box) :
    value z (sq a).expr = value z a.expr ^ 2 := rfl
private theorem eval_recip (a : Checked box) :
    value z (recip a).expr = 1 / value z a.expr := rfl
private theorem eval_sub (a b : Checked box) :
    value z (sub a b).expr = value z a.expr - value z b.expr := by
  simp only [sub, eval_plus, eval_minus, sub_eq_add_neg]
private theorem eval_div (a b : Checked box) :
    value z (div a b).expr = value z a.expr / value z b.expr := by
  simp only [div, eval_times, eval_recip, div_eq_mul_inv, one_mul]

end Annotation

local infixl:65 " +ₑ " => plus
local infixl:65 " -ₑ " => sub
local infixl:70 " *ₑ " => times
local infixl:70 " /ₑ " => div

-- Evaluate only the named expressions and their aliases, leaving polynomial
-- equality for ring rather than applying the general simp rules for products.
open Lean.Parser.Tactic in
local macro "simp_cut" "[" rules:simpLemma,* "]" : tactic =>
  `(tactic| simp only [eval_input, eval_lit, eval_plus, eval_minus, eval_times, eval_sq,
    eval_recip, eval_sub, eval_div, Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat, Rat.cast_div,
    Rat.cast_neg, div_eq_mul_inv, one_mul, _root_.mul_inv_rev, $[$rules],*])

section Expressions

variable (cell : ReplayCell)

private def thermal : Checked cell.box := input cell.box 0
private def distance : Checked cell.box := input cell.box 1
private def h0 : Checked cell.box := input cell.box 2
private def h1 : Checked cell.box := input cell.box 3
private def h2 : Checked cell.box :=
  if cell.gapCoordinates then h1 cell +ₑ input cell.box 4 else input cell.box 4

private def rSquared : Checked cell.box := sq (thermal cell)
private def gibbsLow : Checked cell.box := recip (rSquared cell)
private def gibbsMiddle : Checked cell.box := recip (thermal cell)
private def rMinusOne : Checked cell.box := thermal cell -ₑ lit 1
private def rPlusOne : Checked cell.box := thermal cell +ₑ lit 1
private def thermalSum : Checked cell.box := rSquared cell +ₑ thermal cell +ₑ lit 1
private def thermalEnergy : Checked cell.box :=
  lit 9 /ₑ (lit 4 *ₑ (lit 1 +ₑ rSquared cell *ₑ thermal cell))
private def energyFactor : Checked cell.box :=
  lit (1 / 2) *ₑ thermalEnergy cell *ₑ thermal cell *ₑ rPlusOne cell
private def directedFactor : Checked cell.box :=
  lit (1 / 6) *ₑ thermalEnergy cell *ₑ thermal cell *ₑ rMinusOne cell
private def biasFactor : Checked cell.box :=
  lit 2 *ₑ thermalEnergy cell *ₑ thermal cell *ₑ rMinusOne cell *ₑ
    (rSquared cell +ₑ lit 4 *ₑ thermal cell +ₑ lit 1) /ₑ (lit 3 *ₑ thermalSum cell)
private def gradientFactor : Checked cell.box :=
  lit 27 *ₑ rMinusOne cell /ₑ (lit 4 *ₑ (rSquared cell -ₑ thermal cell +ₑ lit 1) *ₑ thermalSum cell)

private def lowerSlope : Checked cell.box := h1 cell -ₑ h0 cell
private def negH1 : Checked cell.box := minus (h1 cell)
private def middleSlope : Checked cell.box :=
  if cell.gapCoordinates then input cell.box 4 else h2 cell +ₑ negH1 cell
private def upperSlope : Checked cell.box := minus (h2 cell)
private def lowerSumSlope : Checked cell.box := h0 cell +ₑ h1 cell
private def middleSumSlope : Checked cell.box := h1 cell +ₑ h2 cell

private def mExpr : Checked cell.box := gibbsLow cell +ₑ distance cell *ₑ h0 cell
private def nExpr : Checked cell.box := gibbsMiddle cell +ₑ distance cell *ₑ h1 cell
private def upperLevelDisplacement : Checked cell.box := distance cell *ₑ h2 cell
private def qExpr : Checked cell.box := gibbsMiddle cell +ₑ upperLevelDisplacement cell

private def baseLowerGap : Checked cell.box := gibbsMiddle cell -ₑ gibbsLow cell
private def baseUpperGap : Checked cell.box := lit 1 -ₑ gibbsMiddle cell
private def baseLowerSum : Checked cell.box := gibbsLow cell +ₑ gibbsMiddle cell
private def baseMiddleSum : Checked cell.box := lit 2 *ₑ gibbsMiddle cell
private def baseUpperSum : Checked cell.box := gibbsMiddle cell +ₑ lit 1
private def lowerGapDisplacement : Checked cell.box := distance cell *ₑ lowerSlope cell

private def lowerGap : Checked cell.box := baseLowerGap cell +ₑ lowerGapDisplacement cell
private def middleGap : Checked cell.box := distance cell *ₑ middleSlope cell
private def upperGapDisplacement : Checked cell.box := distance cell *ₑ upperSlope cell
private def upperGap : Checked cell.box := baseUpperGap cell +ₑ upperGapDisplacement cell

private def lowerSum : Checked cell.box := mExpr cell +ₑ nExpr cell
private def middleSum : Checked cell.box := nExpr cell +ₑ qExpr cell
private def upperSum : Checked cell.box := qExpr cell +ₑ lit 1
private def lowerGapSq : Checked cell.box := sq (lowerGap cell)

private def lowerEnergy : Checked cell.box := energyFactor cell *ₑ lowerGapSq cell *ₑ lowerSum cell
private def scaledMiddleEnergy : Checked cell.box :=
  energyFactor cell *ₑ middleGap cell *ₑ middleSum cell
private def upperGapSq : Checked cell.box := sq (upperGap cell)
private def upperEnergy : Checked cell.box := energyFactor cell *ₑ upperGapSq cell *ₑ upperSum cell

private def nSq : Checked cell.box := sq (nExpr cell)
private def twiceDirectedFactor : Checked cell.box := lit 2 *ₑ directedFactor cell
private def lowerBias : Checked cell.box :=
  biasFactor cell *ₑ lowerGap cell *ₑ (sq (mExpr cell) +ₑ mExpr cell *ₑ nExpr cell +ₑ nSq cell) +ₑ
  twiceDirectedFactor cell *ₑ (lowerGapSq cell *ₑ lowerGap cell)
private def qSq : Checked cell.box := sq (qExpr cell)
private def upperBias : Checked cell.box :=
  biasFactor cell *ₑ upperGap cell *ₑ (qSq cell +ₑ qExpr cell +ₑ lit 1) +ₑ twiceDirectedFactor cell *ₑ
  (upperGapSq cell *ₑ upperGap cell)
private def thriceDirectedFactor : Checked cell.box := lit 3 *ₑ directedFactor cell

private def adjacent (gap sum : Checked cell.box) : Checked cell.box :=
  gap *ₑ (energyFactor cell *ₑ (sum +ₑ middleSum cell) -ₑ
    thriceDirectedFactor cell *ₑ (gap +ₑ middleGap cell))
private def lowerAdjacent : Checked cell.box := adjacent cell (lowerGap cell) (lowerSum cell)
private def upperAdjacent : Checked cell.box := adjacent cell (upperGap cell) (upperSum cell)

private def selectedAdjacent : Checked cell.box :=
  if cell.upperMin then upperAdjacent cell else lowerAdjacent cell

private def scaledMatched : Checked cell.box :=
  lit (1 / 2) *ₑ (biasFactor cell *ₑ (nSq cell +ₑ nExpr cell *ₑ qExpr cell +ₑ qSq cell) +ₑ
  twiceDirectedFactor cell *ₑ sq (middleGap cell)) -ₑ scaledMiddleEnergy cell
private def negScaledMatched : Checked cell.box := minus (scaledMatched cell)
private def scaledExcess : Checked cell.box := selectedAdjacent cell +ₑ negScaledMatched cell
private def matchedWeight : Checked cell.box := middleGap cell *ₑ scaledMatched cell
private def excessWeight : Checked cell.box := middleGap cell *ₑ scaledExcess cell

-- Each endpoint weight uses its own adjacent coefficient on either minimum branch.
private def P0 : Checked cell.box :=
  lit (1 / 2) *ₑ (lowerEnergy cell +ₑ middleGap cell *ₑ (lowerAdjacent cell +ₑ negScaledMatched cell))
private def P2 : Checked cell.box :=
  lit (1 / 2) *ₑ (upperEnergy cell +ₑ middleGap cell *ₑ (upperAdjacent cell +ₑ negScaledMatched cell))
private def p : Checked cell.box :=
  lit (1 / 2) *ₑ (lowerEnergy cell +ₑ upperEnergy cell +ₑ middleGap cell *ₑ (lowerAdjacent cell +ₑ
  upperAdjacent cell)) +ₑ middleGap cell *ₑ scaledMiddleEnergy cell
private def pDifference : Checked cell.box := P0 cell -ₑ P2 cell

private def kappa : Checked cell.box :=
  lit (1 / 4) *ₑ lowerGap cell *ₑ upperGap cell *ₑ (energyFactor cell *ₑ (lowerSum cell +ₑ upperSum
  cell) -ₑ thriceDirectedFactor cell *ₑ (lowerGap cell +ₑ upperGap cell +ₑ lit 2 *ₑ middleGap cell))

private def scaledLossDenominator : Checked cell.box :=
  lit 4 *ₑ (lit 3 *ₑ scaledMiddleEnergy cell +ₑ selectedAdjacent cell)
private def refinedLoss : Checked cell.box :=
  middleGap cell *ₑ (lit (1 / 4) *ₑ scaledExcess cell +ₑ sq (selectedAdjacent cell) /ₑ
  scaledLossDenominator cell)
private def tiltThreshold : Checked cell.box := distance cell *ₑ lit cell.cutoff
private def invFourP : Checked cell.box := recip (lit 4 *ₑ p cell)

private def Jbar : Checked cell.box :=
  kappa cell +ₑ tiltThreshold cell *ₑ (lit (1 / 4) *ₑ (P0 cell +ₑ P2 cell) -ₑ refinedLoss cell -ₑ sq
  (pDifference cell) *ₑ invFourP cell)

private def h2Sq : Checked cell.box := sq (h2 cell)
private def gibbsMiddleH2Sq : Checked cell.box := gibbsMiddle cell *ₑ h2Sq cell
private def h1Sq : Checked cell.box := sq (h1 cell)
private def gibbsMiddleH1Sq : Checked cell.box := gibbsMiddle cell *ₑ h1Sq cell
private def h2Cube : Checked cell.box := h2Sq cell *ₑ h2 cell
private def h1Cube : Checked cell.box := h1Sq cell *ₑ h1 cell
private def halfBiasFactor : Checked cell.box := lit (1 / 2) *ₑ biasFactor cell
private def cutRemainder (gap sum k l vA2 wB2 a3 b3 : Checked cell.box) : Checked cell.box :=
  let d := distance cell
  let k2 := sq k
  halfBiasFactor cell *ₑ (lit 3 *ₑ (wB2 -ₑ vA2) +ₑ d *ₑ (b3 -ₑ a3)) +ₑ
    directedFactor cell *ₑ (lit 3 *ₑ gap *ₑ k2 +ₑ d *ₑ (k2 *ₑ k)) -ₑ
    energyFactor cell *ₑ (lit 2 *ₑ gap *ₑ k *ₑ l +ₑ k2 *ₑ (sum +ₑ d *ₑ l))
private def middleCostRemainder : Checked cell.box :=
  cutRemainder cell (lit 0) (baseMiddleSum cell) (middleSlope cell) (middleSumSlope cell)
    (gibbsMiddleH1Sq cell) (gibbsMiddleH2Sq cell) (h1Cube cell) (h2Cube cell)
private def h0Sq : Checked cell.box := sq (h0 cell)
private def gibbsLowH0Sq : Checked cell.box := gibbsLow cell *ₑ h0Sq cell
private def h0Cube : Checked cell.box := h0Sq cell *ₑ h0 cell

private def adjacentRemainderExpr (gap sum k l : Checked cell.box) : Checked cell.box :=
  let start := energyFactor cell *ₑ (sum +ₑ baseMiddleSum cell) -ₑ thriceDirectedFactor cell *ₑ gap
  let change := energyFactor cell *ₑ (l +ₑ middleSumSlope cell) -ₑ
    thriceDirectedFactor cell *ₑ (k +ₑ middleSlope cell)
  middleSlope cell *ₑ (k *ₑ start +ₑ gap *ₑ change +ₑ distance cell *ₑ k *ₑ change)
private def lowerCostRemainder : Checked cell.box :=
  cutRemainder cell (baseLowerGap cell) (baseLowerSum cell) (lowerSlope cell) (lowerSumSlope cell)
      (gibbsLowH0Sq cell) (gibbsMiddleH1Sq cell) (h0Cube cell) (h1Cube cell) -ₑ
    adjacentRemainderExpr cell (baseLowerGap cell) (baseLowerSum cell)
      (lowerSlope cell) (lowerSumSlope cell) +ₑ middleCostRemainder cell
private def upperCostRemainder : Checked cell.box :=
  cutRemainder cell (baseUpperGap cell) (baseUpperSum cell) (upperSlope cell) (h2 cell)
      (gibbsMiddleH2Sq cell) (lit 0) (h2Cube cell) (lit 0) -ₑ
    adjacentRemainderExpr cell (baseUpperGap cell) (baseUpperSum cell)
      (upperSlope cell) (h2 cell) +ₑ middleCostRemainder cell

private def G0 : Checked cell.box :=
  gradientFactor cell *ₑ (h0 cell *ₑ gibbsMiddle cell -ₑ h2 cell *ₑ gibbsLow cell) +ₑ distance cell *ₑ
  lowerCostRemainder cell
private def G2 : Checked cell.box :=
  gradientFactor cell *ₑ thermal cell *ₑ h1 cell +ₑ distance cell *ₑ upperCostRemainder cell
private def costSum : Checked cell.box := G0 cell +ₑ G2 cell
private def gibbsLowSq : Checked cell.box := sq (gibbsLow cell)
private def gibbsMiddleSq : Checked cell.box := sq (gibbsMiddle cell)

private def gibbsMass : Checked cell.box :=
  gibbsLowSq cell *ₑ gibbsLow cell +ₑ lit 2 *ₑ (gibbsMiddleSq cell *ₑ gibbsMiddle cell) +ₑ lit 1
private def secondMoment : Checked cell.box :=
  gibbsLowH0Sq cell +ₑ gibbsMiddle cell *ₑ (h1Sq cell +ₑ h2Sq cell)
private def thirdMoment : Checked cell.box := h0Cube cell +ₑ h1Cube cell +ₑ h2Cube cell
private def fourthMoment : Checked cell.box := sq (h0Sq cell) +ₑ sq (h1Sq cell) +ₑ sq (h2Sq cell)
private def massSlope : Checked cell.box :=
  lit 3 *ₑ (gibbsLowSq cell *ₑ h0 cell +ₑ gibbsMiddleSq cell *ₑ middleSumSlope cell) +ₑ distance cell
  *ₑ (lit 3 *ₑ secondMoment cell +ₑ distance cell *ₑ thirdMoment cell)
private def thermalH0 : Checked cell.box := thermal cell *ₑ h0 cell
private def thermalH1 : Checked cell.box := thermal cell *ₑ h1 cell
private def negTopDirection : Checked cell.box := minus (lit 0)
private def twiceTopLevel : Checked cell.box := lit 2 *ₑ lit 1
private def thermalH2 : Checked cell.box := thermal cell *ₑ h2 cell

private def occupationEnergy : Checked cell.box :=
  thermalEnergy cell *ₑ (sq (thermalH0 cell +ₑ negH1 cell) *ₑ (baseMiddleSum cell +ₑ distance cell *ₑ
  (thermalH0 cell +ₑ h1 cell)) +ₑ sq (thermalH0 cell +ₑ upperSlope cell) *ₑ (baseMiddleSum cell +ₑ
  distance cell *ₑ (thermalH0 cell +ₑ h2 cell)) +ₑ sq (thermalH1 cell +ₑ negTopDirection cell) *ₑ
  (twiceTopLevel cell +ₑ distance cell *ₑ (thermalH1 cell +ₑ lit 0)) +ₑ sq (thermalH2 cell +ₑ
  negTopDirection cell) *ₑ (twiceTopLevel cell +ₑ distance cell *ₑ (thermalH2 cell +ₑ lit 0)))
private def massDisplacementSq : Checked cell.box := sq (massSlope cell)

private def occupationCoefficient : Checked cell.box :=
  occupationEnergy cell -ₑ lit (9 / 4) *ₑ secondMoment cell -ₑ lit (9 / 4) *ₑ distance cell *ₑ
  thirdMoment cell -ₑ lit (3 / 4) *ₑ sq (distance cell) *ₑ fourthMoment cell +ₑ massDisplacementSq
  cell /ₑ (lit 4 *ₑ gibbsMass cell) -ₑ distance cell *ₑ (massDisplacementSq cell *ₑ massSlope cell) /ₑ
  (lit 12 *ₑ sq (gibbsMass cell))
private def angleLoss : Checked cell.box :=
  tiltThreshold cell *ₑ sq (G0 cell -ₑ G2 cell -ₑ pDifference cell *ₑ costSum cell /ₑ p cell) /ₑ (lit
  16 *ₑ Jbar cell)
private def margin : Checked cell.box :=
  occupationCoefficient cell -ₑ sq (costSum cell) *ₑ invFourP cell -ₑ angleLoss cell

private def adjacentDifference : Checked cell.box :=
  if cell.upperMin then lowerAdjacent cell -ₑ upperAdjacent cell
  else upperAdjacent cell -ₑ lowerAdjacent cell
private def smallCharge : Checked cell.box :=
  scaledExcess cell -ₑ lit (1 / 2) *ₑ (scaledMiddleEnergy cell +ₑ selectedAdjacent cell) *ₑ tiltThreshold
  cell
private def negExcessWeight : Checked cell.box := minus (excessWeight cell)
private def leftCharge : Checked cell.box := lowerBias cell +ₑ negExcessWeight cell
private def rightCharge : Checked cell.box := upperBias cell +ₑ negExcessWeight cell
private def kappaTest : Checked cell.box := kappa cell -ₑ lit (1 / 4) *ₑ matchedWeight cell

end Expressions

private abbrev AtLeast {box : Fin 5 → ℚ × ℚ} (q : ℚ) (a : Checked box) : Prop :=
  a.ok = true ∧ q ≤ a.lo

private abbrev Positive {box : Fin 5 → ℚ × ℚ} (a : Checked box) : Prop :=
  a.ok = true ∧ 0 < a.lo

private def weightFloor (cell : ReplayCell) : ℚ := min (P0 cell).lo (P2 cell).lo
private def costFloor (cell : ReplayCell) : ℚ := min 0 (min (G0 cell).lo (G2 cell).lo)

private def AcceptsReplay (cell : ReplayCell) : Prop :=
  1 ≤ cell.cutoff ∧
  AtLeast 1 (thermal cell) ∧
  AtLeast (1 / 2) (gibbsLow cell) ∧ AtLeast (1 / 2) (gibbsMiddle cell) ∧
  AtLeast (1 / 2) (mExpr cell) ∧ AtLeast (1 / 2) (nExpr cell) ∧ AtLeast (1 / 2) (qExpr cell) ∧
  AtLeast 0 (lowerGap cell) ∧ AtLeast 0 (middleGap cell) ∧ AtLeast 0 (upperGap cell) ∧
  AtLeast 0 (scaledMatched cell) ∧
  AtLeast 0 (scaledExcess cell) ∧ AtLeast 0 (smallCharge cell) ∧
  AtLeast 0 (leftCharge cell) ∧ AtLeast 0 (rightCharge cell) ∧ AtLeast 0 (kappaTest cell) ∧
  Positive (P0 cell) ∧ Positive (P2 cell) ∧ (G0 cell).ok = true ∧ (G2 cell).ok = true ∧
  -2 * costFloor cell ≤ cell.cutoff * weightFloor cell ∧
  Positive (p cell) ∧ Positive (Jbar cell) ∧ Positive (margin cell)

private instance (cell : ReplayCell) : Decidable (AcceptsReplay cell) := by
  unfold AcceptsReplay
  infer_instance

/-- The original coordinates and a certified lower adjacent minimum throughout the box. -/
def Accepts (cell : LowerCell) : Prop :=
  AtLeast 0 (adjacentDifference (cell.replay false false)) ∧
  AcceptsReplay (cell.replay false false)

instance (cell : LowerCell) : Decidable (Accepts cell) := by
  unfold Accepts
  infer_instance

private theorem lower {box : Fin 5 → ℚ × ℚ} {z : Fin 5 → ℝ} (hz : InBox box z)
    {a : Checked box} {q : ℚ} (h : AtLeast q a) :
    (q : ℝ) ≤ value z a.expr := by
  have hq : (q : ℝ) ≤ (a.lo : ℝ) := by exact_mod_cast h.2
  exact hq.trans (checked_expression_encloses box z hz a.expr (a.sound h.1).1).1

private theorem positive {box : Fin 5 → ℚ × ℚ} {z : Fin 5 → ℝ} (hz : InBox box z)
    {a : Checked box} (h : Positive a) : 0 < value z a.expr := by
  have hq : (0 : ℝ) < (a.lo : ℝ) := by exact_mod_cast h.2
  exact hq.trans_le (lower hz (a := a) (q := a.lo) ⟨h.1, le_rfl⟩)

set_option maxHeartbeats 1800000 in
private theorem positive_of_replay (U : unitary Mat) (cell : ReplayCell)
    (hcell : AcceptsReplay cell) (z : Fin 5 → ℝ) (hz : InBox cell.box z) (hd : 0 < z 1)
    (hselect : 0 ≤ value z (adjacentDifference cell).expr) :
    let r := z 0
    let d := z 1
    let h := replayDirection cell z
    let x := fun i => gibbsLevels r i + d * h i
    0 < normalizedDeficit r U (x 0) (x 1) (x 2) := by
  unfold AcceptsReplay at hcell
  obtain ⟨checkK, checkR, checkGl, checkGm, checkM, checkN, checkQ,
    checkLowerGap, checkMiddleGap, checkUpperGap, checkMatched,
    checkExcess, checkSmall, checkLeft, checkRight, checkKappa, checkP0, checkP2,
    checkG0, checkG2, checkCut, checkP, checkJ, checkMargin⟩ := hcell
  let r := z 0
  let d := z 1
  let H := replayDirection cell z
  let K : ℝ := cell.cutoff
  let a := z 2
  let u := z 3
  let t := upperDirection cell z
  let gl := (r ^ 2)⁻¹
  let gm := r⁻¹
  let m := gl + d * a
  let n := gm + d * u
  let q := gm + d * t
  let E := cutEnergy r m n q
  let B := cutBias r m n q
  let L₀ := matchedMixture E B
  let κ := longCoeff r m n q / 4
  let A₀ := (E 0 + lowerCoeff r m n q - L₀) / 2
  let A₂ := (E 2 + upperCoeff r n q - L₀) / 2
  let pReal := A₀ + A₂ + B 1 / 2
  let loss := (q - n) * (refinedExcessScaled r m n q / 4 +
    refinedMixtureScaled r m n q ^ 2 /
      (4 * (3 * middleEnergyScaled r n q + refinedMixtureScaled r m n q)))
  let J := κ + d * K * ((A₀ + A₂) / 4 - loss - (A₀ - A₂) ^ 2 / (4 * pReal))
  have weightIdentity : pReal =
      (E 0 + E 2 + (q - n) * (lowerCoeffScaled r m n q + upperCoeffScaled r n q)) / 2 +
        (q - n) * middleEnergyScaled r n q := by
    simp only [pReal, A₀, A₂, L₀, E, matchedMixture, middle_energy_eq, lower_coeff_eq, upper_coeff_eq]
    ring
  have vThermal : value z (thermal cell).expr = r := rfl
  have vDistance : value z (distance cell).expr = d := rfl
  have vH0 : value z (h0 cell).expr = a := rfl
  have vH1 : value z (h1 cell).expr = u := rfl
  have vH2 : value z (h2 cell).expr = t := by
    cases hc : cell.gapCoordinates <;>
      simp only [h2, t, upperDirection, hc, Bool.false_eq_true, ite_false, ite_true, h1,
        eval_plus, eval_input]
  have vMiddleSlope : value z (middleSlope cell).expr = t - u := by
    cases hc : cell.gapCoordinates <;>
      simp_cut [middleSlope, hc, Bool.false_eq_true, ite_false, ite_true, vH2, negH1, vH1,
        t, upperDirection, u] <;> ring
  have vRSquared : value z (rSquared cell).expr = r ^ 2 := by
    simp_cut [rSquared, vThermal] <;> ring
  have vGibbsLow : value z (gibbsLow cell).expr = gl := by
    simp_cut [gibbsLow, vRSquared, gl] <;> ring
  have vGibbsMiddle : value z (gibbsMiddle cell).expr = gm := by
    simp_cut [gibbsMiddle, vThermal, gm] <;> ring
  have vThermalEnergy : value z (thermalEnergy cell).expr = gamma r := by
    simp_cut [thermalEnergy, vRSquared, vThermal, gamma] <;> ring
  have vEnergyFactor : value z (energyFactor cell).expr = c r := by
    simp_cut [energyFactor, vThermalEnergy, vThermal, rPlusOne, c] <;> ring
  have vDirectedFactor : value z (directedFactor cell).expr = e r := by
    simp_cut [directedFactor, vThermalEnergy, vThermal, rMinusOne, e] <;> ring
  have vBiasFactor : value z (biasFactor cell).expr = bias r := by
    simp_cut [biasFactor, vThermalEnergy, vThermal, rMinusOne, vRSquared, thermalSum, bias] <;> ring
  have vGradientFactor : value z (gradientFactor cell).expr = gradientCoefficient r := by
    simp_cut [gradientFactor, rMinusOne, vThermal, vRSquared, thermalSum, gradientCoefficient] <;> ring
  have vMExpr : value z (mExpr cell).expr = m := by
    simp_cut [mExpr, vGibbsLow, vDistance, vH0, m] <;> ring
  have vNExpr : value z (nExpr cell).expr = n := by
    simp_cut [nExpr, vGibbsMiddle, vDistance, vH1, n] <;> ring
  have vQExpr : value z (qExpr cell).expr = q := by
    simp_cut [qExpr, vGibbsMiddle, upperLevelDisplacement, vDistance, vH2, q] <;> ring
  have vLowerGap : value z (lowerGap cell).expr = n - m := by
    simp_cut [lowerGap, baseLowerGap, vGibbsMiddle, vGibbsLow, lowerGapDisplacement, vDistance, lowerSlope, vH1,
      vH0, m, n] <;> ring
  have vMiddleGap : value z (middleGap cell).expr = q - n := by
    simp_cut [middleGap, vDistance, vMiddleSlope, n, q] <;> ring
  have vUpperGap : value z (upperGap cell).expr = 1 - q := by
    simp_cut [upperGap, baseUpperGap, vGibbsMiddle, upperGapDisplacement, vDistance, upperSlope, vH2, q] <;> ring
  have vLowerEnergy : value z (lowerEnergy cell).expr = E 0 := by
    simp_cut [lowerEnergy, vEnergyFactor, lowerGapSq, vLowerGap, lowerSum, vMExpr, vNExpr, E,
      cutEnergy, cutA, Matrix.cons_val_zero] <;> ring
  have vUpperEnergy : value z (upperEnergy cell).expr = E 2 := by
    simp_cut [upperEnergy, vEnergyFactor, upperGapSq, vUpperGap, upperSum, vQExpr, E, cutEnergy, cutA,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  have vScaledMiddleEnergy : value z (scaledMiddleEnergy cell).expr = middleEnergyScaled r n q := by
    simp_cut [scaledMiddleEnergy, vEnergyFactor, vMiddleGap, middleSum, vNExpr, vQExpr,
      middleEnergyScaled] <;> ring
  have vLowerBias : value z (lowerBias cell).expr = B 0 := by
    simp_cut [lowerBias, vBiasFactor, vLowerGap, vMExpr, vNExpr, nSq, twiceDirectedFactor,
      vDirectedFactor, lowerGapSq, B, cutBias, cutB, Matrix.cons_val_zero] <;> ring
  have vUpperBias : value z (upperBias cell).expr = B 2 := by
    simp_cut [upperBias, vBiasFactor, vUpperGap, qSq, vQExpr, twiceDirectedFactor, vDirectedFactor,
      upperGapSq, B, cutBias, cutB, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> ring
  have vLowerAdjacent : value z (lowerAdjacent cell).expr = lowerCoeffScaled r m n q := by
    simp_cut [lowerAdjacent, adjacent, vLowerGap, vEnergyFactor, lowerSum, vMExpr, vNExpr,
      middleSum, vQExpr, thriceDirectedFactor, vDirectedFactor, vMiddleGap, lowerCoeffScaled,
      adjacentFactor] <;> ring
  have vUpperAdjacent : value z (upperAdjacent cell).expr = upperCoeffScaled r n q := by
    simp_cut [upperAdjacent, adjacent, vUpperGap, vEnergyFactor, upperSum, vQExpr, middleSum, vNExpr,
      thriceDirectedFactor, vDirectedFactor, vMiddleGap, upperCoeffScaled, adjacentFactor] <;> ring
  have vSelectedAdjacent : value z (selectedAdjacent cell).expr = refinedMixtureScaled r m n q := by
    cases hb : cell.upperMin
    · have ho : lowerCoeffScaled r m n q ≤ upperCoeffScaled r n q := by
        apply sub_nonneg.mp
        simpa only [adjacentDifference, hb, Bool.false_eq_true, ite_false, eval_sub,
          vLowerAdjacent, vUpperAdjacent] using hselect
      simp only [selectedAdjacent, hb, Bool.false_eq_true, ite_false, vLowerAdjacent,
        refinedMixtureScaled, min_eq_left ho]
    · have ho : upperCoeffScaled r n q ≤ lowerCoeffScaled r m n q := by
        apply sub_nonneg.mp
        simpa only [adjacentDifference, hb, ite_true, eval_sub, vLowerAdjacent,
          vUpperAdjacent] using hselect
      simp only [selectedAdjacent, hb, ite_true, vUpperAdjacent, refinedMixtureScaled, min_eq_right ho]
  have vScaledMatched : value z (scaledMatched cell).expr = matchedMixtureScaled r n q := by
    simp_cut [scaledMatched, vBiasFactor, nSq, vNExpr, vQExpr, qSq, twiceDirectedFactor,
      vDirectedFactor, vMiddleGap, vScaledMiddleEnergy, matchedMixtureScaled, middleBiasScaled] <;> ring
  have vScaledExcess : value z (scaledExcess cell).expr = refinedExcessScaled r m n q := by
    simp_cut [scaledExcess, vSelectedAdjacent, negScaledMatched, vScaledMatched, refinedExcessScaled] <;> ring
  have vMatchedWeight : value z (matchedWeight cell).expr = L₀ := by
    simp_cut [matchedWeight, vMiddleGap, vScaledMatched, L₀, E, B, matched_mixture_eq] <;> ring
  have vP0 : value z (P0 cell).expr = A₀ := by
    simp_cut [P0, vLowerEnergy, vMiddleGap, vLowerAdjacent, negScaledMatched, vScaledMatched,
      A₀, lower_coeff_eq, L₀, E, B, matched_mixture_eq] <;> ring
  have vP2 : value z (P2 cell).expr = A₂ := by
    simp_cut [P2, vUpperEnergy, vMiddleGap, vUpperAdjacent, negScaledMatched, vScaledMatched, A₂,
      upper_coeff_eq, L₀, E, B, matched_mixture_eq] <;> ring
  have vP : value z (p cell).expr = pReal := by
    simp_cut [p, vLowerEnergy, vUpperEnergy, vMiddleGap, vLowerAdjacent, vUpperAdjacent,
      vScaledMiddleEnergy, weightIdentity] <;> ring
  have vKappa : value z (kappa cell).expr = κ := by
    simp_cut [kappa, vLowerGap, vUpperGap, vEnergyFactor, lowerSum, vMExpr, vNExpr, upperSum, vQExpr,
      thriceDirectedFactor, vDirectedFactor, vMiddleGap, κ, long_coeff_eq] <;> ring
  have vKappaTest : value z (kappaTest cell).expr = κ - L₀ / 4 := by
    simp_cut [kappaTest, vKappa, vMatchedWeight] <;> ring
  have vScaledLossDenominator : value z (scaledLossDenominator cell).expr = 4 * (3 * middleEnergyScaled r n q + refinedMixtureScaled r m n q) := by
    simp_cut [scaledLossDenominator, vScaledMiddleEnergy, vSelectedAdjacent] <;> ring
  have vRefinedLoss : value z (refinedLoss cell).expr = loss := by
    simp_cut [refinedLoss, vMiddleGap, vScaledExcess, vSelectedAdjacent, vScaledLossDenominator,
      loss] <;> ring
  have vSmallCharge : value z (smallCharge cell).expr = refinedExcessScaled r m n q - refinedHScaled r m n q * (d * K) / 2 := by
    simp_cut [smallCharge, vScaledExcess, vScaledMiddleEnergy, vSelectedAdjacent, tiltThreshold,
      vDistance, K, refinedHScaled] <;> ring
  have vLeftCharge : value z (leftCharge cell).expr = B 0 - (q - n) * refinedExcessScaled r m n q := by
    simp_cut [leftCharge, vLowerBias, negExcessWeight, excessWeight, vMiddleGap, vScaledExcess] <;> ring
  have vRightCharge : value z (rightCharge cell).expr = B 2 - (q - n) * refinedExcessScaled r m n q := by
    simp_cut [rightCharge, vUpperBias, negExcessWeight, excessWeight, vMiddleGap, vScaledExcess] <;> ring
  have vJbar : value z (Jbar cell).expr = J := by
    simp_cut [Jbar, vKappa, tiltThreshold, vDistance, vP0, vP2, vRefinedLoss, pDifference,
      invFourP, vP, J, K] <;> ring
  have vMiddleCostRemainder : value z (middleCostRemainder cell).expr = halfBiasRemainder r d gm gm u t - energyRemainder r d gm gm u t := by
    simp_cut [middleCostRemainder, cutRemainder, halfBiasFactor, vBiasFactor, gibbsMiddleH2Sq,
      vGibbsMiddle, h2Sq, vH2, gibbsMiddleH1Sq, h1Sq, vH1, vDistance, h2Cube, h1Cube, vDirectedFactor,
      vMiddleSlope, vEnergyFactor, middleSumSlope, baseMiddleSum, halfBiasRemainder,
      energyRemainder] <;> ring
  have vLowerCostRemainder : value z (lowerCostRemainder cell).expr = endpointRemainder r d gl gm a u gm u t := by
    simp_cut [lowerCostRemainder, cutRemainder, adjacentRemainderExpr, halfBiasFactor, vBiasFactor,
      gibbsMiddleH1Sq, vGibbsMiddle, h1Sq, vH1, gibbsLowH0Sq, vGibbsLow, h0Sq, vH0, vDistance, h1Cube,
      h0Cube, vDirectedFactor, baseLowerGap, lowerSlope, vEnergyFactor, lowerSumSlope, baseLowerSum,
      vMiddleSlope, vH2, baseMiddleSum, thriceDirectedFactor, middleSumSlope,
      vMiddleCostRemainder, endpointRemainder, halfBiasRemainder, energyRemainder, adjacentRemainder,
      adjacentFactor] <;> ring
  have vUpperCostRemainder : value z (upperCostRemainder cell).expr = endpointRemainder r d gm 1 t 0 gm u t := by
    simp_cut [upperCostRemainder, cutRemainder, adjacentRemainderExpr, halfBiasFactor, vBiasFactor,
      gibbsMiddleH2Sq, vGibbsMiddle, h2Sq, vH2, vDistance, h2Cube, vDirectedFactor, baseUpperGap,
      upperSlope, vEnergyFactor, baseUpperSum, vMiddleSlope, vH1, baseMiddleSum,
      thriceDirectedFactor, middleSumSlope, vMiddleCostRemainder, endpointRemainder,
      halfBiasRemainder, energyRemainder, adjacentRemainder, adjacentFactor] <;> ring
  have vG0 : value z (G0 cell).expr = g0scaled r d H := by
    simp_cut [G0, vGradientFactor, vH0, vGibbsMiddle, vH2, vGibbsLow, vDistance, vLowerCostRemainder,
      g0scaled, H, replayDirection, gibbsLevels, gl, gm, a, u, t, r, d, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] <;> ring
  have vG2 : value z (G2 cell).expr = g2scaled r d H := by
    simp_cut [G2, vGradientFactor, vThermal, vH1, vDistance, vUpperCostRemainder, g2scaled, H,
      replayDirection, gibbsLevels, gl, gm, a, u, t, r, d, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> ring
  have vGibbsMass : value z (gibbsMass cell).expr = cubicMass (gibbsLevels r) := by
    simp_cut [gibbsMass, gibbsLowSq, vGibbsLow, gibbsMiddleSq, vGibbsMiddle, cubicMass, gibbsLevels, gl,
      gm, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> ring
  have vSecondMoment : value z (secondMoment cell).expr = ∑ i, gibbsLevels r i * H i ^ 2 := by
    simp_cut [secondMoment, gibbsLowH0Sq, vGibbsLow, h0Sq, vH0, vGibbsMiddle, h1Sq, vH1,
      h2Sq, vH2, gibbsLevels, gl, gm, H, replayDirection, a, u, t, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;> ring
  have vThirdMoment : value z (thirdMoment cell).expr = ∑ i, H i ^ 3 := by
    simp_cut [thirdMoment, h0Cube, h0Sq, vH0, h1Cube, h1Sq, vH1, h2Cube,
      h2Sq, vH2, H, replayDirection, a, u, t, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] <;> ring
  have vFourthMoment : value z (fourthMoment cell).expr = ∑ i, H i ^ 4 := by
    simp_cut [fourthMoment, h0Sq, vH0, h1Sq, vH1, h2Sq, vH2, H, replayDirection, a, u, t,
      Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> ring
  have vMassSlope : value z (massSlope cell).expr = massDisplacement (gibbsLevels r) H d := by
    simp_cut [massSlope, gibbsLowSq, vGibbsLow, vH0, gibbsMiddleSq, vGibbsMiddle, middleSumSlope, vH1,
      vH2, vDistance, vSecondMoment, vThirdMoment, massDisplacement, gibbsLevels, gl, gm, H,
      replayDirection, a, u, t, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> ring
  have vOccupationEnergy : value z (occupationEnergy cell).expr = occupationEnergyFactor r d H := by
    simp_cut [occupationEnergy, vThermalEnergy, thermalH0, vThermal, vH0, negH1, vH1,
      baseMiddleSum, vGibbsMiddle, vDistance, upperSlope, vH2, thermalH1, negTopDirection, twiceTopLevel,
      thermalH2, occupationEnergyFactor, occupationEdgeSum, gibbsLevels, gl, gm, H, replayDirection, a,
      u, t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;> ring
  have vOccupationCoefficient : value z (occupationCoefficient cell).expr = occupationTaylorCoefficient r d H := by
    simp_cut [occupationCoefficient, vOccupationEnergy, vSecondMoment, vDistance, vThirdMoment,
      vFourthMoment, massDisplacementSq, vMassSlope, vGibbsMass, occupationTaylorCoefficient] <;> ring
  have vMargin : value z (margin cell).expr = occupationTaylorCoefficient r d H - (g0scaled r d H + g2scaled r d H) ^ 2 / (4 * pReal) -
      d * K * (g0scaled r d H - g2scaled r d H - (A₀ - A₂) *
        (g0scaled r d H + g2scaled r d H) / pReal) ^ 2 / (16 * J) := by
    simp_cut [margin, vOccupationCoefficient, costSum, vG0, vG2, invFourP, vP, angleLoss,
      tiltThreshold, vDistance, pDifference, vP0, vP2, vJbar, K] <;> ring

  have hg₀ : 1 / 2 ≤ gl := by simpa [vGibbsLow] using lower hz checkGl
  have hg₁ : 1 / 2 ≤ gm := by simpa [vGibbsMiddle] using lower hz checkGm
  have hx₀ : 1 / 2 ≤ m := by simpa [vMExpr] using lower hz checkM
  have hx₁ : 1 / 2 ≤ n := by simpa [vNExpr] using lower hz checkN
  have hx₂ : 1 / 2 ≤ q := by simpa [vQExpr] using lower hz checkQ
  have hg : ∀ i, 1 / 2 ≤ gibbsLevels r i := by
    intro i
    fin_cases i <;> first | exact hg₀ | exact hg₁ | norm_num [gibbsLevels]
  have hx : ∀ i, 1 / 2 ≤ gibbsLevels r i + d * H i := by
    intro i
    fin_cases i <;> first | exact hx₀ | exact hx₁ | exact hx₂ | norm_num [gibbsLevels, H, replayDirection]
  have hmn : m ≤ n := sub_nonneg.mp (by simpa [vLowerGap] using lower hz checkLowerGap)
  have hnq : n ≤ q := sub_nonneg.mp (by simpa [vMiddleGap] using lower hz checkMiddleGap)
  have hq1 : q ≤ 1 := sub_nonneg.mp (by simpa [vUpperGap] using lower hz checkUpperGap)
  have hw : 0 < weightFloor cell := lt_min checkP0.2 checkP2.2
  have ht : refinedRayTests r d K (weightFloor cell) (costFloor cell) H := by
    have x₀ : gibbsLevels r 0 + d * H 0 = m := rfl
    have x₁ : gibbsLevels r 1 + d * H 1 = n := rfl
    have x₂ : gibbsLevels r 2 + d * H 2 = q := rfl
    simp only [refinedRayTests, x₀, x₁, x₂]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [vScaledMatched] using lower hz checkMatched
    · simpa [vScaledExcess] using lower hz checkExcess
    · exact sub_nonneg.mp (by simpa [vSmallCharge] using lower hz checkSmall)
    · exact sub_nonneg.mp (by simpa [vLeftCharge] using lower hz checkLeft)
    · exact sub_nonneg.mp (by simpa [vRightCharge] using lower hz checkRight)
    · exact_mod_cast hw
    · have hp : AtLeast (weightFloor cell) (P0 cell) := ⟨checkP0.1, min_le_left _ _⟩
      simpa [vP0] using lower hz hp
    · have hp : AtLeast (weightFloor cell) (P2 cell) := ⟨checkP2.1, min_le_right _ _⟩
      simpa [vP2] using lower hz hp
    · exact_mod_cast (min_le_left 0 (min (G0 cell).lo (G2 cell).lo))
    · have hG : AtLeast (costFloor cell) (G0 cell) :=
        ⟨checkG0, (min_le_right _ _).trans (min_le_left _ _)⟩
      simpa [vG0] using lower hz hG
    · have hG : AtLeast (costFloor cell) (G2 cell) :=
        ⟨checkG2, (min_le_right _ _).trans (min_le_right _ _)⟩
      simpa [vG2] using lower hz hG
    · change (-2 : ℝ) * (costFloor cell : ℝ) ≤ (cell.cutoff : ℝ) * (weightFloor cell : ℝ)
      exact_mod_cast checkCut
    · simpa [vP] using positive hz checkP
    · exact sub_nonneg.mp (by simpa [vKappaTest] using lower hz checkKappa)
    · simpa [vJbar] using positive hz checkJ
    · simpa [vMargin] using positive hz checkMargin
  have hr : 1 ≤ r := by simpa [vThermal] using lower hz checkR
  have hK : 1 ≤ K := by
    change (1 : ℝ) ≤ (cell.cutoff : ℝ)
    exact_mod_cast checkK
  exact refined_positive_of_ray_tests U H hr hd hK rfl hx hg ⟨hmn, hnq, hq1⟩ ht

/-- A checked cell proves positivity for every actual sorted spectrum arising
from a ray in its box at positive displacement. -/
theorem positive_of_accepted (U : unitary Mat) (cell : LowerCell) (hcell : Accepts cell)
    (z : Fin 5 → ℝ) (hz : InBox cell.box z) (hd : 0 < z 1) :
    let r := z 0
    let d := z 1
    let h := rayDirection z
    let x := fun i => gibbsLevels r i + d * h i
    0 < normalizedDeficit r U (x 0) (x 1) (x 2) := by
  apply positive_of_replay U (cell.replay false false) hcell.2 z hz hd
  simpa only [Rat.cast_zero] using lower hz hcell.1

/-- In coordinates `(r,d,h₀,h₁,k)` with `h₂ = h₁ + k`, certify a
minimum branch globally or certify the tests for both branches. -/
def AcceptsGapCell (cell : LowerCell) : Prop :=
  let lo := cell.replay true false
  let hi := cell.replay true true
  (AcceptsReplay lo ∧ AtLeast 0 (adjacentDifference lo)) ∨
    (AcceptsReplay hi ∧ AtLeast 0 (adjacentDifference hi)) ∨
    (AcceptsReplay lo ∧ AcceptsReplay hi)

instance (cell : LowerCell) : Decidable (AcceptsGapCell cell) := by
  unfold AcceptsGapCell
  infer_instance

/-- The sorted ray in gap coordinates uses the minimum at the actual point. -/
theorem positive_of_accepted_gap (U : unitary Mat) (cell : LowerCell)
    (hcell : AcceptsGapCell cell) (z : Fin 5 → ℝ) (hz : InBox cell.box z) (hd : 0 < z 1) :
    let h : Fin 4 → ℝ := ![z 2, z 3, z 3 + z 4, 0]
    let x := fun i => gibbsLevels (z 0) i + z 1 * h i
    0 < normalizedDeficit (z 0) U (x 0) (x 1) (x 2) := by
  let lo := cell.replay true false
  let hi := cell.replay true true
  rcases hcell with ⟨hl, hs⟩ | ⟨hu, hs⟩ | ⟨hl, hu⟩
  · apply positive_of_replay U lo hl z hz hd
    simpa only [Rat.cast_zero] using lower hz hs
  · apply positive_of_replay U hi hu z hz hd
    simpa only [Rat.cast_zero] using lower hz hs
  · rcases le_total (value z (lowerAdjacent lo).expr) (value z (upperAdjacent lo).expr) with hs | hs
    · apply positive_of_replay U lo hl z hz hd
      change 0 ≤ value z (upperAdjacent lo -ₑ lowerAdjacent lo).expr
      rw [eval_sub]
      exact sub_nonneg.mpr hs
    · apply positive_of_replay U hi hu z hz hd
      change 0 ≤ value z (lowerAdjacent hi -ₑ upperAdjacent hi).expr
      rw [eval_sub]
      exact sub_nonneg.mpr hs

/-- The `h₀ = -1` face near the repeated-middle ray with `h₁ = h₂ = 0`.
The gap box contains the sorted part of the entire direction square. -/
def diagonalFaceCell : LowerCell :=
  ⟨![(1049 / 1000, 21 / 20), (0, 1 / 256), (-1, -1), (-1 / 16, 0), (0, 1 / 16)], 120⟩

set_option maxHeartbeats 3600000 in
theorem diagonalFaceCell_accepted : AcceptsGapCell diagonalFaceCell := by
  exact Or.inr (Or.inr ⟨by decide +kernel, by decide +kernel⟩)

/-- Strict positivity on the sorted part of the `h₀ = -1` face with both
middle directions in `[-1/16, 0]), including their common diagonal. -/
theorem diagonalFace_positive {r d h₁ h₂ : ℝ} (U : unitary Mat)
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 21 / 20)
    (hd : 0 < d) (hd₁ : d ≤ 1 / 256)
    (hh₁ : -1 / 16 ≤ h₁) (horder : h₁ ≤ h₂) (hh₂ : h₂ ≤ 0) :
    0 < normalizedDeficit r U ((r ^ 2)⁻¹ - d)
      (r⁻¹ + d * h₁) (r⁻¹ + d * h₂) := by
  let z : Fin 5 → ℝ := ![r, d, -1, h₁, h₂ - h₁]
  have hz : InBox diagonalFaceCell.box z := by
    intro i
    fin_cases i
    · change (((1049 / 1000 : ℚ) : ℝ)) ≤ r ∧ r ≤ (((21 / 20 : ℚ) : ℝ))
      simpa only [Rat.cast_div, Rat.cast_ofNat] using And.intro hr₀ hr₁
    · change ((0 : ℚ) : ℝ) ≤ d ∧ d ≤ (((1 / 256 : ℚ) : ℝ))
      simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using And.intro hd.le hd₁
    · norm_num [diagonalFaceCell, z]
    · change (((-1 / 16 : ℚ) : ℝ)) ≤ h₁ ∧ h₁ ≤ ((0 : ℚ) : ℝ)
      simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero] using
        And.intro hh₁ (horder.trans hh₂)
    · change ((0 : ℚ) : ℝ) ≤ h₂ - h₁ ∧ h₂ - h₁ ≤ (((1 / 16 : ℚ) : ℝ))
      push_cast
      exact ⟨sub_nonneg.mpr horder, by linarith⟩
  have hp := positive_of_accepted_gap U diagonalFaceCell diagonalFaceCell_accepted z hz hd
  change 0 < normalizedDeficit r U ((r ^ 2)⁻¹ + d * (-1)) (r⁻¹ + d * h₁)
    (r⁻¹ + d * (h₁ + (h₂ - h₁))) at hp
  have heq : h₁ + (h₂ - h₁) = h₂ := by ring
  simpa only [heq, mul_neg_one, ← sub_eq_add_neg] using hp

def hotCell : LowerCell := ⟨hotBox, 120⟩

-- Kernel reduction evaluates every closed rational inequality in Accepts.
set_option maxHeartbeats 1800000 in
theorem hotCell_accepted : Accepts hotCell := by decide +kernel

/-- Strict positivity for every positive displacement in the certified cell. -/
theorem hotBox_positive (U : unitary Mat) (z : Fin 5 → ℝ) (hz : InBox hotBox z)
    (hd : 0 < z 1) :
    let h := rayDirection z
    let x := fun i => gibbsLevels (z 0) i + z 1 * h i
    0 < normalizedDeficit (z 0) U (x 0) (x 1) (x 2) :=
  positive_of_accepted U hotCell hotCell_accepted z hz hd

/-- The shared boundary of the two middle direction intervals gives a
whole repeated-middle face at positive displacement. -/
theorem hotBox_repeated_middle {r d : ℝ} (U : unitary Mat)
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 21 / 20)
    (hd : 0 < d) (hd₁ : d ≤ 1 / 256) :
    0 < normalizedDeficit r U ((r ^ 2)⁻¹ + d * (-1))
      (r⁻¹ + d * (-19 / 20)) (r⁻¹ + d * (-19 / 20)) := by
  let z : Fin 5 → ℝ := ![r, d, -1, -19 / 20, -19 / 20]
  have hz : InBox hotBox z := by
    intro i
    fin_cases i
    · change (((1049 / 1000 : ℚ) : ℝ)) ≤ r ∧ r ≤ (((21 / 20 : ℚ) : ℝ))
      simpa only [Rat.cast_div, Rat.cast_ofNat] using And.intro hr₀ hr₁
    · change ((0 : ℚ) : ℝ) ≤ d ∧ d ≤ (((1 / 256 : ℚ) : ℝ))
      simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using And.intro hd.le hd₁
    all_goals norm_num [hotBox, z]
  exact hotBox_positive U z hz hd

#print axioms hotCell_accepted
#print axioms positive_of_accepted
#print axioms hotBox_positive
#print axioms hotBox_repeated_middle
#print axioms diagonalFaceCell_accepted
#print axioms diagonalFace_positive

end D5.S3.Quantum.Semigroups.WuCubicGibbsCheckedCoverCompact
