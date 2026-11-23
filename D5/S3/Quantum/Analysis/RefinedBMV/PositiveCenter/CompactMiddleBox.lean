/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMiddleBox
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform sign certificate on the boxes of the compact middle-gap kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleAssembly
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactSlopeCheckpoints
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorResiduals

/-! A shared analytic certificate for all compact middle-gap boxes. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open CompactGap
open DimThree.Certificate (Sparse checkPackedProduct)
open private rate c from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities
open private crossDecay from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleKernel
open private differentiable_marginal from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.Regularized

/-- Coordinate models and fixed-point reciprocal witnesses for one middle-gap box. -/
structure CompactMiddleBox where
  U : Model
  D : Model
  H : Model
  invLowerGap : Sparse
  invGap : Sparse
  invUpperGap : Sparse
  invScale : Sparse
  invLower : Sparse
  upperGapProduct : Option Sparse := none

namespace CompactMiddleBox

private theorem affine_coordinates {lo hi : ℚ} {x : ℝ} (hlohi : lo < hi)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    let y := (2 * x - ((hi : ℝ) + lo)) / ((hi : ℝ) - lo)
    |y| ≤ 1 ∧ x = ((hi : ℝ) + lo) / 2 + y * (((hi : ℝ) - lo) / 2) := by
  dsimp only
  have hpos : 0 < (hi : ℝ) - lo := sub_pos.mpr (by exact_mod_cast hlohi)
  constructor
  · apply abs_le.mpr
    constructor
    · apply (le_div_iff₀ hpos).2
      linarith only [hlo]
    · apply (div_le_iff₀ hpos).2
      linarith only [hhi]
  · field_simp [hpos.ne'] <;> ring

/-- The affine coordinates used by the middle-gap certificate on any nondegenerate box. -/
theorem boxCoordinates {p : ℕ} (hp : 11 ≤ p) {u v : ℝ} {u₀ u₁ d₀ d₁ : ℚ}
    (huWidth : u₀ < u₁) (hdWidth : d₀ < d₁)
    (hu₀ : (u₀ : ℝ) ≤ u) (hu₁ : u ≤ (u₁ : ℝ))
    (hd₀ : (d₀ : ℝ) ≤ v - u) (hd₁ : v - u ≤ (d₁ : ℝ)) :
    ∃ s t z : ℝ, InBox s t z ∧
      (Model.affineCoordinate 0 ((u₁ + u₀) / 2) ((u₁ - u₀) / 2)).Encloses s t z u ∧
      (Model.affineCoordinate 1 ((d₁ + d₀) / 2) ((d₁ - d₀) / 2)).Encloses s t z (v - u) ∧
      (Model.affineCoordinate 2 (3 / 22) (3 / 22)).Encloses s t z (rate p) := by
  let s := (2 * u - ((u₁ : ℝ) + u₀)) / ((u₁ : ℝ) - u₀)
  let t := (2 * (v - u) - ((d₁ : ℝ) + d₀)) / ((d₁ : ℝ) - d₀)
  let z := 22 / (p : ℝ) - 1
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₀ : (0 : ℝ) < p := by linarith
  have hzUpper : 22 / (p : ℝ) ≤ 2 := (div_le_iff₀ hp₀).2 (by linarith)
  obtain ⟨hs, hsEq⟩ := affine_coordinates huWidth hu₀ hu₁
  obtain ⟨ht, htEq⟩ := affine_coordinates hdWidth hd₀ hd₁
  change u = ((u₁ : ℝ) + u₀) / 2 + s * (((u₁ : ℝ) - u₀) / 2) at hsEq
  change v - u = ((d₁ : ℝ) + d₀) / 2 + t * (((d₁ : ℝ) - d₀) / 2) at htEq
  have hz : |z| ≤ 1 := by
    dsimp [z]
    exact abs_le.mpr ⟨by linarith [div_pos (by norm_num : (0 : ℝ) < 22) hp₀], by linarith⟩
  have hb : InBox s t z := ⟨hs, ht, hz⟩
  refine ⟨s, t, z, hb, ?_, ?_, ?_⟩
  · have h := Model.affineCoordinate_sound hb 0 ((u₁ + u₀) / 2) ((u₁ - u₀) / 2)
    simpa only [show (![s, t, z] : Fin 3 → ℝ) 0 = s by rfl, Rat.cast_div, Rat.cast_add,
      Rat.cast_sub, Rat.cast_ofNat, ← hsEq] using h
  · have h := Model.affineCoordinate_sound hb 1 ((d₁ + d₀) / 2) ((d₁ - d₀) / 2)
    simpa only [show (![s, t, z] : Fin 3 → ℝ) 1 = t by rfl, Rat.cast_div, Rat.cast_add,
      Rat.cast_sub, Rat.cast_ofNat, ← htEq] using h
  · have h := Model.affineCoordinate_sound hb 2 (3 / 22) (3 / 22)
    convert h using 1 <;> first | rfl | (norm_num [rate, z] <;> ring)

variable (box : CompactMiddleBox)

private def V : Model := box.U.add box.D
private def one := Model.ofRat 1
private def three := Model.ofRat 3
private def neg (M : Model) : Model := Model.zero.sub M
private def G := three.add box.H
private def K := three.add ((Model.ofRat 2).mul box.H)
private def C := (box.G.mul box.K).mul (Model.ofRat (1 / 2))
private def Fu := middleGapModel box.H box.U
private def Fd := middleGapModel box.H box.D
private def Fv := middleGapModel box.H box.V
private def Ifu := reciprocalFrom box.Fu box.invLowerGap (7 * scale / 16)
private def Ifd := reciprocalFrom box.Fd box.invGap (3 * scale / 4)
private def Ifv :=
  match box.upperGapProduct with
  | none => reciprocalFrom box.Fv box.invUpperGap scale
  | some product => reciprocalFromPacked box.Fv box.invUpperGap product scale
private def Ic := reciprocalFrom box.C box.invScale (9 * scale / 2)
private def Iu := reciprocalFrom box.U box.invLower (scale / 2)
private def Eu := (neg (box.G.mul box.U)).centeredExp

private def inverseCandidate (X : Model) (center : ℚ) : Model :=
  let displacement := (X.sub (Model.ofRat center)).mul (Model.ofRat center⁻¹)
  Model.series 13 (fun n ↦ Model.ofRat ((-1 : ℚ) ^ n / center)) displacement

private def gapInverseCandidate (H X : Model) (center : ℚ) : Sparse :=
  let bernoulli : List ℚ := [1, 1 / 2, 1 / 12, 0, -1 / 720, 0, 1 / 30240,
    0, -1 / 1209600, 0, 1 / 47900160, 0, -691 / 1307674368000]
  ((inverseCandidate X center).mul (Model.horner bernoulli (H.mul X))).polynomial

/-- Generate candidates for all five reciprocals from the affine coordinates.
The resolved error is checked against the original functions by `mixed_neg_of_checks`. -/
def ofIntervals (u₀ u₁ d₀ d₁ : ℚ) : CompactMiddleBox :=
  let uCenter := (u₁ + u₀) / 2
  let dCenter := (d₁ + d₀) / 2
  let U := Model.affineCoordinate 0 uCenter ((u₁ - u₀) / 2)
  let D := Model.affineCoordinate 1 dCenter ((d₁ - d₀) / 2)
  let H := Model.affineCoordinate 2 (3 / 22) (3 / 22)
  let G := three.add H
  let K := three.add ((Model.ofRat 2).mul H)
  let invScale := ((Model.ofRat 2).mul
    ((inverseCandidate G (69 / 22)).mul (inverseCandidate K (36 / 11)))).polynomial
  ⟨U, D, H, gapInverseCandidate H U uCenter, gapInverseCandidate H D dCenter,
    gapInverseCandidate H (U.add D) (uCenter + dCenter), invScale,
    (inverseCandidate U uCenter).polynomial, none⟩

private def halfDecayInput (M : Model) : Model := box.H.mul (M.mul (Model.ofRat (-1 / 2)))

private def elementaryChecks (M : Model) : Prop :=
  (box.halfDecayInput M).argumentRadius ≤ 2 ∧ (box.halfDecayInput M).expChecks

structure Checks : Prop where
  gapU : box.elementaryChecks box.U
  gapD : box.elementaryChecks box.D
  gapV : box.elementaryChecks box.V
  decayU : (neg box.U).expChecks
  doubleDecayD : ((Model.ofRat (-2)).mul box.D).expChecks
  doubleDecayV : ((Model.ofRat (-2)).mul box.V).expChecks
  ratioDecayD : (neg ((one.add box.H).mul box.D)).expChecks
  crossU : (neg (box.G.mul box.U)).expChecks
  crossD : (neg (box.G.mul box.D)).expChecks
  crossV : (neg (box.G.mul box.V)).expChecks
  checkUpperGapProduct : ∀ product, box.upperGapProduct = some product →
    checkPackedProduct box.Fv.polynomial.terms box.invUpperGap.terms product.terms = true

private def alpha (upper : Bool) : Model :=
  if upper then box.Iu.add (Model.ofRat (3 / 10)) else Model.ofRat (5 / 12)

private def beta (upper : Bool) : Model :=
  Model.ofRat (if upper then 1 else 5 / 12)

private def scores (upperAlpha upperBeta : Bool) : Model × Model :=
  let weights := middleWeightModels box.H box.U box.D box.Fd box.Fv box.Ifd box.Ic
  let profile := middleCrossProfileModels box.H box.G box.Ifu box.Eu
  middleEndpointModels weights.1 (middleRadicandModel box.G box.C box.Fv box.V)
    (middleRadicandModel box.G box.C box.Fd box.D) box.G box.K box.C box.Fd box.Fv box.Ifd (box.Ifd.sub box.H) (box.Ifv.sub box.H)
    weights.2.1 weights.2.2.1 weights.2.2.2 box.Eu profile.1 profile.2
    (box.alpha upperAlpha) (beta upperBeta) Model.zero

private theorem gap_lower {h x a : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ha : 0 < a) (hax : a ≤ x) :
    a / (1 + (3 / 11) * a) ≤ upperTailGap h x := by
  have hx := ha.trans_le hax
  have hd₁ : 0 < 1 + h * a := by positivity
  have hd₂ : 0 < 1 + h * x := by positivity
  have hexp : Real.exp (-(h * x)) ≤ (1 + h * x)⁻¹ := by
    have hbound : 1 + h * x ≤ Real.exp (h * x) := by
      simpa only [add_comm] using Real.add_one_le_exp (h * x)
    simpa only [one_div, ← Real.exp_neg] using
      one_div_le_one_div_of_le hd₂ hbound
  calc
    _ ≤ a / (1 + h * a) :=
      div_le_div_of_nonneg_left ha.le hd₁ (by gcongr)
    _ ≤ x / (1 + h * x) := by
      apply (div_le_div_iff₀ hd₁ hd₂).2
      nlinarith only [hax]
    _ ≤ upperTailGap h x := by
      unfold upperTailGap
      apply (le_div_iff₀ hh).2
      calc
        x / (1 + h * x) * h = 1 - (1 + h * x)⁻¹ := by
          field_simp <;> ring
        _ ≤ 1 - Real.exp (-(h * x)) := sub_le_sub_left hexp _

private theorem reciprocal_from_bound {M : Model} {s t z x : ℝ} {lower : ℕ}
    (hb : InBox s t z) (hx : M.Encloses s t z x) (witness : Sparse)
    (hpos : 0 < lower) (hlo : (lower : ℝ) / (scale : ℝ) ≤ x) :
    (reciprocalFrom M witness lower).Encloses s t z x⁻¹ := by
  simpa only [one_div] using reciprocalFrom_sound hb hx witness hpos hlo

private theorem scores_sound {p : ℕ} (hp : 11 ≤ p) {u v s t z : ℝ}
    (hu₁ : 1 / 2 ≤ u) (hd₁ : 1 ≤ v - u)
    (hb : InBox s t z) (hU : box.U.Encloses s t z u) (hD : box.D.Encloses s t z (v - u))
    (hH : box.H.Encloses s t z (rate p)) (checks : box.Checks) (a b : Bool) :
    let α := if a then 1 / u + 3 / 10 else 5 / 12
    let β := if b then 1 else 5 / 12
    (box.scores a b).1.Encloses s t z (middleEndpointScores p u v α β 0).1 ∧
      (box.scores a b).2.Encloses s t z (middleEndpointScores p u v α β 0).2 := by
  let h := rate p
  let d := v - u
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp [h, rate]; positivity
  have hhmax : h ≤ 3 / 11 := by
    have hp₁₁ : (11 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp₁₁
  have hu : 0 < u := by linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have huv : u < v := sub_pos.mp hd
  have hv := hu.trans huv
  have hV : box.V.Encloses s t z v := by
    simpa only [V, d, add_sub_cancel] using Model.add_sound hU hD
  have hThree : three.Encloses s t z (3 : ℝ) := by simpa [three] using Model.ofRat_sound 3 s t z
  have hTwo : (Model.ofRat 2).Encloses s t z (2 : ℝ) := by simpa using Model.ofRat_sound 2 s t z
  have hHalf : (Model.ofRat (1 / 2)).Encloses s t z (1 / 2 : ℝ) := by
    simpa using Model.ofRat_sound (1 / 2) s t z
  have hG : box.G.Encloses s t z (3 + h) := Model.add_sound hThree hH
  have hK : box.K.Encloses s t z (3 + 2 * h) := Model.add_sound hThree (Model.mul_sound hb hTwo hH)
  have hC : box.C.Encloses s t z (c h) := by
    simpa only [C, c, mul_one_div] using Model.mul_sound hb (Model.mul_sound hb hG hK) hHalf
  have gap {M : Model} {x : ℝ} (hx : M.Encloses s t z x) (hx₀ : 0 < x)
      (hc : box.elementaryChecks M) : (middleGapModel box.H M).Encloses s t z (upperTailGap h x) :=
    middleGapModel_sound hb hH hx hh.ne' hx₀.ne' hc.1 hc.2
  have hFu : box.Fu.Encloses s t z (upperTailGap h u) := gap hU hu checks.gapU
  have hFd : box.Fd.Encloses s t z (upperTailGap h d) := gap hD hd checks.gapD
  have hFv : box.Fv.Encloses s t z (upperTailGap h v) := gap hV hv checks.gapV
  have hIfu : box.Ifu.Encloses s t z (upperTailGap h u)⁻¹ := by
    refine reciprocal_from_bound (lower := 7 * scale / 16) hb hFu _ (by decide) ?_
    calc
      _ ≤ (1 / 2 : ℝ) / (1 + 3 / 11 * (1 / 2)) := by norm_num [scale]
      _ ≤ _ := gap_lower hh hhmax (by norm_num) hu₁
  have hIfd : box.Ifd.Encloses s t z (upperTailGap h d)⁻¹ := by
    refine reciprocal_from_bound (lower := 3 * scale / 4) hb hFd _ (by decide) ?_
    calc
      _ ≤ (1 : ℝ) / (1 + 3 / 11 * 1) := by norm_num [scale]
      _ ≤ _ := gap_lower hh hhmax (by norm_num) hd₁
  have hIfv : box.Ifv.Encloses s t z (upperTailGap h v)⁻¹ := by
    have hlo : (scale : ℝ) / (scale : ℝ) ≤ upperTailGap h v := by
      calc
        _ ≤ (3 / 2 : ℝ) / (1 + 3 / 11 * (3 / 2)) := by norm_num [scale]
        _ ≤ _ := gap_lower hh hhmax (by norm_num) (by linarith)
    cases hproduct : box.upperGapProduct with
    | none =>
      simpa only [Ifv, hproduct] using
        reciprocal_from_bound (lower := scale) hb hFv box.invUpperGap (by decide) hlo
    | some product =>
      simpa only [Ifv, hproduct, one_div] using
        reciprocalFromPacked_sound hb hFv box.invUpperGap product
          (checks.checkUpperGapProduct product hproduct) (by decide) hlo
  have hIc : box.Ic.Encloses s t z (c h)⁻¹ := by
    refine reciprocal_from_bound (lower := 9 * scale / 2) hb hC _ (by decide) ?_
    norm_num [scale, c]
    nlinarith only [hh, sq_nonneg h]
  have hIu : box.Iu.Encloses s t z u⁻¹ := by
    refine reciprocal_from_bound (lower := scale / 2) hb hU _ (by decide) ?_
    simpa only [show ((scale / 2 : ℕ) : ℝ) / (scale : ℝ) = 1 / 2 by norm_num [scale]]
      using hu₁
  have hld : (box.Ifd.sub box.H).Encloses s t z (upperTailSlope h d) := by
    rw [upperTailSlope_eq_inv_gap_sub_rate hh hd]
    exact Model.sub_sound hIfd hH
  have hlv : (box.Ifv.sub box.H).Encloses s t z (upperTailSlope h v) := by
    rw [upperTailSlope_eq_inv_gap_sub_rate hh hv]
    exact Model.sub_sound hIfv hH
  have hEu : box.Eu.Encloses s t z (crossDecay h u) := by
    simpa only [Eu, crossDecay, neg, zero_sub] using Model.expChecks_sound hb
      (Model.sub_sound (Model.zero_sound s t z) (Model.mul_sound hb hG hU)) checks.crossU
  have hx := middleRadicandModel_sound hb hG hC hFv hV checks.crossV checks.doubleDecayV
  have hy := middleRadicandModel_sound hb hG hC hFd hD checks.crossD checks.doubleDecayD
  obtain ⟨hw, he, hq, hr⟩ := middleWeightModels_sound hb hH hU hD hFd hFv hIfd hIc
    checks.decayU checks.doubleDecayD checks.ratioDecayD
  obtain ⟨ht, ht₁⟩ := middleCrossProfileModels_sound (v := v) hb hh hu hH hG hIfu hEu
  obtain ⟨heq, hqq, hrq⟩ := middleReplayRatios hh hu huv
  have hα : (box.alpha a).Encloses s t z (if a then 1 / u + 3 / 10 else 5 / 12) := by
    cases a
    · simpa [alpha] using Model.ofRat_sound (5 / 12) s t z
    · simpa [alpha, one_div] using Model.add_sound hIu (Model.ofRat_sound (3 / 10) s t z)
  have hβ : (beta b).Encloses s t z (if b then 1 else 5 / 12) := by
    cases b
    · simpa [beta] using Model.ofRat_sound (5 / 12) s t z
    · simpa [beta] using Model.ofRat_sound 1 s t z
  simpa only [scores, Fd, Fv] using
    middleEndpointModels_sound hp₀ huv hb hw hx hy hG hK hC hFd hFv
    hIfd hld hlv he hq hr hEu ht ht₁ hα hβ (Model.zero_sound s t z) heq hqq hrq

private def upperHead (a b : Bool) : Model := (neg (box.scores a b).2).truncate 3

private def headLower (head : Model) : ℚ := head.radius + (scale : ℚ) / 100000

structure EndpointTests (a b : Bool) : Prop where
  zeroPositive : 0 < (neg (box.scores a b).1).lower
  upperPositive : 0 < (neg (box.scores a b).2).lower ∨
    ∀ i ≤ 3, ∀ j ≤ 3, ∀ k ≤ 3,
      headLower (box.upperHead a b) ≤ CompactBernstein.tensorCoefficient
        (box.upperHead a b).polynomial.terms 3 i j k

private def headChecks (head : Model) : Bool :=
  let terms := head.polynomial.terms
  let lower := headLower head
  let indices := List.range 4
  indices.all fun i ↦ indices.all fun j ↦ indices.all fun k ↦
    decide (lower ≤ CompactBernstein.tensorCoefficient terms 3 i j k)

def zeroCheck (a b : Bool) : Bool := decide (0 < (neg (box.scores a b).1).lower)

def upperCheck (a b : Bool) : Bool := headChecks (box.upperHead a b)

def upperDirectCheck (a b : Bool) : Bool := decide (0 < (neg (box.scores a b).2).lower)

theorem endpointTests_of_checks (a b : Bool)
    (hzero : box.zeroCheck a b = true) (hupper : box.upperCheck a b = true) :
    box.EndpointTests a b := by
  have hpos : 0 < (neg (box.scores a b).1).lower := by
    unfold zeroCheck at hzero
    exact of_decide_eq_true hzero
  refine ⟨hpos, Or.inr ?_⟩
  simp only [upperCheck, headChecks, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hupper
  intro i hi j hj k hk
  exact hupper i (by omega) j (by omega) k (by omega)

theorem endpointTests_of_direct_checks (a b : Bool)
    (hzero : box.zeroCheck a b = true) (hupper : box.upperDirectCheck a b = true) :
    box.EndpointTests a b := by
  unfold zeroCheck at hzero
  unfold upperDirectCheck at hupper
  exact ⟨of_decide_eq_true hzero, Or.inl (of_decide_eq_true hupper)⟩

theorem mixed_neg_of_checks {p : ℕ} (hp : 11 ≤ p) {u v s t z : ℝ}
    (hu₁ : 1 / 2 ≤ u) (hu₂ : u ≤ 4) (hd₁ : 1 ≤ v - u)
    (hb : InBox s t z) (hU : box.U.Encloses s t z u) (hD : box.D.Encloses s t z (v - u))
    (hH : box.H.Encloses s t z (rate p)) (checks : box.Checks)
    (corner : ∀ a b : Bool, box.EndpointTests a b) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  have hu : 0 < u := by linarith
  have huv : u < v := by linarith
  have hsign (a b : Bool) :
      let α := if a then 1 / u + 3 / 10 else 5 / 12
      let β := if b then 1 else 5 / 12
      (middleEndpointScores p u v α β 0).1 < 0 ∧ (middleEndpointScores p u v α β 0).2 < 0 := by
    dsimp only
    obtain ⟨hz, hh⟩ := box.scores_sound hp hu₁ hd₁ hb hU hD hH checks a b
    have hzero := Model.sub_sound (Model.zero_sound s t z) hz
    have hnegativeUpper := Model.sub_sound (Model.zero_sound s t z) hh
    obtain ⟨hpositive, hcoeff⟩ := corner a b
    have hz' := Model.lower_sound hb hzero
    have hz₀ : (0 : ℝ) < (neg (box.scores a b).1).lower := by exact_mod_cast hpositive
    refine ⟨by linarith [(div_pos hz₀ scale_real_pos).trans_le hz'], ?_⟩
    rcases hcoeff with hDirect | hBernstein
    · have hd : (0 : ℝ) < (neg (box.scores a b).2).lower := by exact_mod_cast hDirect
      linarith [(div_pos hd scale_real_pos).trans_le (Model.lower_sound hb hnegativeUpper)]
    · have hupper := Model.truncate_sound 3 hb hnegativeUpper
      have hh' := Model.lower_of_bernstein hb hupper
        (fun _ ha ↦ Model.truncate_degree _ _ ha) hBernstein
      have hh₀ : (0 : ℝ) < (headLower (box.upperHead a b) : ℝ) -
          (box.upperHead a b).radius := by
        simp only [headLower, Rat.cast_add, Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat]
        linarith only [div_pos scale_real_pos (by norm_num : (0 : ℝ) < 100000)]
      linarith [(div_pos hh₀ scale_real_pos).trans_le hh']
  apply logKernel_mixed_neg_of_middle_corner_scores hp₀ hu huv (differentiable_marginal p)
    (μ := 0) (α₀ := 5 / 12) (α₁ := 1 / u + 3 / 10) (β₀ := 5 / 12) (β₁ := 1) (le_refl 0)
  · exact reflectedHalfLogSlope_ge_five_twelfths hp hu
  · exact reflectedHalfLogSlope_le_inv_add_three_tenths hp₀ hu (by linarith)
  · exact reflectedHalfLogSlope_ge_five_twelfths hp (hu.trans huv)
  · exact reflectedHalfLogSlope_le_one_of_three_halves_le hp₀ (by linarith)
  · intro α β hα hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
    · exact hsign false false
    · exact hsign false true
    · exact hsign true false
    · exact hsign true true

end CompactMiddleBox

end RefinedBMV.PositiveCenter.CompactTaylorModel
