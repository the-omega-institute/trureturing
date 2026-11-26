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
open private rate c X rate_pos from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities
open private crossDecay quadraticWeight crossProfile crossProfileJet from
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

/-- The affine coordinates used by the compact gap certificates on any nondegenerate box. -/
theorem boxCoordinatesAffine {p : ℕ} (hp : 11 ≤ p) {u v : ℝ} {u₀ u₁ d₀ d₁ : ℚ}
    (huWidth : u₀ < u₁) (hdWidth : d₀ < d₁)
    (hu₀ : (u₀ : ℝ) ≤ u) (hu₁ : u ≤ (u₁ : ℝ))
    (hd₀ : (d₀ : ℝ) ≤ v - u) (hd₁ : v - u ≤ (d₁ : ℝ)) :
    ∃ s t z : ℝ, InBox s t z ∧
      (Model.affineCoordinate 0 ((u₁ + u₀) / 2) ((u₁ - u₀) / 2)).Encloses s t z u ∧
      (Model.affineCoordinate 1 ((d₁ + d₀) / 2) ((d₁ - d₀) / 2)).Encloses s t z (v - u) ∧
      (Model.affineCoordinate 2 (3 / 22) (3 / 22)).Encloses s t z (rate p) ∧
      3 / (p : ℝ) = (3 / 22 : ℝ) + (3 / 22 : ℝ) * z := by
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
  have hh : 3 / (p : ℝ) = (3 / 22 : ℝ) + (3 / 22 : ℝ) * z := by
    dsimp only [z]
    ring
  refine ⟨s, t, z, hb, ?_, ?_, ?_, hh⟩
  · have h := Model.affineCoordinate_sound hb 0 ((u₁ + u₀) / 2) ((u₁ - u₀) / 2)
    simpa only [show (![s, t, z] : Fin 3 → ℝ) 0 = s by rfl, Rat.cast_div, Rat.cast_add,
      Rat.cast_sub, Rat.cast_ofNat, ← hsEq] using h
  · have h := Model.affineCoordinate_sound hb 1 ((d₁ + d₀) / 2) ((d₁ - d₀) / 2)
    simpa only [show (![s, t, z] : Fin 3 → ℝ) 1 = t by rfl, Rat.cast_div, Rat.cast_add,
      Rat.cast_sub, Rat.cast_ofNat, ← htEq] using h
  · change (Model.affineCoordinate 2 (3 / 22) (3 / 22)).Encloses s t z (3 / (p : ℝ))
    rw [hh]
    simpa only [show (![s, t, z] : Fin 3 → ℝ) 2 = z by rfl, Rat.cast_div,
      Rat.cast_ofNat, mul_comm z] using Model.affineCoordinate_sound hb 2 (3 / 22) (3 / 22)

/-- The affine coordinates used by the middle-gap certificate on any nondegenerate box. -/
theorem boxCoordinates {p : ℕ} (hp : 11 ≤ p) {u v : ℝ} {u₀ u₁ d₀ d₁ : ℚ}
    (huWidth : u₀ < u₁) (hdWidth : d₀ < d₁)
    (hu₀ : (u₀ : ℝ) ≤ u) (hu₁ : u ≤ (u₁ : ℝ))
    (hd₀ : (d₀ : ℝ) ≤ v - u) (hd₁ : v - u ≤ (d₁ : ℝ)) :
    ∃ s t z : ℝ, InBox s t z ∧
      (Model.affineCoordinate 0 ((u₁ + u₀) / 2) ((u₁ - u₀) / 2)).Encloses s t z u ∧
      (Model.affineCoordinate 1 ((d₁ + d₀) / 2) ((d₁ - d₀) / 2)).Encloses s t z (v - u) ∧
      (Model.affineCoordinate 2 (3 / 22) (3 / 22)).Encloses s t z (rate p) := by
  obtain ⟨s, t, z, hb, hU, hD, hH, _⟩ :=
    boxCoordinatesAffine hp huWidth hdWidth hu₀ hu₁ hd₀ hd₁
  exact ⟨s, t, z, hb, hU, hD, hH⟩

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

/-- The exponential checks shared by both score models. -/
structure ClearedChecks : Prop where
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

private def weights := middleWeightModels box.H box.U box.D box.Fd box.Fv box.Ifd box.Ic
private def profile := middleCrossProfileModels box.H box.G box.Ifu box.Eu
private def upperRadicand := middleRadicandModel box.G box.C box.Fv box.V
private def lowerRadicand := middleRadicandModel box.G box.C box.Fd box.D

private noncomputable def alphaValue (u : ℝ) (upper : Bool) : ℝ :=
  if upper then 1 / u + 3 / 10 else 5 / 12

private def scores (upperAlpha upperBeta : Bool) : Model × Model :=
  middleEndpointModels box.weights.1 box.upperRadicand box.lowerRadicand
    box.G box.K box.C box.Fd box.Fv box.Ifd (box.Ifd.sub box.H) (box.Ifv.sub box.H)
    box.weights.2.1 box.weights.2.2.1 box.weights.2.2.2 box.Eu box.profile.1 box.profile.2
    (box.alpha upperAlpha) (beta upperBeta) Model.zero

private def clearedBetaUpper (d₀ : ℚ) : ℚ := if 2 ≤ d₀ then 13 / 20 else 1

private def clearedBeta (d₀ : ℚ) (upper : Bool) : Model :=
  if upper then Model.ofRat (clearedBetaUpper d₀) else Model.ofRat (5 / 12)

private def clearedScores (d₀ : ℚ) (a b : Bool) : Model × Model :=
  middleClearedEndpointModels box.H box.weights.1 box.upperRadicand box.lowerRadicand
    box.G box.K box.C box.Fd box.Fv box.Ifd (box.Ifd.sub box.H)
    box.weights.2.1 box.weights.2.2.1 box.weights.2.2.2 box.Eu box.profile.1 box.profile.2
    (box.alpha a) (clearedBeta d₀ b)

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

private structure EndpointEnclosures (p : ℕ) (u v s t z : ℝ) : Prop where
  g : box.G.Encloses s t z (3 + rate p)
  k : box.K.Encloses s t z (3 + 2 * rate p)
  cModel : box.C.Encloses s t z (c (rate p))
  fd : box.Fd.Encloses s t z (upperTailGap (rate p) (v - u))
  fv : box.Fv.Encloses s t z (upperTailGap (rate p) v)
  id : box.Ifd.Encloses s t z (upperTailGap (rate p) (v - u))⁻¹
  ellD : (box.Ifd.sub box.H).Encloses s t z (upperTailSlope (rate p) (v - u))
  eu : box.Eu.Encloses s t z (crossDecay (rate p) u)
  x : box.upperRadicand.Encloses s t z (X (rate p) v)
  y : box.lowerRadicand.Encloses s t z (X (rate p) (v - u))
  w : box.weights.1.Encloses s t z (quadraticWeight (rate p) (v - u))
  e : box.weights.2.1.Encloses s t z
    (Real.exp (-((1 + rate p) * (v - u))) / (c (rate p) * upperTailGap (rate p) (v - u) ^ 2))
  q : box.weights.2.2.1.Encloses s t z
    (Real.exp (-(2 * u)) * (upperTailGap (rate p) v / upperTailGap (rate p) (v - u)) ^ 2)
  r : box.weights.2.2.2.Encloses s t z
    (Real.exp (-u) * (upperTailGap (rate p) v / upperTailGap (rate p) (v - u)))
  profileValue : box.profile.1.Encloses s t z (crossProfile (rate p) u)
  profileDu : box.profile.2.Encloses s t z (crossProfileJet (rate p) u v).du
  alphaModel : ∀ a : Bool, (box.alpha a).Encloses s t z (alphaValue u a)

private theorem endpoint_enclosures {p : ℕ} (hp : 11 ≤ p) {u v s t z : ℝ}
    (hu₁ : 1 / 2 ≤ u) (hd₁ : 1 ≤ v - u)
    (hb : InBox s t z) (hU : box.U.Encloses s t z u) (hD : box.D.Encloses s t z (v - u))
    (hH : box.H.Encloses s t z (rate p)) (checks : box.ClearedChecks) :
    box.EndpointEnclosures p u v s t z := by
  let h := rate p
  let d := v - u
  have hp₀ : 0 < p := by omega
  have hh : 0 < h := rate_pos hp₀
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
  have hEu : box.Eu.Encloses s t z (crossDecay h u) := by
    simpa only [Eu, crossDecay, neg, zero_sub] using Model.expChecks_sound hb
      (Model.sub_sound (Model.zero_sound s t z) (Model.mul_sound hb hG hU)) checks.crossU
  have hx := middleRadicandModel_sound hb hG hC hFv hV checks.crossV checks.doubleDecayV
  have hy := middleRadicandModel_sound hb hG hC hFd hD checks.crossD checks.doubleDecayD
  obtain ⟨hw, he, hq, hr⟩ := middleWeightModels_sound hb hH hU hD hFd hFv hIfd hIc
    checks.decayU checks.doubleDecayD checks.ratioDecayD
  obtain ⟨ht, ht₁⟩ := middleCrossProfileModels_sound (v := v) hb hh hu hH hG hIfu hEu
  refine ⟨hG, hK, hC, hFd, hFv, hIfd, hld, hEu, hx, hy, hw, he, hq, hr, ht, ht₁, ?_⟩
  intro a
  cases a
  · simpa [alpha, alphaValue] using Model.ofRat_sound (5 / 12) s t z
  · simpa [alpha, alphaValue, one_div] using Model.add_sound hIu (Model.ofRat_sound (3 / 10) s t z)

private theorem scores_sound {p : ℕ} (hp : 11 ≤ p) {u v s t z : ℝ}
    (hu₁ : 1 / 2 ≤ u) (hd₁ : 1 ≤ v - u)
    (hb : InBox s t z) (hU : box.U.Encloses s t z u) (hD : box.D.Encloses s t z (v - u))
    (hH : box.H.Encloses s t z (rate p)) (checks : box.Checks) (a b : Bool) :
    let α := alphaValue u a
    let β := if b then 1 else 5 / 12
    (box.scores a b).1.Encloses s t z (middleEndpointScores p u v α β 0).1 ∧
      (box.scores a b).2.Encloses s t z (middleEndpointScores p u v α β 0).2 := by
  let h := rate p
  have hp₀ : 0 < p := by omega
  have hh : 0 < h := rate_pos hp₀
  have hhmax : h ≤ 3 / 11 := by
    have hp₁₁ : (11 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp₁₁
  have hu : 0 < u := by linarith
  have huv : u < v := by linarith
  have hv := hu.trans huv
  have common : box.ClearedChecks :=
    ⟨checks.gapU, checks.gapD, checks.gapV, checks.decayU, checks.doubleDecayD,
      checks.doubleDecayV, checks.ratioDecayD, checks.crossU, checks.crossD, checks.crossV⟩
  have inputs := box.endpoint_enclosures hp hu₁ hd₁ hb hU hD hH common
  have hFv := inputs.fv
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
  have hlv : (box.Ifv.sub box.H).Encloses s t z (upperTailSlope h v) := by
    rw [upperTailSlope_eq_inv_gap_sub_rate hh hv]
    exact Model.sub_sound hIfv hH
  obtain ⟨heq, hqq, hrq⟩ := middleReplayRatios hh hu huv
  have hβ : (beta b).Encloses s t z (if b then 1 else 5 / 12) := by
    cases b
    · simpa [beta] using Model.ofRat_sound (5 / 12) s t z
    · simpa [beta] using Model.ofRat_sound 1 s t z
  exact middleEndpointModels_sound hp₀ huv hb inputs.w inputs.x inputs.y inputs.g inputs.k
    inputs.cModel inputs.fd inputs.fv inputs.id inputs.ellD hlv inputs.e inputs.q inputs.r
    inputs.eu inputs.profileValue inputs.profileDu (inputs.alphaModel a) hβ
    (Model.zero_sound s t z) heq hqq hrq

private theorem cleared_scores_sound {p : ℕ} (hp : 0 < p) {u v s t z : ℝ}
    (hu : 0 < u) (huv : u < v) (hb : InBox s t z) (hH : box.H.Encloses s t z (rate p))
    (inputs : box.EndpointEnclosures p u v s t z) (d₀ : ℚ) (a b : Bool) :
    let fv := upperTailGap (rate p) v
    let α := alphaValue u a
    let β := if b then (clearedBetaUpper d₀ : ℝ) else 5 / 12
    (box.clearedScores d₀ a b).1.Encloses s t z (fv * (middleEndpointScores p u v α β 0).1) ∧
      ∃ upperScore : ℝ, (box.clearedScores d₀ a b).2.Encloses s t z upperScore ∧
        quadraticWeight (rate p) (v - u) * upperScore = fv * (middleEndpointScores p u v α β 0).2 := by
  obtain ⟨heq, hqq, hrq⟩ := middleReplayRatios (rate_pos hp) hu huv
  have hβ : (clearedBeta d₀ b).Encloses s t z
      (if b then (clearedBetaUpper d₀ : ℝ) else 5 / 12) := by
    cases b
    · simpa [clearedBeta] using Model.ofRat_sound (5 / 12) s t z
    · simpa [clearedBeta] using Model.ofRat_sound (clearedBetaUpper d₀) s t z
  exact middleClearedEndpointModels_sound hp (hu.trans huv) huv hb hH inputs.w inputs.x inputs.y
    inputs.g inputs.k inputs.cModel inputs.fd inputs.fv inputs.id inputs.ellD inputs.e inputs.q
    inputs.r inputs.eu inputs.profileValue inputs.profileDu (inputs.alphaModel a) hβ heq hqq hrq

private def upperHead (a b : Bool) : Model := (neg (box.scores a b).2).truncate 3

private def headLower (head : Model) : ℚ := head.radius + (scale : ℚ) / 100000

structure EndpointTests (a b : Bool) : Prop where
  zeroPositive : 0 < (neg (box.scores a b).1).lower
  upperPositive : 0 < (neg (box.scores a b).2).lower ∨
    ∀ i ≤ 3, ∀ j ≤ 3, ∀ k ≤ 3,
      headLower (box.upperHead a b) ≤ CompactBernstein.tensorCoefficient
        (box.upperHead a b).polynomial.terms 3 i j k

private def headChecks (degree : ℕ) (head : Model) : Bool :=
  let terms := head.polynomial.terms
  let lower := headLower head
  let indices := List.range (degree + 1)
  indices.all fun i ↦ indices.all fun j ↦ indices.all fun k ↦
    decide (lower ≤ CompactBernstein.tensorCoefficient terms degree i j k)

def zeroCheck (a b : Bool) : Bool := decide (0 < (neg (box.scores a b).1).lower)

def upperCheck (a b : Bool) : Bool := headChecks 3 (box.upperHead a b)

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

private def BernsteinPositive (score : Model) (degree : ℕ) : Prop :=
  let head := (neg score).truncate degree
  ∀ i ≤ degree, ∀ j ≤ degree, ∀ k ≤ degree,
    headLower head ≤ CompactBernstein.tensorCoefficient head.polynomial.terms degree i j k

private theorem neg_of_direct_lower {score : Model} {s t z value : ℝ}
    (hb : InBox s t z) (h : score.Encloses s t z value) (hlower : 0 < (neg score).lower) :
    value < 0 := by
  have hneg := Model.sub_sound (Model.zero_sound s t z) h
  have hpos : (0 : ℝ) < (neg score).lower := by exact_mod_cast hlower
  linarith only [(div_pos hpos scale_real_pos).trans_le (Model.lower_sound hb hneg)]

private theorem neg_of_bernstein_head {score : Model} {s t z value : ℝ}
    (hb : InBox s t z) (h : score.Encloses s t z value) {degree : ℕ}
    (hcoeff : BernsteinPositive score degree) : value < 0 := by
  let head := (neg score).truncate degree
  have hneg := Model.truncate_sound degree hb (Model.sub_sound (Model.zero_sound s t z) h)
  have hbound := Model.lower_of_bernstein (D := degree) (L := headLower head) hb hneg
    (fun _ ha ↦ Model.truncate_degree _ _ ha) hcoeff
  have hpos : 0 < (headLower head : ℝ) - head.radius := by
    simp only [headLower, Rat.cast_add, Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat]
    linarith only [div_pos scale_real_pos (by norm_num : (0 : ℝ) < 100000)]
  linarith only [(div_pos hpos scale_real_pos).trans_le hbound]

private theorem mixed_neg_of_scores {p : ℕ} (hp : 11 ≤ p) {u v β₁ : ℝ}
    (hu : 0 < u) (hu₂ : u ≤ 4) (huv : u < v)
    (hβ₁ : reflectedHalfLogSlope (compositionMoment p 0) v ≤ β₁)
    (hsign : ∀ a b : Bool,
      let α := alphaValue u a
      let β := if b then β₁ else 5 / 12
      (middleEndpointScores p u v α β 0).1 < 0 ∧ (middleEndpointScores p u v α β 0).2 < 0) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  apply logKernel_mixed_neg_of_middle_corner_scores hp₀ hu huv (differentiable_marginal p)
    (μ := 0) (α₀ := 5 / 12) (α₁ := 1 / u + 3 / 10) (β₀ := 5 / 12) (β₁ := β₁) (le_refl 0)
  · exact reflectedHalfLogSlope_ge_five_twelfths hp hu
  · exact reflectedHalfLogSlope_le_inv_add_three_tenths hp₀ hu hu₂
  · exact reflectedHalfLogSlope_ge_five_twelfths hp (hu.trans huv)
  · exact hβ₁
  · intro α β hα hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
    · exact hsign false false
    · exact hsign false true
    · exact hsign true false
    · exact hsign true true

theorem mixed_neg_of_checks {p : ℕ} (hp : 11 ≤ p) {u v s t z : ℝ}
    (hu₁ : 1 / 2 ≤ u) (hu₂ : u ≤ 4) (hd₁ : 1 ≤ v - u)
    (hb : InBox s t z) (hU : box.U.Encloses s t z u) (hD : box.D.Encloses s t z (v - u))
    (hH : box.H.Encloses s t z (rate p)) (checks : box.Checks)
    (corner : ∀ a b : Bool, box.EndpointTests a b) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  apply mixed_neg_of_scores hp (u := u) (v := v) (by linarith) hu₂ (by linarith)
    (reflectedHalfLogSlope_le_one_of_three_halves_le hp₀ (t := v) (by linarith))
  intro a b
  obtain ⟨hz, hh⟩ := box.scores_sound hp hu₁ hd₁ hb hU hD hH checks a b
  obtain ⟨hzero, hupper⟩ := corner a b
  refine ⟨neg_of_direct_lower hb hz hzero, ?_⟩
  rcases hupper with hDirect | hBernstein
  · exact neg_of_direct_lower hb hh hDirect
  · exact neg_of_bernstein_head hb hh (degree := 3) hBernstein

/-- The arithmetic obligations at one corner, with the upper score tested directly
or through a Bernstein head of degree at most four. -/
structure ClearedEndpointTests (d₀ : ℚ) (a b : Bool) : Prop where
  zeroPositive : 0 < (neg (box.clearedScores d₀ a b).1).lower
  upperPositive : 0 < (neg (box.clearedScores d₀ a b).2).lower ∨
    ∃ degree : ℕ, degree ≤ 4 ∧ BernsteinPositive (box.clearedScores d₀ a b).2 degree

def clearedZeroCheck (d₀ : ℚ) (a b : Bool) : Bool :=
  decide (0 < (neg (box.clearedScores d₀ a b).1).lower)

def clearedUpperCheck (d₀ : ℚ) (a b : Bool) (degree : ℕ) : Bool :=
  headChecks degree ((neg (box.clearedScores d₀ a b).2).truncate degree)

def clearedUpperDirectCheck (d₀ : ℚ) (a b : Bool) : Bool :=
  decide (0 < (neg (box.clearedScores d₀ a b).2).lower)

theorem clearedEndpointTests_of_checks (d₀ : ℚ) (a b : Bool) (degree : ℕ) (hdegree : degree ≤ 4)
    (hzero : box.clearedZeroCheck d₀ a b = true)
    (hupper : box.clearedUpperCheck d₀ a b degree = true) :
    box.ClearedEndpointTests d₀ a b := by
  unfold clearedZeroCheck at hzero
  refine ⟨of_decide_eq_true hzero, Or.inr ⟨degree, hdegree, ?_⟩⟩
  simp only [clearedUpperCheck, headChecks, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hupper
  intro i hi j hj k hk
  exact hupper i (by omega) j (by omega) k (by omega)

theorem clearedEndpointTests_of_direct_checks (d₀ : ℚ) (a b : Bool)
    (hzero : box.clearedZeroCheck d₀ a b = true)
    (hupper : box.clearedUpperDirectCheck d₀ a b = true) :
    box.ClearedEndpointTests d₀ a b := by
  unfold clearedZeroCheck at hzero
  unfold clearedUpperDirectCheck at hupper
  exact ⟨of_decide_eq_true hzero, Or.inl (of_decide_eq_true hupper)⟩

/-- The cleared endpoint tests imply the original strict mixed derivative sign. -/
theorem mixed_neg_of_cleared_checks {p : ℕ} (hp : 11 ≤ p) {u v s t z : ℝ} {d₀ : ℚ}
    (hu₁ : 1 / 2 ≤ u) (hu₂ : u ≤ 4) (hd₁ : 1 ≤ v - u) (hd₀ : (d₀ : ℝ) ≤ v - u)
    (hb : InBox s t z) (hU : box.U.Encloses s t z u) (hD : box.D.Encloses s t z (v - u))
    (hH : box.H.Encloses s t z (rate p)) (checks : box.ClearedChecks)
    (corner : ∀ a b : Bool, box.ClearedEndpointTests d₀ a b) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  have hu : 0 < u := by linarith
  have huv : u < v := by linarith
  have hh := rate_pos hp₀
  have hfv := tail_gap_pos hh (hu.trans huv)
  have hw : 0 < quadraticWeight (rate p) (v - u) := by
    have hc : 0 < c (rate p) := by unfold c; positivity
    exact mul_pos (mul_pos hc (pow_pos (tail_gap_pos hh (sub_pos.mpr huv)) 2)) (Real.exp_pos _)
  have hbeta : reflectedHalfLogSlope (compositionMoment p 0) v ≤ (clearedBetaUpper d₀ : ℝ) := by
    by_cases hd : (2 : ℚ) ≤ d₀
    · have hd' : (2 : ℝ) ≤ (d₀ : ℝ) := by exact_mod_cast hd
      simpa [clearedBetaUpper, hd] using
        reflectedHalfLogSlope_le_thirteen_twentieths_of_five_halves_le hp₀ (t := v) (by linarith)
    · simpa [clearedBetaUpper, hd] using
        reflectedHalfLogSlope_le_one_of_three_halves_le hp₀ (t := v) (by linarith)
  have inputs := box.endpoint_enclosures hp hu₁ hd₁ hb hU hD hH checks
  apply mixed_neg_of_scores hp hu hu₂ huv hbeta
  intro a b
  obtain ⟨hz, upperScore, hupper, heq⟩ :=
    box.cleared_scores_sound hp₀ hu huv hb hH inputs d₀ a b
  obtain ⟨hzeroTest, hupperTest⟩ := corner a b
  have hzero := neg_of_direct_lower hb hz hzeroTest
  have hnegativeUpper : upperScore < 0 := by
    rcases hupperTest with hDirect | ⟨degree, _, hBernstein⟩
    · exact neg_of_direct_lower hb hupper hDirect
    · exact neg_of_bernstein_head hb hupper hBernstein
  have hscaledUpper := mul_neg_of_pos_of_neg hw hnegativeUpper
  rw [heq] at hscaledUpper
  exact ⟨(mul_lt_mul_iff_right₀ hfv).mp (by simpa only [mul_zero] using hzero),
    (mul_lt_mul_iff_right₀ hfv).mp (by simpa only [mul_zero] using hscaledUpper)⟩

/-- One set of arithmetic checks gives the strict sign throughout the closed affine box.
The upper slope endpoint is selected by the lower gap endpoint of that box. -/
theorem mixed_neg_of_cleared_interval_checks {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    {u₀ u₁ d₀ d₁ : ℚ} (huMin : 1 / 2 ≤ u₀) (huMax : u₁ ≤ 4) (hdMin : 1 ≤ d₀)
    (huWidth : u₀ < u₁) (hdWidth : d₀ < d₁)
    (hu₀ : (u₀ : ℝ) ≤ u) (hu₁ : u ≤ (u₁ : ℝ))
    (hd₀ : (d₀ : ℝ) ≤ v - u) (hd₁ : v - u ≤ (d₁ : ℝ))
    (checks : (ofIntervals u₀ u₁ d₀ d₁).ClearedChecks)
    (corner : ∀ a b : Bool, (ofIntervals u₀ u₁ d₀ d₁).ClearedEndpointTests d₀ a b) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  obtain ⟨s, t, z, hb, hU, hD, hH⟩ := boxCoordinates hp huWidth hdWidth hu₀ hu₁ hd₀ hd₁
  have huMin' : (1 / 2 : ℝ) ≤ (u₀ : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le.mpr huMin : ((1 / 2 : ℚ) : ℝ) ≤ (u₀ : ℝ))
  have huMax' : (u₁ : ℝ) ≤ 4 := by exact_mod_cast huMax
  have hdMin' : (1 : ℝ) ≤ (d₀ : ℝ) := by exact_mod_cast hdMin
  exact (ofIntervals u₀ u₁ d₀ d₁).mixed_neg_of_cleared_checks hp (huMin'.trans hu₀)
    (hu₁.trans huMax') (hdMin'.trans hd₀) hd₀ hb hU hD hH checks corner

end CompactMiddleBox

end RefinedBMV.PositiveCenter.CompactTaylorModel
