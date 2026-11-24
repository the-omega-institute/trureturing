/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortBox
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Soundness of rational boxes for the fourth-order short-gap tangent comparison. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortComparison
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMomentEnclosure

/-! A rational cell certificate for the compact short-gap mixed derivative. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open scoped BigOperators

open private Model.center from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary

open private shortRootMultiplierReal from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortComparison

/-- The rational endpoints, tangent point, and Taylor orders for one short-gap cell.
The spacing coordinate always covers `[0, 3/11]`. -/
structure CompactShortBox where
  uLo : ℚ
  uHi : ℚ
  dLo : ℚ
  dHi : ℚ
  root : ℚ
  marginalTerms : ℕ
  centerTerms : ℕ
  offsetTerms : ℕ

namespace CompactShortBox

variable (box : CompactShortBox)

private def U : Model :=
  Model.affineCoordinate 0 ((box.uHi + box.uLo) / 2) ((box.uHi - box.uLo) / 2)

private def D : Model :=
  Model.affineCoordinate 1 ((box.dHi + box.dLo) / 2) ((box.dHi - box.dLo) / 2)

private def H : Model := Model.affineCoordinate 2 (3 / 22) (3 / 22)
private def V : Model := box.U.add box.D

private def neg (M : Model) : Model := Model.zero.sub M

private theorem neg_sound {X : Model} {s t z x : ℝ} (hx : X.Encloses s t z x) :
    (neg X).Encloses s t z (-x) := by
  simpa only [neg, zero_sub] using Model.sub_sound (Model.zero_sound s t z) hx

private def half : Model := Model.ofRat (1 / 2)
private def halfGap : Model := box.D.mul half

private def midpoint : ℚ := (box.uHi + box.uLo) / 2 + (box.dHi + box.dLo) / 4
private def midpointWidth : ℚ := (box.uHi - box.uLo) / 2 + (box.dHi - box.dLo) / 4
private def offset : Model := (box.U.add box.halfGap).sub (Model.ofRat box.midpoint)
private def jointRadius : ℚ := 3 * box.dHi / 2
private def marginalRadius : ℚ := box.uHi + box.dHi

private def expUpper (n : ℕ) (x : ℚ) : ℚ :=
  (∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ)) +
    x ^ n / (n.factorial : ℚ) / (1 - x / (n.succ : ℚ))

private theorem expUpper_sound {n : ℕ} {x : ℚ} (hn : 2 ≤ n) (hx : 0 ≤ x)
    (hr : x / (n.succ : ℚ) < 1) :
    Real.exp (x : ℝ) ≤ (expUpper n x : ℝ) := by
  have hx' : 0 ≤ (x : ℝ) := by exact_mod_cast hx
  have hr' : (x : ℝ) / (n.succ : ℝ) < 1 := by exact_mod_cast hr
  have h := compactExp_sub_truncation_geometric_le (z := (x : ℝ)) (R := (x : ℝ))
    hn (by rw [abs_of_nonneg hx']) hr'
  have h' := (abs_le.mp h).2
  unfold expUpper
  push_cast
  rw [Nat.cast_succ] at h'
  exact sub_le_iff_le_add'.1 h'

private def marginal (k : ℕ) (X : Model) : Model :=
  shortMarginalMomentWith CompactShortMomentTable.marginalCoefficients
    k box.marginalTerms box.marginalRadius X

private def inverse (X : Model) : Model :=
  let c := Model.center X
  let displacement := (X.sub (Model.ofRat c)).mul (Model.ofRat c⁻¹)
  let candidate := Model.series 9 (fun n ↦ Model.ofRat ((-1 : ℚ) ^ n / c)) displacement
  reciprocalFrom X candidate.polynomial X.lower.toNat

private def slope (X : Model) : Model :=
  (box.marginal 1 X).mul (inverse (box.marginal 0 X))

private def ZV : Model := box.marginal 0 box.V
private def ZD : Model := box.marginal 0 box.D
private def SD : Model := box.slope box.D
private def SUneg : Model := box.slope (neg box.U)
private def SVneg : Model := box.slope (neg box.V)
private def curvature : Model := ((box.marginal 2 box.D).mul (inverse box.ZD)).sub (box.SD.pow 2)

private def multiplier : Model :=
  shortRootMultiplier box.D box.SUneg box.SVneg (box.slope box.V) box.SD box.curvature
    (inverse box.U)

private def A : Model := (inverse box.U).sub (box.SUneg.mul half)
private def B : Model := (inverse box.V).sub (box.SVneg.mul half)
private def skew : Model := (box.B.sub box.A).mul half

private def skewRadius : ℚ :=
  max 0 (-(neg box.skew).lower : ℚ) / (2 * (scale : ℚ))

private def maxSkew : Model := (Model.ofRat box.skewRadius).widen box.skewRadius

private def moment (j : Fin 4) (k : Fin 3) : Model :=
  shortAffineMidpointMomentModel j k box.centerTerms box.offsetTerms box.midpoint
    box.midpointWidth (expUpper box.centerTerms (2 * |box.midpoint|)) box.offset

private def joint : Model :=
  shortMidpointJointModel box.A box.B box.halfGap box.maxSkew box.jointRadius box.moment

private def kappa : Model := ((Model.ofRat 1).add H).mul (Model.ofRat (1 / 4))

private def tangent : Model :=
  (((box.ZV.mul box.ZD).mul (Model.ofRat box.root⁻¹)).add (Model.ofRat box.root)).mul half

private def negScore : Model :=
  neg ((box.joint.sub (box.A.mul box.B)).add
    (((kappa.mul box.V).mul box.tangent).mul box.multiplier))

private theorem list_sum_range (f : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

private def shiftedCoefficient (degree i k : ℕ) : ℚ :=
  ((List.range (k + 1)).map fun j ↦
    (-1 : ℚ) ^ (k - j) * 2 ^ j * (k.choose j : ℚ) * (i.choose j : ℚ) / degree.choose j).sum

private theorem shiftedCoefficient_eq (degree i k : ℕ) :
    shiftedCoefficient degree i k = CompactBernstein.shiftedCoefficient degree i k := by
  simp only [shiftedCoefficient, list_sum_range, CompactBernstein.shiftedCoefficient]

private def tensorCoefficient (terms : List DimThree.Certificate.Term) (degree i j k : ℕ) : ℚ :=
  (terms.map fun a ↦ (a.coefficient : ℚ) *
    shiftedCoefficient degree i a.exponents.1 *
    shiftedCoefficient degree j a.exponents.2.1 *
    shiftedCoefficient degree k a.exponents.2.2).sum

private theorem tensorCoefficient_eq (terms : List DimThree.Certificate.Term) (degree i j k : ℕ) :
    tensorCoefficient terms degree i j k = CompactBernstein.tensorCoefficient terms degree i j k :=
  by simp only [tensorCoefficient, shiftedCoefficient_eq, CompactBernstein.tensorCoefficient]

/-- Check a lower endpoint in the model's fixed-point units. The Bernstein test moves terms
above the chosen degree into the error radius before converting the polynomial. -/
def lowerCheck (M : Model) (degree : ℕ) (endpoint : ℚ) : Bool :=
  if endpoint ≤ (M.lower : ℚ) then true else
    let head := M.truncate degree
    let indices := List.range (degree + 1)
    indices.all fun i ↦ indices.all fun j ↦ indices.all fun k ↦
      decide (endpoint + (head.radius : ℚ) ≤
        tensorCoefficient head.polynomial.terms degree i j k)

theorem lowerCheck_sound {M : Model} {degree : ℕ} {endpoint : ℚ} {s t z x : ℝ}
    (hb : InBox s t z) (hx : M.Encloses s t z x)
    (hcheck : lowerCheck M degree endpoint = true) :
    (endpoint : ℝ) / scale ≤ x := by
  by_cases h : endpoint ≤ (M.lower : ℚ)
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast h) scale_real_pos.le).trans
      (Model.lower_sound hb hx)
  · simp only [lowerCheck, ite_eq_right h, List.all_eq_true, List.mem_range,
      decide_eq_true_eq, tensorCoefficient_eq] at hcheck
    have hbound := Model.lower_of_bernstein hb (Model.truncate_sound degree hb hx)
      (fun _ ha ↦ Model.truncate_degree _ _ ha)
      (fun i hi j hj k hk ↦ hcheck i (by omega) j (by omega) k (by omega))
    push_cast at hbound
    simpa only [add_sub_cancel_right] using hbound

/-- All hypotheses are rational, integer, or Boolean checks on the cell. The score endpoint
is in units of `1 / scale` and may be any positive rational. -/
structure Checks (degree : ℕ) (endpoint : ℚ) : Prop where
  uMin : 1 / 2 ≤ box.uLo
  uMax : box.uHi ≤ 4
  uWidth : box.uLo < box.uHi
  dMin : 0 ≤ box.dLo
  dMax : box.dHi ≤ 1
  dWidth : box.dLo < box.dHi
  rootPos : 0 < box.root
  marginalOrder : 2 ≤ box.marginalTerms
  centerOrder : 2 ≤ box.centerTerms
  offsetOrder : 2 ≤ box.offsetTerms
  marginalRatio : 2 * box.marginalRadius / (box.marginalTerms.succ : ℚ) < 1
  centerRatio : 2 * |box.midpoint| / (box.centerTerms.succ : ℚ) < 1
  offsetRatio : 2 * box.midpointWidth / (box.offsetTerms.succ : ℚ) < 1
  uPos : 0 < box.U.lower
  vPos : 0 < box.V.lower
  zvPos : 0 < box.ZV.lower
  zdPos : 0 < box.ZD.lower
  zuNegPos : 0 < (box.marginal 0 (neg box.U)).lower
  zvNegPos : 0 < (box.marginal 0 (neg box.V)).lower
  multiplierLower : lowerCheck box.multiplier degree 0 = true
  endpointPos : 0 < endpoint
  scoreLower : lowerCheck box.negScore degree endpoint = true

private theorem inverse_sound {X : Model} {s t z x : ℝ} (hb : InBox s t z)
    (hx : X.Encloses s t z x) (h : 0 < X.lower) :
    (inverse X).Encloses s t z (1 / x) :=
  reciprocalFrom_lower_sound hb hx _ h

private theorem marginal_sound {p : ℕ} (hp : 0 < p) (k : ℕ) {s t z x : ℝ} {X : Model}
    {degree : ℕ} {endpoint : ℚ} (checks : box.Checks degree endpoint)
    (hb : InBox s t z) (hh : 3 / (p : ℝ) = (3 / 22 : ℝ) + (3 / 22 : ℝ) * z)
    (hx : X.Encloses s t z x) (hr : |x| ≤ (box.marginalRadius : ℝ)) :
    (box.marginal k X).Encloses s t z (iteratedDeriv k (compactZ p) x) := by
  exact shortMarginalMomentWith_sound (CompactShortMomentTable.marginalCoefficients_eval hp)
    hp checks.marginalOrder hb hh hx hr (by exact_mod_cast checks.marginalRatio)

private theorem slope_sound {p : ℕ} (hp : 0 < p) {s t z x : ℝ} {X : Model}
    {degree : ℕ} {endpoint : ℚ} (checks : box.Checks degree endpoint)
    (hb : InBox s t z) (hh : 3 / (p : ℝ) = (3 / 22 : ℝ) + (3 / 22 : ℝ) * z)
    (hx : X.Encloses s t z x) (hr : |x| ≤ (box.marginalRadius : ℝ))
    (hpos : 0 < (box.marginal 0 X).lower) :
    (box.slope X).Encloses s t z (compactZSlope p x) := by
  have hzero : (box.marginal 0 X).Encloses s t z (compactZ p x) := by
    simpa using box.marginal_sound hp 0 checks hb hh hx hr
  have h := Model.mul_sound hb (box.marginal_sound hp 1 checks hb hh hx hr)
    (inverse_sound hb hzero hpos)
  simpa [slope, compactZSlope, marginalLogSlope, div_eq_mul_inv] using h

private theorem maxSkew_sound {s t z c : ℝ} (hb : InBox s t z)
    (hskew : box.skew.Encloses s t z c) :
    box.maxSkew.Encloses s t z (max 0 c) := by
  apply Model.widen_sound (g := (box.skewRadius : ℝ)) (Model.ofRat_sound box.skewRadius s t z)
  have hc := Model.lower_sound hb (neg_sound hskew)
  have hr : 2 * (box.skewRadius : ℝ) = max 0 (-(neg box.skew).lower : ℝ) / scale := by
    unfold skewRadius
    push_cast
    ring
  have hcap : 0 ≤ max 0 (-(neg box.skew).lower : ℝ) / scale :=
    div_nonneg (le_max_left _ _) scale_real_pos.le
  have hc' : c ≤ max 0 (-(neg box.skew).lower : ℝ) / scale := by
    have h := div_le_div_of_nonneg_right
      (le_max_right 0 (-(neg box.skew).lower : ℝ)) scale_real_pos.le
    rw [neg_div] at h
    linarith only [hc, h]
  have hmax := max_le hcap hc'
  have hnonneg := le_max_left (0 : ℝ) c
  exact abs_le.2 ⟨by linarith only [hnonneg], by linarith only [hr, hmax]⟩

/-- The checked cell certifies the original kernel for all degrees at least eleven and
all positive gaps in the cell. A zero lower gap endpoint is allowed. -/
theorem mixed_neg_of_checks {p : ℕ} {u v : ℝ} {degree : ℕ} {endpoint : ℚ}
    (hp : 11 ≤ p) (checks : box.Checks degree endpoint)
    (huLo : (box.uLo : ℝ) ≤ u) (huHi : u ≤ (box.uHi : ℝ))
    (hdLo : (box.dLo : ℝ) ≤ v - u) (hdHi : v - u ≤ (box.dHi : ℝ)) (huv : u < v) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  have hp₀ : 0 < p := by omega
  have huMin : ((1 / 2 : ℚ) : ℝ) ≤ (box.uLo : ℝ) := by exact_mod_cast checks.uMin
  norm_num at huMin
  have hdMin : (0 : ℝ) ≤ (box.dLo : ℝ) := by exact_mod_cast checks.dMin
  have hdMax : (box.dHi : ℝ) ≤ 1 := by exact_mod_cast checks.dMax
  have hd : 0 < v - u := sub_pos.mpr huv
  have hu : 0 < u := by linarith only [huMin, huLo]
  have hv := hu.trans huv
  obtain ⟨s, t, z, hb, hU, hD, hH, hh⟩ :=
    CompactMiddleBox.boxCoordinatesAffine hp checks.uWidth checks.dWidth huLo huHi hdLo hdHi
  have hU : box.U.Encloses s t z u := hU
  have hD : box.D.Encloses s t z (v - u) := hD
  have hH : H.Encloses s t z (3 / (p : ℝ)) := hH
  have hV : box.V.Encloses s t z v := by
    simpa only [V, add_sub_cancel] using Model.add_sound hU hD
  have hR : (box.marginalRadius : ℝ) = (box.uHi : ℝ) + (box.dHi : ℝ) := by
    simp [marginalRadius]
  have bU : |u| ≤ (box.marginalRadius : ℝ) := by
    rw [abs_of_pos hu, hR]
    linarith only [huHi, hdHi, hd]
  have bV : |v| ≤ (box.marginalRadius : ℝ) := by
    rw [abs_of_pos hv, hR]
    linarith only [huHi, hdHi]
  have bD : |v - u| ≤ (box.marginalRadius : ℝ) := by
    rw [abs_of_pos hd, hR]
    linarith only [hu, huHi, hdHi]
  have hZV : box.ZV.Encloses s t z (compactZ p v) := by
    simpa only [ZV, iteratedDeriv_zero] using box.marginal_sound hp₀ 0 checks hb hh hV bV
  have hZD : box.ZD.Encloses s t z (compactZ p (v - u)) := by
    simpa only [ZD, iteratedDeriv_zero] using box.marginal_sound hp₀ 0 checks hb hh hD bD
  have hSV := box.slope_sound hp₀ checks hb hh hV bV checks.zvPos
  have hSD := box.slope_sound hp₀ checks hb hh hD bD checks.zdPos
  have hSUneg := box.slope_sound hp₀ checks hb hh (neg_sound hU) (by simpa using bU) checks.zuNegPos
  have hSVneg := box.slope_sound hp₀ checks hb hh (neg_sound hV) (by simpa using bV) checks.zvNegPos
  have hInvU := inverse_sound hb hU checks.uPos
  have hInvV := inverse_sound hb hV checks.vPos
  have hcurvature : box.curvature.Encloses s t z (deriv (compactZSlope p) (v - u)) := by
    rw [deriv_compactZSlope hp₀, ← iteratedDeriv_compactZ_eq_integral hp₀]
    simpa only [curvature, SD, div_eq_mul_inv, one_mul] using Model.sub_sound
      (Model.mul_sound hb (box.marginal_sound hp₀ 2 checks hb hh hD bD)
        (inverse_sound hb hZD checks.zdPos))
      (Model.pow_sound hb hSD 2)
  have hMul := shortRootMultiplier_sound hb hD hSUneg hSVneg hSV hSD hcurvature hInvU
  have hHalf : half.Encloses s t z (1 / 2 : ℝ) := by
    simpa [half] using Model.ofRat_sound (1 / 2) s t z
  have hOne : (Model.ofRat 1).Encloses s t z 1 := by simpa using Model.ofRat_sound 1 s t z
  let a := reflectedHalfLogSlope (compositionMoment p 0) u
  let b := reflectedHalfLogSlope (compositionMoment p 0) v
  have hA : box.A.Encloses s t z a := by
    dsimp only [a]
    rw [reflectedHalfLogSlope_eq_compactZSlope hp₀ hu.ne']
    simpa only [A, SUneg, div_eq_mul_inv, one_mul] using
      Model.sub_sound hInvU (Model.mul_sound hb hSUneg hHalf)
  have hB : box.B.Encloses s t z b := by
    dsimp only [b]
    rw [reflectedHalfLogSlope_eq_compactZSlope hp₀ hv.ne']
    simpa only [B, SVneg, div_eq_mul_inv, one_mul] using
      Model.sub_sound hInvV (Model.mul_sound hb hSVneg hHalf)
  have hHalfGap : box.halfGap.Encloses s t z ((v - u) / 2) := by
    simpa only [halfGap, div_eq_mul_inv, one_mul] using Model.mul_sound hb hD hHalf
  have hOffset : box.offset.Encloses s t z ((u + v) / 2 - (box.midpoint : ℝ)) := by
    have he : u + (v - u) / 2 = (u + v) / 2 := by ring
    simpa only [offset, he] using Model.sub_sound (Model.add_sound hU hHalfGap)
      (Model.ofRat_sound box.midpoint s t z)
  have hOffBound : |(u + v) / 2 - (box.midpoint : ℝ)| ≤ (box.midpointWidth : ℝ) := by
    apply abs_le.2
    push_cast [midpoint, midpointWidth]
    exact ⟨by linarith only [huLo, hdLo], by linarith only [huHi, hdHi]⟩
  have hMoment (j : Fin 4) (k : Fin 3) :
      (box.moment j k).Encloses s t z (shortMidpointMoment p j k ((u + v) / 2)) := by
    have hcenter : 2 * |(box.midpoint : ℝ)| / (box.centerTerms.succ : ℝ) < 1 := by
      exact_mod_cast checks.centerRatio
    have hsmall : 2 * (box.midpointWidth : ℝ) / (box.offsetTerms.succ : ℝ) < 1 := by
      exact_mod_cast checks.offsetRatio
    have hbound := expUpper_sound checks.centerOrder
      (show 0 ≤ 2 * |box.midpoint| by positivity) checks.centerRatio
    push_cast at hbound
    have hm := shortAffineMidpointMomentModel_sound (k := (k : ℕ)) hp checks.centerOrder
      checks.offsetOrder j hb hh hOffset hOffBound hcenter hsmall hbound
    simpa only [moment, add_sub_cancel] using hm
  have hSkew : box.skew.Encloses s t z ((b - a) / 2) := by
    simpa only [skew, div_eq_mul_inv, one_mul] using
      Model.mul_sound hb (Model.sub_sound hB hA) hHalf
  have hJoint := shortMidpointJointModel_sound (radius := box.jointRadius) hb hA hB hHalfGap
    (box.maxSkew_sound hb hSkew) hMoment
  have hκ : kappa.Encloses s t z (compactKappa p) := by
    have hquarter : (Model.ofRat (1 / 4)).Encloses s t z (1 / 4 : ℝ) := by
      simpa using Model.ofRat_sound (1 / 4) s t z
    simpa [kappa, compactKappa, div_eq_mul_inv] using
      Model.mul_sound hb (Model.add_sound hOne hH) hquarter
  have hRootInv : (Model.ofRat box.root⁻¹).Encloses s t z (box.root : ℝ)⁻¹ := by
    simpa only [Rat.cast_inv] using Model.ofRat_sound box.root⁻¹ s t z
  have hTangent := Model.mul_sound hb (Model.add_sound
    (Model.mul_sound hb (Model.mul_sound hb hZV hZD) hRootInv)
    (Model.ofRat_sound box.root s t z)) hHalf
  have hbound := neg_sound (Model.add_sound (Model.sub_sound hJoint (Model.mul_sound hb hA hB))
    (Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb hκ hV) hTangent) hMul))
  rw [shortJointMajorant_eq_moments] at hbound
  have hNet : box.negScore.Encloses s t z
      (-shortMidpointTangentScore p u v box.jointRadius box.root) := by
    simp only [shortMidpointTangentScore]
    convert hbound using 1 <;> first | rfl | (simp only [a, b, div_eq_mul_inv]; ring)
  have hPositive := (div_pos (by exact_mod_cast checks.endpointPos) scale_real_pos).trans_le
    (lowerCheck_sound hb hNet checks.scoreLower)
  have hMPositive : 0 ≤ shortRootMultiplierReal p u v := by
    simpa only [Rat.cast_zero, zero_div] using lowerCheck_sound hb hMul checks.multiplierLower
  have hrad : (box.jointRadius : ℝ) = 3 * (box.dHi : ℝ) / 2 := by simp [jointRadius]
  have hdNonneg : 0 ≤ (box.dHi : ℝ) := hdMin.trans (hdLo.trans hdHi)
  apply logKernel_mixed_neg_of_shortMidpointTangent hp₀ hu huv
    (by exact_mod_cast checks.rootPos) _ _ hMPositive (neg_pos.mp hPositive)
  · rw [hrad]
    linarith only [hdHi]
  · rw [hrad]
    nlinarith only [sq_nonneg ((box.dHi : ℝ) - 1),
      mul_nonneg hdNonneg (sub_nonneg.mpr hdMax), hdMax]

end CompactShortBox

end RefinedBMV.PositiveCenter.CompactTaylorModel
