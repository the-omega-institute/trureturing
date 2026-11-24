/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureBox
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional Taylor-model soundness for rational short-gap quadrature subboxes. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureScore
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortBox
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortIntegratedMeshError
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentGrid

/-! The first-subbox quadrature proof with rational geometry and Taylor orders as inputs. -/

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureBox

open CompactTaylorModel (Model InBox scale scale_real_pos)
open CompactTaylorModel.CompactShortBox (lowerCheck lowerCheck_sound)
open CompactTaylorModel.ShortTangentGrid (Rectangle)

open private neg neg_sound inverse inverse_sound from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortBox
open private CompactTaylorModel.Model.center from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary

open private candidate_sound from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorResiduals

private theorem radicalFrom_nonneg_sound {a : Model} {s t z x : ℝ}
    (hb : InBox s t z) (ha : a.Encloses s t z x) (hx : 0 ≤ x)
    (poly : DimThree.Certificate.Sparse) (hpoly : 0 < (⟨poly, 0⟩ : Model).lower) :
    (CompactTaylorModel.radicalFrom a poly (Nat.sqrt (a.lower.toNat * scale))
      (⟨poly, 0⟩ : Model).lower.toNat).Encloses s t z (Real.sqrt x) := by
  by_cases hlo : 0 ≤ a.lower
  · exact CompactTaylorModel.radicalFrom_lower_sound hb ha poly hlo hpoly (Nat.sqrt_le' _)
  have hz : a.lower.toNat = 0 := Int.toNat_eq_zero.mpr (le_of_not_ge hlo)
  have hcast : (((⟨poly, 0⟩ : Model).lower.toNat : ℕ) : ℝ) = ((⟨poly, 0⟩ : Model).lower : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hpoly.le
  rw [hz]
  apply CompactTaylorModel.radicalFrom_sound (lower := 0) hb ha poly
  · simpa using hx
  · simp
  · rw [hcast]
    exact Model.lower_sound hb (candidate_sound poly s t z)
  · simpa using (show 0 < (⟨poly, 0⟩ : Model).lower.toNat by omega)

private structure Interval where
  lo : ℚ
  hi : ℚ

private def Interval.center (I : Interval) : ℚ := (I.lo + I.hi) / 2
private def Interval.width (I : Interval) : ℚ := (I.hi - I.lo) / 2
private def Interval.radius (I : Interval) : ℚ := |I.center| + I.width
private def Interval.reflect (I : Interval) : Interval := ⟨-I.hi, -I.lo⟩
private noncomputable def Interval.normalize (I : Interval) (x : ℝ) : ℝ :=
  (x - (I.center : ℝ)) / (I.width : ℝ)

private def Interval.axis (I : Interval) (i : Fin 3) : Model :=
  Model.affineCoordinate i I.center I.width

private def Interval.offset (I : Interval) (i : Fin 3) : Model :=
  Model.affineCoordinate i 0 I.width

private theorem Interval.offset_le (I : Interval) {x : ℝ}
    (hlo : (I.lo : ℝ) ≤ x) (hhi : x ≤ (I.hi : ℝ)) :
    |x - (I.center : ℝ)| ≤ (I.width : ℝ) := by
  unfold Interval.center Interval.width
  push_cast
  exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩

private theorem Interval.width_pos (I : Interval) (hlt : I.lo < I.hi) :
    0 < (I.width : ℝ) := by
  have h : (I.lo : ℝ) < (I.hi : ℝ) := by exact_mod_cast hlt
  unfold Interval.width
  push_cast
  exact div_pos (sub_pos.mpr h) (by norm_num)

private theorem Interval.normalize_le (I : Interval) {x : ℝ} (hlt : I.lo < I.hi)
    (hlo : (I.lo : ℝ) ≤ x) (hhi : x ≤ (I.hi : ℝ)) : |I.normalize x| ≤ 1 := by
  have hw := I.width_pos hlt
  rw [Interval.normalize, abs_div, abs_of_pos hw, div_le_iff₀ hw, one_mul]
  exact I.offset_le hlo hhi

private theorem Interval.normalize_mul (I : Interval) (x : ℝ) (hlt : I.lo < I.hi) :
    I.normalize x * (I.width : ℝ) = x - (I.center : ℝ) :=
  div_mul_cancel₀ _ (I.width_pos hlt).ne'

private theorem Interval.axis_sound (I : Interval) {s t z x : ℝ} (i : Fin 3)
    (hb : InBox s t z) (hx : ![s, t, z] i * (I.width : ℝ) = x - (I.center : ℝ)) :
    (I.axis i).Encloses s t z x := by
  simpa only [Interval.axis, hx, add_sub_cancel] using Model.affineCoordinate_sound hb i I.center I.width

private theorem Interval.offset_sound (I : Interval) {s t z x : ℝ} (i : Fin 3)
    (hb : InBox s t z) (hx : ![s, t, z] i * (I.width : ℝ) = x - (I.center : ℝ)) :
    (I.offset i).Encloses s t z (x - (I.center : ℝ)) := by
  simpa only [Interval.offset, hx, Rat.cast_zero, zero_add] using
    Model.affineCoordinate_sound hb i 0 I.width

private theorem Interval.reflect_center (I : Interval) :
    ((I.reflect.center : ℚ) : ℝ) = -(I.center : ℝ) := by
  simp only [Interval.reflect, Interval.center, Rat.cast_div, Rat.cast_add, Rat.cast_neg]
  ring

private def lowerInterval (b : Rectangle) : Interval := ⟨b.uLo, b.uHi⟩
private def gapInterval (b : Rectangle) : Interval := ⟨b.dLo, b.dHi⟩
private def upperInterval (b : Rectangle) : Interval := ⟨b.uLo + b.dLo, b.uHi + b.dHi⟩
private def jointInterval (b : Rectangle) : Interval :=
  (⟨b.uLo + b.dLo / 2, b.uHi + b.dHi / 2⟩ : Interval).reflect

private def lowerAxis (b : Rectangle) : Model := (lowerInterval b).axis 0
private def gapAxis (b : Rectangle) : Model := (gapInterval b).axis 1
private def spacingAxis (hLo hHi : ℚ) : Model := (Interval.mk hLo hHi).axis 2
private def upperAxis (b : Rectangle) : Model := (lowerAxis b).add (gapAxis b)

private def upperOffset (b : Rectangle) : Model :=
  ((lowerInterval b).offset 0).add ((gapInterval b).offset 1)

private def jointOffset (b : Rectangle) : Model :=
  neg (((lowerInterval b).offset 0).add
    (Model.affineCoordinate 1 0 ((gapInterval b).width / 2)))

private def marginalInterval (b : Rectangle) (i : Fin 4) : Interval :=
  ![(lowerInterval b).reflect, (upperInterval b).reflect, upperInterval b, gapInterval b] i

private def marginalOffset (b : Rectangle) (i : Fin 4) : Model :=
  ![neg ((lowerInterval b).offset 0), neg (upperOffset b),
    upperOffset b, (gapInterval b).offset 1] i

/-- Truncation orders for one marginal channel. The two mesh orders apply to the
negative and positive halves of the integration interval. -/
structure MarginalOrders where
  terms : Fin 3 → ℕ
  meshNeg : ℕ
  meshPos : ℕ

/-- Orders for the local Taylor expansion, three joint densities and four marginals.
The marginal order is reflected lower, reflected upper, direct upper, direct gap.
The index into each marginal selects the derivative order. -/
structure Orders where
  localOrder : ℕ
  jointTerms : Fin 3 → ℕ
  marginals : Fin 4 → MarginalOrders

private def jointDensity (b : Rectangle) (hLo hHi : ℚ) (orders : Orders) (i : Fin 3) : Model :=
  let I := jointInterval b
  shortJointClosedQuadratureModel i hHi I.radius I.width I.center
    (orders.jointTerms i) orders.localOrder (spacingAxis hLo hHi) (jointOffset b)

private def joint (b : Rectangle) (hLo hHi : ℚ) (orders : Orders) : Model :=
  let density := jointDensity b hLo hHi orders
  let D₂ := (gapAxis b).mul (gapAxis b)
  (density 0).add (D₂.mul ((density 1).add (D₂.mul (density 2))))

private def marginal (b : Rectangle) (hLo hHi : ℚ) (orders : Orders) (i : Fin 4) (j : Fin 3) :
    Model :=
  let I := marginalInterval b i
  let m := orders.marginals i
  (marginalClosedQuadratureModel hHi I.radius I.width I.center j (m.terms j) orders.localOrder
    (spacingAxis hLo hHi) (marginalOffset b i)).widen
      (shortMarginalIntegratedMeshError hHi I.lo I.hi m.meshNeg m.meshPos j)

private def rateGap (b : Rectangle) (hLo hHi : ℚ) : Model :=
  neg (CompactTaylorModel.positiveRateGapModel (spacingAxis hLo hHi) (neg (lowerAxis b)))

private def decayInput (b : Rectangle) (hLo hHi : ℚ) : Model :=
  neg (((Model.ofRat 1).add (spacingAxis hLo hHi)).mul (lowerAxis b))

-- The degree-eight square-root candidate from CompactShortQuadratureFirstBox.
-- The residual check below supplies its error bound.
private def rootCandidate (m : Model) : Model :=
  let S : ℚ := scale
  let c := CompactTaylorModel.Model.center m
  let r := (Nat.sqrt (⌊c * S ^ 2⌋ : ℤ).toNat : ℚ) / S
  let δ := (m.sub (Model.ofRat c)).mul (Model.ofRat c⁻¹)
  (Model.horner [1, 1 / 2, -1 / 8, 1 / 16, -5 / 128, 7 / 256,
    -21 / 1024, 33 / 2048, -429 / 32768] δ).mul (Model.ofRat r)

private def radicand (b : Rectangle) (hLo hHi : ℚ) (orders : Orders) : Model :=
  (marginal b hLo hHi orders 2 0).mul (marginal b hLo hHi orders 3 0)

private def rootPolynomial (b : Rectangle) (hLo hHi : ℚ) (orders : Orders) :
    DimThree.Certificate.Sparse :=
  (rootCandidate (radicand b hLo hHi orders)).polynomial

private def inputs (b : Rectangle) (hLo hHi : ℚ) (orders : Orders) : ShortQuadratureScoreInputs :=
  let M := marginal b hLo hHi orders
  let A := radicand b hLo hHi orders
  let P := rootPolynomial b hLo hHi orders
  { lowerCoordinate := lowerAxis b
    gap := gapAxis b
    spacing := spacingAxis hLo hHi
    inverseLower := inverse (lowerAxis b)
    inverseUpper := inverse (upperAxis b)
    reflectedLowerSlope := (M 0 1).mul (inverse (M 0 0))
    reflectedUpperSlope := (M 1 1).mul (inverse (M 1 0))
    upperSlope := (M 2 1).mul (inverse (M 2 0))
    gapSlope := (M 3 1).mul (inverse (M 3 0))
    gapSecondRatio := (M 3 2).mul (inverse (M 3 0))
    inverseRateGap := inverse (rateGap b hLo hHi)
    decay := (decayInput b hLo hHi).centeredExp
    growth := (lowerAxis b).centeredExp
    joint := joint b hLo hHi orders
    upperMarginal := M 2 0
    gapMarginal := M 3 0
    gapMarginalDeriv := M 3 1
    root := CompactTaylorModel.radicalFrom A P (Nat.sqrt (A.lower.toNat * scale))
      (⟨P, 0⟩ : Model).lower.toNat }

/-- The computed enclosure for the exact scaled negative score on this subbox. -/
def scoreModel (b : Rectangle) (hLo hHi : ℚ) (orders : Orders) : Model :=
  (inputs b hLo hHi orders).score

private abbrev TaylorChecks (order terms : ℕ) (radius : ℚ) : Prop :=
  order ≤ terms ∧ 3 ≤ terms ∧ 2 * radius < (terms : ℚ) - 2

private abbrev MeshChecks (m : MarginalOrders) (I : Interval) : Prop :=
  2 ≤ m.meshNeg ∧ 2 ≤ m.meshPos ∧
    |I.lo| / (m.meshNeg.succ : ℚ) < 1 ∧ |2 * I.hi| / (m.meshPos.succ : ℚ) < 1

/-- Finite rational, integer and model checks for the enclosure. A score endpoint
uses the existing `lowerCheck` separately. -/
structure Checks (b : Rectangle) (hLo hHi : ℚ) (orders : Orders) : Prop where
  jointTaylor : ∀ i : Fin 3, TaylorChecks orders.localOrder (orders.jointTerms i)
    (jointInterval b).radius
  marginalTaylor : ∀ (i : Fin 4) (j : Fin 3),
    TaylorChecks orders.localOrder ((orders.marginals i).terms j) (marginalInterval b i).radius
  mesh : ∀ i : Fin 4, MeshChecks (orders.marginals i) (marginalInterval b i)
  lowerPos : 0 < (lowerAxis b).lower
  upperPos : 0 < (upperAxis b).lower
  marginalPos : ∀ i : Fin 4, 0 < (marginal b hLo hHi orders i 0).lower
  rateGapPos : 0 < (rateGap b hLo hHi).lower
  rateGapSmall : ((spacingAxis hLo hHi).mul (neg (lowerAxis b))).argumentRadius ≤ 2
  decayOk : (decayInput b hLo hHi).expChecks
  growthOk : (lowerAxis b).expChecks
  rootPos : 0 < (⟨rootPolynomial b hLo hHi orders, 0⟩ : Model).lower

private theorem Interval.radius_bound (I : Interval) {x : ℝ}
    (hlo : (I.lo : ℝ) ≤ x) (hhi : x ≤ (I.hi : ℝ)) :
    |(I.center : ℝ)| + |x - (I.center : ℝ)| ≤ (I.radius : ℝ) := by
  simpa only [Interval.radius, Rat.cast_add, Rat.cast_abs] using
    add_le_add_right (I.offset_le hlo hhi) |(I.center : ℝ)|

private theorem jointDensity_sound {b : Rectangle} {hLo hHi : ℚ} {orders : Orders}
    (checks : Checks b hLo hHi orders) (i : Fin 3) {s t z x h : ℝ}
    (hb : InBox s t z) (hh : 0 ≤ h) (hmax : h ≤ (hHi : ℝ))
    (hH : (spacingAxis hLo hHi).Encloses s t z h)
    (hx : (jointOffset b).Encloses s t z (x - ((jointInterval b).center : ℝ)))
    (hlo : ((jointInterval b).lo : ℝ) ≤ x) (hhi : x ≤ ((jointInterval b).hi : ℝ)) :
    (jointDensity b hLo hHi orders i).Encloses s t z (shortJointClosedQuadrature i h x) := by
  let I := jointInterval b
  obtain ⟨horder, hterms, hratio⟩ := checks.jointTaylor i
  have hm := shortJointClosedQuadratureModel_sound (center := I.center) (radius := I.radius)
    (width := I.width) i hb hH hx hh hmax horder hterms
    (I.radius_bound hlo hhi) (I.offset_le hlo hhi) (by exact_mod_cast hratio)
  simpa only [I, jointDensity, add_sub_cancel] using hm

private theorem marginal_sound {b : Rectangle} {hLo hHi : ℚ} {orders : Orders}
    (checks : Checks b hLo hHi orders) (i : Fin 4) (j : Fin 3) {p : ℕ}
    (hp : 0 < p) {s t z x : ℝ} (hb : InBox s t z)
    (hH : (spacingAxis hLo hHi).Encloses s t z (3 / (p : ℝ)))
    (hmax : 3 / (p : ℝ) ≤ (hHi : ℝ))
    (hx : (marginalOffset b i).Encloses s t z (x - ((marginalInterval b i).center : ℝ)))
    (hlo : ((marginalInterval b i).lo : ℝ) ≤ x) (hhi : x ≤ ((marginalInterval b i).hi : ℝ)) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    (marginal b hLo hHi orders i j).Encloses s t z
      (iteratedDeriv (j : ℕ) (fun a ↦ (J * compactKappa p) * compactZ p a) x) := by
  let I := marginalInterval b i
  let m := orders.marginals i
  obtain ⟨horder, hterms, hratio⟩ := checks.marginalTaylor i j
  obtain ⟨hmNeg, hmPos, hrNeg, hrPos⟩ := checks.mesh i
  have hm := marginalClosedQuadratureModel_widen_integratedMeshError_sound
    (center := I.center) (width := I.width) (radius := I.radius) (lo := I.lo) (hi := I.hi)
    (mNeg := m.meshNeg) (mPos := m.meshPos) j hb hp hH hx hmax horder hterms
    (I.radius_bound hlo hhi) (I.offset_le hlo hhi) (by exact_mod_cast hratio)
    (by simpa only [I, add_sub_cancel] using hlo) (by simpa only [I, add_sub_cancel] using hhi)
    hmNeg hmPos (by exact_mod_cast hrNeg) (by exact_mod_cast hrPos)
  simpa only [I, m, marginal, add_sub_cancel] using hm

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
/-- A checked fixed-point lower endpoint bounds the exact short quadrature score
at every point of the subbox with spacing `3 / p`. -/
theorem score_lower_of_checks {b : Rectangle} {hLo hHi : ℚ} {orders : Orders}
    {degree : ℕ} {endpoint : ℚ} (checks : Checks b hLo hHi orders)
    (hscore : lowerCheck (scoreModel b hLo hHi orders) degree endpoint = true)
    {p : ℕ} {u v : ℝ} (hp : 11 ≤ p) (hvalid : b.Valid) (hpoint : b.Contains u (v - u))
    (hwidth : hLo < hHi) (hhLo : (hLo : ℝ) ≤ 3 / (p : ℝ))
    (hhHi : 3 / (p : ℝ) ≤ (hHi : ℝ)) :
    (endpoint : ℝ) / (scale : ℝ) ≤ shortQuadratureNegativeScore p u v := by
  let d := v - u
  let h : ℝ := 3 / (p : ℝ)
  let s := (lowerInterval b).normalize u
  let t := (gapInterval b).normalize d
  let z := (Interval.mk hLo hHi).normalize h
  let J := (3 + h) * (3 + 2 * h) / 2
  let q (x : ℝ) := (J * compactKappa p) * compactZ p x
  let M := marginal b hLo hHi orders
  obtain ⟨huLo, huHi, hdLo, hdHi⟩ := hpoint
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 < h := by dsimp only [h]; positivity
  have hu₀ : 1 / 2 ≤ u := by
    have h : (((1 / 2 : ℚ)) : ℝ) ≤ (b.uLo : ℝ) := by exact_mod_cast hvalid.1.1
    push_cast at h
    exact h.trans huLo
  have hb : InBox s t z :=
    ⟨(lowerInterval b).normalize_le hvalid.1.2.1 huLo huHi,
      (gapInterval b).normalize_le hvalid.2.2.1 hdLo hdHi,
      (Interval.mk hLo hHi).normalize_le hwidth hhLo hhHi⟩
  have hs : s * ((lowerInterval b).width : ℝ) = u - ((lowerInterval b).center : ℝ) :=
    (lowerInterval b).normalize_mul u hvalid.1.2.1
  have ht : t * ((gapInterval b).width : ℝ) = d - ((gapInterval b).center : ℝ) :=
    (gapInterval b).normalize_mul d hvalid.2.2.1
  have hz : z * ((Interval.mk hLo hHi).width : ℝ) = h - ((Interval.mk hLo hHi).center : ℝ) :=
    (Interval.mk hLo hHi).normalize_mul h hwidth
  have hU : (lowerAxis b).Encloses s t z u := (lowerInterval b).axis_sound 0 hb hs
  have hD : (gapAxis b).Encloses s t z d := (gapInterval b).axis_sound 1 hb ht
  have hH : (spacingAxis hLo hHi).Encloses s t z h := (Interval.mk hLo hHi).axis_sound 2 hb hz
  have hV : (upperAxis b).Encloses s t z v := by
    simpa only [upperAxis, d, add_sub_cancel] using Model.add_sound hU hD
  have hxU := (lowerInterval b).offset_sound 0 hb hs
  have hxD := (gapInterval b).offset_sound 1 hb ht
  have hxV : (upperOffset b).Encloses s t z (v - ((upperInterval b).center : ℝ)) := by
    have heq : (u - ((lowerInterval b).center : ℝ)) + (d - ((gapInterval b).center : ℝ)) =
        v - ((upperInterval b).center : ℝ) := by
      dsimp only [upperInterval, lowerInterval, gapInterval, Interval.center, d]
      push_cast
      ring
    have hm := Model.add_sound hxU hxD
    rw [heq] at hm
    exact hm
  have hvLo : ((upperInterval b).lo : ℝ) ≤ v := by
    simp only [upperInterval, Rat.cast_add]
    linarith only [huLo, hdLo]
  have hvHi : v ≤ ((upperInterval b).hi : ℝ) := by
    simp only [upperInterval, Rat.cast_add]
    linarith only [huHi, hdHi]
  let arg : Fin 4 → ℝ := ![-u, -v, v, d]
  have hmarginal (i : Fin 4) (j : Fin 3) :
      (M i j).Encloses s t z (iteratedDeriv (j : ℕ) q (arg i)) := by
    apply marginal_sound checks i j hp₀ hb hH hhHi
    all_goals fin_cases i
    · change (neg ((lowerInterval b).offset 0)).Encloses s t z
        (-u - (((lowerInterval b).reflect.center : ℚ) : ℝ))
      have heq : -u - (((lowerInterval b).reflect.center : ℚ) : ℝ) =
          -(u - ((lowerInterval b).center : ℝ)) := by rw [Interval.reflect_center]; ring
      rw [heq]
      exact neg_sound hxU
    · change (neg (upperOffset b)).Encloses s t z
        (-v - (((upperInterval b).reflect.center : ℚ) : ℝ))
      have heq : -v - (((upperInterval b).reflect.center : ℚ) : ℝ) =
          -(v - ((upperInterval b).center : ℝ)) := by rw [Interval.reflect_center]; ring
      rw [heq]
      exact neg_sound hxV
    · exact hxV
    · exact hxD
    · change ((-b.uHi : ℚ) : ℝ) ≤ -u
      simpa only [Rat.cast_neg] using neg_le_neg huHi
    · change ((-(upperInterval b).hi : ℚ) : ℝ) ≤ -v
      simpa only [Rat.cast_neg] using neg_le_neg hvHi
    · exact hvLo
    · exact hdLo
    · change -u ≤ ((-b.uLo : ℚ) : ℝ)
      simpa only [Rat.cast_neg] using neg_le_neg huLo
    · change -v ≤ ((-(upperInterval b).lo : ℚ) : ℝ)
      simpa only [Rat.cast_neg] using neg_le_neg hvLo
    · exact hvHi
    · exact hdHi
  have hmid : (jointOffset b).Encloses s t z
      (-((u + v) / 2) - ((jointInterval b).center : ℝ)) := by
    have hhalf := Model.affineCoordinate_sound hb 1 0 ((gapInterval b).width / 2)
    change (Model.affineCoordinate 1 0 ((gapInterval b).width / 2)).Encloses s t z
      (((0 : ℚ) : ℝ) + t * ((((gapInterval b).width / 2 : ℚ)) : ℝ)) at hhalf
    norm_num only [Rat.cast_zero, zero_add, Rat.cast_div, Rat.cast_ofNat] at hhalf
    have heq : -(u - ((lowerInterval b).center : ℝ) + t * ((gapInterval b).width / 2)) =
        -((u + v) / 2) - ((jointInterval b).center : ℝ) := by
      rw [show t * (((gapInterval b).width : ℝ) / 2) =
        (t * ((gapInterval b).width : ℝ)) / 2 by ring, ht]
      dsimp only [jointInterval, lowerInterval, gapInterval, Interval.reflect, Interval.center, d]
      push_cast
      ring
    have hm := neg_sound (Model.add_sound hxU hhalf)
    rw [heq] at hm
    exact hm
  have hmidLo : ((jointInterval b).lo : ℝ) ≤ -((u + v) / 2) := by
    simp only [jointInterval, Interval.reflect, Rat.cast_add, Rat.cast_div, Rat.cast_neg]
    linarith only [huHi, hdHi]
  have hmidHi : -((u + v) / 2) ≤ ((jointInterval b).hi : ℝ) := by
    simp only [jointInterval, Interval.reflect, Rat.cast_add, Rat.cast_div, Rat.cast_neg]
    linarith only [huLo, hdLo]
  have hDensity (i : Fin 3) :=
    jointDensity_sound checks i hb hh.le hhHi hH hmid hmidLo hmidHi
  have hJoint : (joint b hLo hHi orders).Encloses s t z
      (J * shortJointFourthQuadrature h ((u + v) / 2) d) :=
    shortJointFourthQuadrature_model_sound hb hh.le hD (hDensity 0) (hDensity 1) (hDensity 2)
  have hRate : (rateGap b hLo hHi).Encloses s t z (upperTailGap h u) := by
    unfold rateGap
    have hm := neg_sound (CompactTaylorModel.positiveRateGapModel_sound hb hH (neg_sound hU)
      hh.ne' (show -u ≠ 0 by linarith) checks.rateGapSmall)
    convert hm using 1
    unfold upperTailGap
    rw [mul_neg, ← neg_div]
    ring
  have hC (a : ℚ) := Model.ofRat_sound a s t z
  have hDecay : (decayInput b hLo hHi).Encloses s t z (-(1 + h) * u) := by
    simpa only [decayInput, Rat.cast_one, neg_mul] using neg_sound
      (Model.mul_sound hb (Model.add_sound (hC 1) hH) hU)
  have hq₀ (i : Fin 4) : (M i 0).Encloses s t z (q (arg i)) := by
    simpa only [Fin.val_zero, iteratedDeriv_zero] using hmarginal i 0
  have hq₁ (i : Fin 4) : (M i 1).Encloses s t z (deriv q (arg i)) := by
    simpa only [Fin.val_one, iteratedDeriv_one] using hmarginal i 1
  have hradicand : (radicand b hLo hHi orders).Encloses s t z (q v * q d) :=
    Model.mul_sound hb (hq₀ 2) (hq₀ 3)
  have hqpos (i : Fin 4) : 0 < q (arg i) :=
    (div_pos (by exact_mod_cast checks.marginalPos i) scale_real_pos).trans_le
      (Model.lower_sound hb (hq₀ i))
  have hroot : (inputs b hLo hHi orders).root.Encloses s t z (Real.sqrt (q v * q d)) :=
    radicalFrom_nonneg_sound hb hradicand (mul_nonneg (hqpos 2).le (hqpos 3).le)
      (rootPolynomial b hLo hHi orders) checks.rootPos
  have hslope {P Q : Model} {x y : ℝ} (hP : P.Encloses s t z x) (hQ : Q.Encloses s t z y)
      (hpos : 0 < Q.lower) : (P.mul (inverse Q)).Encloses s t z (x / y) := by
    simpa only [div_eq_mul_inv, one_mul] using Model.mul_sound hb hP (inverse_sound hb hQ hpos)
  have hbound : (scoreModel b hLo hHi orders).Encloses s t z
      (shortQuadratureNegativeScore p u v) := by
    refine ShortQuadratureScoreInputs.score_sound (m := inputs b hLo hHi orders)
      (p := p) (u := u) (v := v) hb hU hD hH
      (inverse_sound hb hU checks.lowerPos) (inverse_sound hb hV checks.upperPos)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hJoint (hq₀ 2) (hq₀ 3) (hq₁ 3) hroot
    · exact hslope (hq₁ 0) (hq₀ 0) (checks.marginalPos 0)
    · exact hslope (hq₁ 1) (hq₀ 1) (checks.marginalPos 1)
    · exact hslope (hq₁ 2) (hq₀ 2) (checks.marginalPos 2)
    · exact hslope (hq₁ 3) (hq₀ 3) (checks.marginalPos 3)
    · exact hslope (hmarginal 3 2) (hq₀ 3) (checks.marginalPos 3)
    · exact inverse_sound hb hRate checks.rateGapPos
    · exact Model.expChecks_sound hb hDecay checks.decayOk
    · exact Model.expChecks_sound hb hU checks.growthOk
  exact lowerCheck_sound hb hbound hscore

/-- A positive finite lower endpoint certifies the exact score on a single subbox. -/
theorem score_pos_of_checks {b : Rectangle} {hLo hHi : ℚ} {orders : Orders}
    {degree : ℕ} {endpoint : ℚ} (checks : Checks b hLo hHi orders)
    (hscore : lowerCheck (scoreModel b hLo hHi orders) degree endpoint = true)
    (hpos : 0 < endpoint)
    {p : ℕ} {u v : ℝ} (hp : 11 ≤ p) (hvalid : b.Valid) (hpoint : b.Contains u (v - u))
    (hwidth : hLo < hHi) (hhLo : (hLo : ℝ) ≤ 3 / (p : ℝ))
    (hhHi : 3 / (p : ℝ) ≤ (hHi : ℝ)) :
    0 < shortQuadratureNegativeScore p u v :=
  (div_pos (by exact_mod_cast hpos) scale_real_pos).trans_le
    (score_lower_of_checks checks hscore hp hvalid hpoint hwidth hhLo hhHi)

/-- The existing rectangle cover dispatches to local certificates for any choice of
spacing subintervals that supplies a checked subbox at `3 / p` in each leaf. -/
theorem logKernel_mixed_lt_of_grid_checks {p : ℕ} {u v : ℝ} (hp : 11 ≤ p)
    (huLo : 1 / 2 ≤ u) (huHi : u ≤ 4) (huv : u < v) (hdHi : v - u ≤ 1)
    (certify : ∀ leaf ∈ CompactTaylorModel.ShortTangentGrid.leaves,
      ∃ (hLo hHi : ℚ) (orders : Orders) (degree : ℕ) (endpoint : ℚ),
        hLo < hHi ∧ (hLo : ℝ) ≤ 3 / (p : ℝ) ∧ 3 / (p : ℝ) ≤ (hHi : ℝ) ∧
          Checks leaf.box hLo hHi orders ∧ 0 < endpoint ∧
          lowerCheck (scoreModel leaf.box hLo hHi orders) degree endpoint = true) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  obtain ⟨leaf, hm, hpoint, hvalid⟩ :=
    CompactTaylorModel.ShortTangentGrid.exists_leaf huLo huHi (sub_nonneg.mpr huv.le) hdHi
  obtain ⟨hLo, hHi, orders, degree, endpoint, hwidth, hhLo, hhHi, checks, hpos, hscore⟩ :=
    certify leaf hm
  exact logKernel_mixed_neg_of_shortQuadratureNegativeScore hp huLo huv hdHi
    (score_pos_of_checks checks hscore hpos hp hvalid hpoint hwidth hhLo hhHi)

end RefinedBMV.PositiveCenter.CompactShortQuadratureBox
