/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailBernsteinReplay
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Taylor enclosures for the Bernstein coefficients of the joint sign. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailBernstein

/-! Enclose the ordinary polynomial coefficients before applying the known Bernstein transform. -/

open Polynomial

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

open private constant from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailBernstein
open private geometricValue geometricDerivative lossValue lossDerivative from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailJointScore
open private CompactMiddleBox.affine_coordinates CompactMiddleBox.gapInverseCandidate from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

private abbrev Coefficients := Array Model

private def coefficientAt (a : Coefficients) (i : ℕ) : Model := a.getD i Model.zero

private def EnclosesCoefficients (M : Coefficients) (P : ℂ[X]) (s t w : ℝ) : Prop :=
  ∀ i, (coefficientAt M i).Encloses s t w (P.coeff i).re ∧ (P.coeff i).im = 0

private theorem coefficientAt_ofFn {n i : ℕ} (f : Fin n → Model) :
    coefficientAt (Array.ofFn f) i = if hi : i < n then f ⟨i, hi⟩ else Model.zero := by
  rw [coefficientAt, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split <;> rfl

private theorem enclosesArray {n : ℕ} {f : Fin n → Model} {P : ℂ[X]} {s t w : ℝ}
    (hbelow : ∀ i : Fin n, (f i).Encloses s t w (P.coeff i).re ∧ (P.coeff i).im = 0)
    (habove : ∀ i ≥ n, P.coeff i = 0) :
    EnclosesCoefficients (Array.ofFn f) P s t w := by
  intro i
  rw [coefficientAt_ofFn]
  by_cases hi : i < n
  · simpa only [dite_eq_left hi] using hbelow ⟨i, hi⟩
  · simp only [dite_eq_right hi, habove i (Nat.le_of_not_gt hi), Complex.zero_re, Complex.zero_im,
      and_true]
    exact Model.zero_sound s t w

private theorem coeff_zero_of_size_le {a : Coefficients} {P : ℂ[X]} {s t w : ℝ}
    (ha : EnclosesCoefficients a P s t w) {i : ℕ} (hi : a.size ≤ i) : P.coeff i = 0 := by
  have hr := (ha i).1
  rw [coefficientAt, Array.getD_eq_getD_getElem?, getElem?_neg a i (not_lt.mpr hi)] at hr
  apply Complex.ext
  · simpa [Model.Encloses, Model.zero, Model.eval, DimThree.Certificate.Sparse.eval,
      DimThree.evalTerms] using hr
  · simpa using (ha i).2

private def monomialModel (n : ℕ) (c : Model) : Coefficients :=
  Array.ofFn (n := n + 1) fun i ↦ if i.val = n then c else Model.zero

private theorem monomialModel_sound {n : ℕ} {M : Model} {s t w a : ℝ}
    (hM : M.Encloses s t w a) :
    EnclosesCoefficients (monomialModel n M) (Polynomial.monomial n (a : ℂ)) s t w := by
  apply enclosesArray
  · intro i
    by_cases hi : i.val = n
    · simpa [hi, coeff_monomial] using hM
    · simpa [coeff_monomial, hi, Ne.symm hi] using Model.zero_sound s t w
  · intro i hi
    simp [coeff_monomial, show n ≠ i by omega]

private def addModels (a b : Coefficients) : Coefficients :=
  Array.ofFn (n := max a.size b.size) fun i ↦ (coefficientAt a i).add (coefficientAt b i)

private def subModels (a b : Coefficients) : Coefficients :=
  Array.ofFn (n := max a.size b.size) fun i ↦ (coefficientAt a i).sub (coefficientAt b i)

private def mulModels (a b : Coefficients) : Coefficients :=
  Array.ofFn (n := a.size + b.size - 1) fun i ↦
    Model.sum (i.val + 1) fun j ↦
      if j < a.size ∧ i.val - j < b.size then
        (coefficientAt a j).mul (coefficientAt b (i - j))
      else Model.zero

private theorem addModels_sound {a b : Coefficients} {P Q : ℂ[X]} {s t w : ℝ}
    (ha : EnclosesCoefficients a P s t w) (hb : EnclosesCoefficients b Q s t w) :
    EnclosesCoefficients (addModels a b) (P + Q) s t w := by
  apply enclosesArray
  · intro i
    simpa only [coeff_add, Complex.add_re, Complex.add_im, (ha _).2, (hb _).2,
      add_zero, and_true] using Model.add_sound (ha i).1 (hb i).1
  · intro i hi
    rw [coeff_add, coeff_zero_of_size_le ha (by omega), coeff_zero_of_size_le hb (by omega),
      add_zero]

private theorem subModels_sound {a b : Coefficients} {P Q : ℂ[X]} {s t w : ℝ}
    (ha : EnclosesCoefficients a P s t w) (hb : EnclosesCoefficients b Q s t w) :
    EnclosesCoefficients (subModels a b) (P - Q) s t w := by
  apply enclosesArray
  · intro i
    simpa only [coeff_sub, Complex.sub_re, Complex.sub_im, (ha _).2, (hb _).2,
      sub_zero, and_true] using Model.sub_sound (ha i).1 (hb i).1
  · intro i hi
    rw [coeff_sub, coeff_zero_of_size_le ha (by omega), coeff_zero_of_size_le hb (by omega),
      sub_zero]

private theorem mulModels_sound {a b : Coefficients} {P Q : ℂ[X]} {s t w : ℝ}
    (hbox : InBox s t w)
    (ha : EnclosesCoefficients a P s t w) (hb : EnclosesCoefficients b Q s t w) :
    EnclosesCoefficients (mulModels a b) (P * Q) s t w := by
  classical
  apply enclosesArray
  · intro i
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    constructor
    · rw [Complex.re_sum]
      simp only [Complex.mul_re, (ha _).2, (hb _).2, mul_zero, sub_zero]
      apply Model.sum_sound (i.val + 1)
      intro j _
      split
      · exact Model.mul_sound hbox (ha j).1 (hb (i - j)).1
      · rename_i h
        by_cases hleft : j < a.size
        · have hright : b.size ≤ i.val - j := by omega
          rw [coeff_zero_of_size_le hb hright, Complex.zero_re, mul_zero]
          exact Model.zero_sound s t w
        · rw [coeff_zero_of_size_le ha (Nat.le_of_not_gt hleft), Complex.zero_re, zero_mul]
          exact Model.zero_sound s t w
    · rw [Complex.im_sum]
      simp only [Complex.mul_im, (ha _).2, (hb _).2, mul_zero, zero_mul, add_zero,
        Finset.sum_const_zero]
  · intro i hi
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hleft : a.size ≤ j
    · rw [coeff_zero_of_size_le ha hleft, zero_mul]
    · rw [coeff_zero_of_size_le hb (by omega : b.size ≤ i - j), mul_zero]

private def bernsteinModel (n i : ℕ) (M : Coefficients) : Model :=
  Model.sum (n + 1) fun j ↦
    if j ≤ i then
      (coefficientAt M j).mul (Model.ofRat ((i.choose j : ℚ) / (n.choose j : ℚ)))
    else Model.zero

private theorem bernsteinModel_sound {n i : ℕ} {M : Coefficients} {P : ℂ[X]} {s t w : ℝ}
    (hbox : InBox s t w) (hM : EnclosesCoefficients M P s t w) :
    (bernsteinModel n i M).Encloses s t w (bernsteinCoefficient n i P).re := by
  unfold bernsteinCoefficient
  rw [Complex.re_sum]
  apply Model.sum_sound (n + 1)
  intro j hj
  by_cases hj' : j ≤ i
  swap
  · rw [ite_eq_right hj', Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj'), Nat.cast_zero,
      mul_zero, zero_div, Complex.zero_re]
    exact Model.zero_sound s t w
  rw [ite_eq_left hj']
  have Hj := Model.mul_sound hbox (hM j).1
    (Model.ofRat_sound ((i.choose j : ℚ) / (n.choose j : ℚ)) s t w)
  have hreal : P.coeff j = ((P.coeff j).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using (hM j).2
  rw [hreal]
  convert Hj using 1
  push_cast
  rw [show (i.choose j : ℂ) = ((i.choose j : ℝ) : ℂ) by norm_cast,
    show (n.choose j : ℂ) = ((n.choose j : ℝ) : ℂ) by norm_cast]
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv,
    mul_assoc]

private def constantModel (a : Model) : Coefficients := monomialModel 0 a

private theorem constantModel_sound {M : Model} {s t w a : ℝ}
    (hM : M.Encloses s t w a) : EnclosesCoefficients (constantModel M) (constant a) s t w := by
  simpa only [constantModel, constant, monomial_zero_left] using monomialModel_sound (n := 0) hM

private def negModels (a : Coefficients) : Coefficients :=
  Array.ofFn (n := a.size) fun i ↦ Model.zero.sub (coefficientAt a i)

private theorem negModels_sound {a : Coefficients} {P : ℂ[X]} {s t w : ℝ}
    (ha : EnclosesCoefficients a P s t w) : EnclosesCoefficients (negModels a) (-P) s t w := by
  apply enclosesArray
  · intro i
    simpa only [coeff_neg, Complex.neg_re, Complex.neg_im, (ha _).2, neg_zero,
      zero_sub, and_true] using Model.sub_sound (Model.zero_sound s t w) (ha i).1
  · intro i hi
    rw [coeff_neg, coeff_zero_of_size_le ha hi, neg_zero]

private def oneModel : Coefficients := constantModel (Model.ofRat 1)

private theorem oneModel_sound (s t w : ℝ) : EnclosesCoefficients oneModel 1 s t w := by
  simpa [oneModel, constant] using constantModel_sound (Model.ofRat_sound 1 s t w)

private structure BernsteinScalars (α : Type) where
  n : α
  kF : α
  c : α
  weight : α
  scaleWeight : α
  curvature : α
  reflected : α
  linearGeom : α
  linearGeomDerivative : α
  linearLoss : α
  linearLossDerivative : α
  cutoff : α

-- These are the scalar inputs of the independent rational replay.
private def bernsteinScalarModels (H F InvF X R : Model) : BernsteinScalars Model :=
  let one := Model.ofRat 1
  let two := Model.ofRat 2
  let three := Model.ofRat 3
  let half := Model.ofRat (1 / 2)
  let n := three.add H
  let k := three.add (two.mul H)
  let c := (n.mul k).mul half
  let kF := k.mul F
  let decay := ((X.mul X).mul X).mul R
  let E := decay.mul R
  let W := (((kF.sub one).add E).sub (((c.mul F).mul F).mul X))
  let S := (two.mul F).mul W
  let curve := (((one.add H).mul F).mul (kF.sub (Model.ofRat 4))).add two
    |>.sub ((two.mul (F.add one)).mul E)
  let Z := ((two.add H).mul S).sub curve
  let D₀ := (((Model.ofRat (3 / 2)).mul (one.add H)).sub InvF).add
    (((n.mul half).add InvF).mul E)
  let D₁ := (R.sub (((one.add (n.mul F)).add ((c.mul F).mul F)).mul E))
    |>.mul (InvF.mul InvF)
  let L₀ := (one.sub (decay.mul (one.add (n.mul F)))).mul half
  let L₁ := (c.mul F).mul decay
  let cutoff := ((Model.ofRat (4 / 13)).sub (H.mul half)).add
    (((Model.ofRat (13 / 48)).mul H).mul H)
  ⟨n, kF, c, W, S, curve, Z, D₀, D₁, L₀, L₁, cutoff⟩

private noncomputable def bernsteinScalars (h u : ℝ) : BernsteinScalars ℝ :=
  let F := upperTailGap h u
  let k := 3 + 2 * h
  let c := (3 + h) * k / 2
  let W := shortGapWeight h u
  let S := 2 * F * W
  let curve := (1 + h) * F * (k * F - 4) + 2 - 2 * (F + 1) * Real.exp (-(k * u))
  ⟨3 + h, k * F, c, W, S, curve, (2 + h) * S - curve,
    geometricValue h u, geometricDerivative h u, lossValue h u, lossDerivative h u,
    middleTailSlopeCutoff h⟩

private theorem bernsteinScalarModels_sound {H F InvF X R : Model} {h u s t w : ℝ}
    (hb : InBox s t w) (hh : 0 < h) (hu : 0 < u)
    (hH : H.Encloses s t w h) (hF : F.Encloses s t w (upperTailGap h u))
    (hInvF : InvF.Encloses s t w (upperTailGap h u)⁻¹)
    (hX : X.Encloses s t w (Real.exp (-u)))
    (hR : R.Encloses s t w (Real.exp (-(h * u)))) :
    let m := bernsteinScalarModels H F InvF X R
    let a := bernsteinScalars h u
    m.n.Encloses s t w a.n ∧ m.kF.Encloses s t w a.kF ∧ m.c.Encloses s t w a.c ∧
    m.weight.Encloses s t w a.weight ∧ m.scaleWeight.Encloses s t w a.scaleWeight ∧
    m.curvature.Encloses s t w a.curvature ∧ m.reflected.Encloses s t w a.reflected ∧
    m.linearGeom.Encloses s t w a.linearGeom ∧
    m.linearGeomDerivative.Encloses s t w a.linearGeomDerivative ∧
    m.linearLoss.Encloses s t w a.linearLoss ∧
    m.linearLossDerivative.Encloses s t w a.linearLossDerivative ∧
    m.cutoff.Encloses s t w a.cutoff := by
  let f := upperTailGap h u
  let x := Real.exp (-u)
  let r := Real.exp (-(h * u))
  let n : ℝ := 3 + h
  let k : ℝ := 3 + 2 * h
  let c := n * k / 2
  let e := Real.exp (-(k * u))
  let m := bernsteinScalarModels H F InvF X R
  let a := bernsteinScalars h u
  have hf : 0 < f := tail_gap_pos hh hu
  have hDecay : x * x * x * r = Real.exp (-((3 + h) * u)) := by
    simp only [x, r, ← Real.exp_add]
    congr 1
    ring
  have hE : x * x * x * r * r = e := by
    simp only [x, r, e, k, ← Real.exp_add]
    congr 1
    ring
  have hr : r = 1 - h * f := by
    have eq : 1 - r = h * f := tail_gap_factor (t := u) hh
    linarith only [eq]
  have hSlope : upperTailSlope h u = f⁻¹ - h :=
    CompactGap.upperTailSlope_eq_inv_gap_sub_rate hh hu
  have rat (b : ℚ) := Model.ofRat_sound b s t w
  have one : (Model.ofRat 1).Encloses s t w (1 : ℝ) := by simpa using rat 1
  have two : (Model.ofRat 2).Encloses s t w (2 : ℝ) := by simpa using rat 2
  have three : (Model.ofRat 3).Encloses s t w (3 : ℝ) := by simpa using rat 3
  have four : (Model.ofRat 4).Encloses s t w (4 : ℝ) := by simpa using rat 4
  have half : (Model.ofRat (1 / 2)).Encloses s t w (1 / 2 : ℝ) := by simpa using rat (1 / 2)
  have hn : m.n.Encloses s t w n := Model.add_sound three hH
  have hk := Model.add_sound three (Model.mul_sound hb two hH)
  have hc : m.c.Encloses s t w c := by
    rw [show c = n * (3 + 2 * h) * (1 / 2) by dsimp only [c, k]; ring]
    exact Model.mul_sound hb (Model.mul_sound hb hn hk) half
  have hkF : m.kF.Encloses s t w (k * f) := Model.mul_sound hb hk hF
  have hDecayModel := Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb hX hX) hX) hR
  have hEModel := Model.mul_sound hb hDecayModel hR
  change Model.Encloses _ s t w (x * x * x * r * r) at hEModel
  rw [hE] at hEModel
  have hw : m.weight.Encloses s t w a.weight := by
    have hw' := Model.sub_sound (Model.add_sound (Model.sub_sound hkF one) hEModel)
      (Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb hc hF) hF) hX)
    change m.weight.Encloses s t w (k * f - 1 + e - c * f * f * x) at hw'
    rw [show k * f - 1 + e - c * f * f * x = a.weight by
      dsimp only [a, bernsteinScalars, shortGapWeight, x, f, e, k, c, n]
      ring] at hw'
    exact hw'
  have hS : m.scaleWeight.Encloses s t w a.scaleWeight :=
    Model.mul_sound hb (Model.mul_sound hb two hF) hw
  have hCurve : m.curvature.Encloses s t w a.curvature :=
    Model.sub_sound
      (Model.add_sound (Model.mul_sound hb (Model.mul_sound hb (Model.add_sound one hH) hF)
        (Model.sub_sound hkF four)) two)
      (Model.mul_sound hb (Model.mul_sound hb two (Model.add_sound hF one)) hEModel)
  have hZ : m.reflected.Encloses s t w a.reflected :=
    Model.sub_sound (Model.mul_sound hb (Model.add_sound two hH) hS) hCurve
  have hThreeHalf : (Model.ofRat (3 / 2)).Encloses s t w (3 / 2 : ℝ) := by
    simpa using rat (3 / 2)
  have hD₀ : m.linearGeom.Encloses s t w a.linearGeom := by
    have hd := Model.add_sound (Model.sub_sound (Model.mul_sound hb hThreeHalf
      (Model.add_sound one hH)) hInvF)
      (Model.mul_sound hb (Model.add_sound (Model.mul_sound hb hn half) hInvF) hEModel)
    change m.linearGeom.Encloses s t w (3 / 2 * (1 + h) - f⁻¹ + (n * (1 / 2) + f⁻¹) * e) at hd
    rw [show 3 / 2 * (1 + h) - f⁻¹ + (n * (1 / 2) + f⁻¹) * e = a.linearGeom by
      dsimp only [a, bernsteinScalars, geometricValue]
      change _ = n * (1 + e) / 2 + h - (1 - e) / f
      rw [div_eq_mul_inv (1 - e)]
      dsimp only [n]
      ring] at hd
    exact hd
  have hD₁ : m.linearGeomDerivative.Encloses s t w a.linearGeomDerivative := by
    have hd := Model.mul_sound hb (Model.sub_sound hR (Model.mul_sound hb
      (Model.add_sound (Model.add_sound one (Model.mul_sound hb hn hF))
        (Model.mul_sound hb (Model.mul_sound hb hc hF) hF)) hEModel))
      (Model.mul_sound hb hInvF hInvF)
    change m.linearGeomDerivative.Encloses s t w
      ((r - (1 + n * f + c * f * f) * e) * (f⁻¹ * f⁻¹)) at hd
    rw [show (r - (1 + n * f + c * f * f) * e) * (f⁻¹ * f⁻¹) = a.linearGeomDerivative by
      dsimp only [a, bernsteinScalars, geometricDerivative]
      change _ = (upperTailSlope h u * (1 - e) - k * e) / f - k * n * e / 2
      rw [hSlope, hr]
      dsimp only [c, k, n]
      field_simp [hf.ne']
      ring] at hd
    exact hd
  change Model.Encloses _ s t w (x * x * x * r) at hDecayModel
  rw [hDecay] at hDecayModel
  have hL₀ : m.linearLoss.Encloses s t w a.linearLoss := by
    rw [show a.linearLoss = (1 - Real.exp (-((3 + h) * u)) * (1 + n * f)) * (1 / 2) by
      dsimp only [bernsteinScalars, a, lossValue, n, f]
      ring]
    exact Model.mul_sound hb (Model.sub_sound one (Model.mul_sound hb hDecayModel
      (Model.add_sound one (Model.mul_sound hb hn hF)))) half
  have hL₁ : m.linearLossDerivative.Encloses s t w a.linearLossDerivative :=
    Model.mul_sound hb (Model.mul_sound hb hc hF) hDecayModel
  have hCutoff : m.cutoff.Encloses s t w a.cutoff := by
    have ha : (Model.ofRat (4 / 13)).Encloses s t w (4 / 13 : ℝ) := by simpa using rat (4 / 13)
    have hb' : (Model.ofRat (13 / 48)).Encloses s t w (13 / 48 : ℝ) := by simpa using rat (13 / 48)
    have hbound := Model.add_sound (Model.sub_sound ha (Model.mul_sound hb hH half))
      (Model.mul_sound hb (Model.mul_sound hb hb' hH) hH)
    change m.cutoff.Encloses s t w ((4 / 13 : ℝ) - h * (1 / 2) + 13 / 48 * h * h) at hbound
    rw [show (4 / 13 : ℝ) - h * (1 / 2) + 13 / 48 * h * h = a.cutoff by
      dsimp only [a, bernsteinScalars, middleTailSlopeCutoff]
      ring] at hbound
    exact hbound
  exact ⟨hn, hkF, hc, hw, hS, hCurve, hZ, hD₀, hD₁, hL₀, hL₁, hCutoff⟩

local infixl:65 " +ₘ " => addModels
local infixl:65 " -ₘ " => subModels
local infixl:70 " *ₘ " => mulModels

private def bernsteinPolynomialModels (H F X : Model) (a : BernsteinScalars Model) :
    Coefficients × Coefficients × Coefficients × Coefficients :=
  let C := constantModel
  let q := monomialModel 1 a.cutoff
  let r := C H +ₘ q
  let A := C a.n +ₘ C (a.kF.sub (Model.ofRat 1)) *ₘ q
  let R := oneModel +ₘ C F *ₘ q
  let ρ := C X *ₘ R
  let ell := oneModel -ₘ q
  let η := q *ₘ r
  let M := (C a.reflected +ₘ q *ₘ C a.scaleWeight) *ₘ C a.linearLoss +ₘ
    C (a.scaleWeight.mul a.linearLossDerivative)
  let U := C ((a.reflected.mul a.linearGeom).add (a.scaleWeight.mul a.linearGeomDerivative))
    -ₘ r *ₘ M
  let V := η *ₘ (M +ₘ r *ₘ C (a.scaleWeight.mul a.linearLoss))
  let δ := oneModel -ₘ ρ
  let σ := oneModel -ₘ ρ *ₘ ρ
  let B := C a.curvature *ₘ (δ *ₘ δ) -ₘ ell *ₘ C a.scaleWeight *ₘ σ
  let cR := C a.c *ₘ R
  let T := cR *ₘ U -ₘ A *ₘ V
  let P := (cR -ₘ A *ₘ (oneModel +ₘ r)) *ₘ B +ₘ A *ₘ η *ₘ
    (C a.scaleWeight *ₘ σ -ₘ C (((Model.ofRat 2).mul F).mul X) *ₘ
      (C a.curvature *ₘ δ -ₘ C a.scaleWeight *ₘ ell *ₘ ρ))
  let q₂ := q *ₘ q
  let q₅ := q₂ *ₘ q₂ *ₘ q
  let N := C a.c *ₘ P -ₘ C (Model.ofRat (2 * (31 / 800) * (13 / 4) ^ 4)) *ₘ q₅ *ₘ T
    +ₘ C ((a.c.mul a.scaleWeight).mul (Model.ofRat (1 / 2000))) *ₘ A
  (negModels B, U, T, negModels N)

/-- Models in the order of the independent replay: (W), then the four
Bernstein lists of lengths 4, 3, 5 and 10. -/
def middleTailBernsteinModels (H F InvF X R : Model) :
    Model × (Fin 4 → Model) × (Fin 3 → Model) × (Fin 5 → Model) × (Fin 10 → Model) :=
  let a := bernsteinScalarModels H F InvF X R
  let m := bernsteinPolynomialModels H F X a
  (a.weight, fun i ↦ bernsteinModel 3 i m.1, fun i ↦ bernsteinModel 2 i m.2.1,
    fun i ↦ bernsteinModel 4 i m.2.2.1, fun i ↦ bernsteinModel 9 i m.2.2.2)

set_option maxHeartbeats 800000 in
-- The four coefficient expressions contain nested finite convolutions.
/-- The computed models enclose the weight and each of the 22 coefficients of the
exact gap-elimination polynomials. -/
theorem middleTailBernsteinModels_sound {H F InvF X R : Model} {h u s t w : ℝ}
    (hb : InBox s t w) (hh : 0 < h) (hu : 0 < u)
    (hH : H.Encloses s t w h) (hF : F.Encloses s t w (upperTailGap h u))
    (hInvF : InvF.Encloses s t w (upperTailGap h u)⁻¹)
    (hX : X.Encloses s t w (Real.exp (-u)))
    (hR : R.Encloses s t w (Real.exp (-(h * u)))) :
    let m := middleTailBernsteinModels H F InvF X R
    let p := middleTailBernsteinPolynomials h u
    m.1.Encloses s t w (shortGapWeight h u) ∧
      (∀ i : Fin 4, (m.2.1 i).Encloses s t w (bernsteinCoefficient 3 i p.1).re) ∧
      (∀ i : Fin 3, (m.2.2.1 i).Encloses s t w (bernsteinCoefficient 2 i p.2.1).re) ∧
      (∀ i : Fin 5, (m.2.2.2.1 i).Encloses s t w (bernsteinCoefficient 4 i p.2.2.1).re) ∧
      (∀ i : Fin 10, (m.2.2.2.2 i).Encloses s t w (bernsteinCoefficient 9 i p.2.2.2).re) := by
  obtain ⟨hn, hkF, hc, hw, hs, hcurve, hz, hd₀, hd₁, hl₀, hl₁, hcutoff⟩ :=
    bernsteinScalarModels_sound hb hh hu hH hF hInvF hX hR
  have mul {a b : Coefficients} {P Q : ℂ[X]}
      (ha : EnclosesCoefficients a P s t w) (hb' : EnclosesCoefficients b Q s t w) :=
    mulModels_sound hb ha hb'
  have mulScalar {a b : Model} {x y : ℝ}
      (ha : a.Encloses s t w x) (hb' : b.Encloses s t w y) := Model.mul_sound hb ha hb'
  have one : (Model.ofRat 1).Encloses s t w (1 : ℝ) := by
    simpa using Model.ofRat_sound 1 s t w
  have two : (Model.ofRat 2).Encloses s t w (2 : ℝ) := by
    simpa using Model.ofRat_sound 2 s t w
  have margin : (Model.ofRat (1 / 2000)).Encloses s t w (2000 : ℝ)⁻¹ := by
    simpa [div_eq_mul_inv] using Model.ofRat_sound (1 / 2000) s t w
  have beta : (Model.ofRat (2 * (31 / 800) * (13 / 4) ^ 4)).Encloses s t w
      (2 * ((31 / 800 : ℝ) * (13 / 4) ^ 4)) := by
    have eq : ((↑(2 * (31 / 800) * (13 / 4) ^ 4 : ℚ)) : ℝ) =
        2 * ((31 / 800 : ℝ) * (13 / 4) ^ 4) := by norm_num
    rw [← eq]
    exact Model.ofRat_sound _ s t w
  have q := monomialModel_sound (n := 1) hcutoff
  rw [← C_mul_X_eq_monomial] at q
  have r := addModels_sound (constantModel_sound hH) q
  have A := addModels_sound (constantModel_sound hn)
    (mul (constantModel_sound (Model.sub_sound hkF one)) q)
  have R' := addModels_sound (oneModel_sound s t w) (mul (constantModel_sound hF) q)
  have rho := mul (constantModel_sound hX) R'
  have ell := subModels_sound (oneModel_sound s t w) q
  have eta := mul q r
  have M := addModels_sound (mul (addModels_sound (constantModel_sound hz)
    (mul q (constantModel_sound hs))) (constantModel_sound hl₀))
    (constantModel_sound (mulScalar hs hl₁))
  have U := subModels_sound (constantModel_sound (Model.add_sound (mulScalar hz hd₀)
    (mulScalar hs hd₁))) (mul r M)
  have V := mul eta (addModels_sound M (mul r (constantModel_sound (mulScalar hs hl₀))))
  have δ := subModels_sound (oneModel_sound s t w) rho
  have σ := subModels_sound (oneModel_sound s t w) (mul rho rho)
  have B := subModels_sound (mul (constantModel_sound hcurve) (mul δ δ))
    (mul (mul ell (constantModel_sound hs)) σ)
  have cR := mul (constantModel_sound hc) R'
  have T := subModels_sound (mul cR U) (mul A V)
  have P := addModels_sound (mul (subModels_sound cR (mul A (addModels_sound
    (oneModel_sound s t w) r))) B)
    (mul (mul A eta) (subModels_sound (mul (constantModel_sound hs) σ)
      (mul (constantModel_sound (mulScalar (mulScalar two hF) hX))
        (subModels_sound (mul (constantModel_sound hcurve) δ)
          (mul (mul (constantModel_sound hs) ell) rho)))))
  have q₂ := mul q q
  have q₅ := mul (mul q₂ q₂) q
  have N := addModels_sound (subModels_sound (mul (constantModel_sound hc) P)
    (mul (mul (constantModel_sound beta) q₅) T))
    (mul (constantModel_sound (mulScalar (mulScalar hc hs) margin)) A)
  have pow_five (a : ℂ[X]) : a ^ 5 = a * a * (a * a) * a := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  refine ⟨hw, ?_, ?_, ?_, ?_⟩
  · intro i
    apply bernsteinModel_sound hb
    simpa only [bernsteinPolynomialModels, middleTailBernsteinPolynomials, bernsteinScalars,
      constant, pow_two] using negModels_sound B
  · intro i
    apply bernsteinModel_sound hb
    simpa only [bernsteinPolynomialModels, middleTailBernsteinPolynomials, bernsteinScalars,
      constant]
      using U
  · intro i
    apply bernsteinModel_sound hb
    simpa only [bernsteinPolynomialModels, middleTailBernsteinPolynomials, bernsteinScalars,
      constant]
      using T
  · intro i
    apply bernsteinModel_sound hb
    simpa only [bernsteinPolynomialModels, middleTailBernsteinPolynomials, bernsteinScalars,
      constant, pow_two, pow_five, div_eq_mul_inv] using negModels_sound N

/-- A positive common lower bound for the computed coefficient models gives the
four exact signs needed by the gap elimination theorem. -/
theorem middleTailGap_signs_of_replay {H F InvF X R : Model} {h u q s t w : ℝ} {lower : ℤ}
    (hb : InBox s t w) (hh : 0 < h) (hu : 0 < u)
    (hH : H.Encloses s t w h) (hF : F.Encloses s t w (upperTailGap h u))
    (hInvF : InvF.Encloses s t w (upperTailGap h u)⁻¹)
    (hX : X.Encloses s t w (Real.exp (-u)))
    (hR : R.Encloses s t w (Real.exp (-(h * u))))
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ middleTailSlopeCutoff h) (hQ : 0 < middleTailSlopeCutoff h)
    (hlower : 0 < lower)
    (hcheck :
      let m := middleTailBernsteinModels H F InvF X R
      (∀ i, lower ≤ (m.2.1 i).lower) ∧ (∀ i, lower ≤ (m.2.2.1 i).lower) ∧
      (∀ i, lower ≤ (m.2.2.2.1 i).lower) ∧ (∀ i, lower ≤ (m.2.2.2.2 i).lower)) :
    let B := middleTailGapPolynomials h u q
    B.upperSlopeCoefficient < 0 ∧ 0 < B.linearLoss ∧
      0 < B.decayCoefficient ∧ B.numerator < 0 := by
  have hl : (0 : ℝ) < (lower : ℝ) := by exact_mod_cast hlower
  obtain ⟨_, hC, hU, hT, hN⟩ := middleTailBernsteinModels_sound hb hh hu hH hF hInvF hX hR
  obtain ⟨hLC, hLU, hLT, hLN⟩ := hcheck
  have bound {m : Model} {x : ℝ} (hm : m.Encloses s t w x) (hL : lower ≤ m.lower) :
      (lower : ℝ) / (scale : ℝ) ≤ x :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hL) scale_real_pos.le).trans
      (Model.lower_sound hb hm)
  apply middleTailGap_signs_of_bernstein hq₀ hq₁ hQ (div_pos hl scale_real_pos)
  exact ⟨fun i hi ↦ bound (hC ⟨i, by omega⟩) (hLC ⟨i, by omega⟩),
    fun i hi ↦ bound (hU ⟨i, by omega⟩) (hLU ⟨i, by omega⟩),
    fun i hi ↦ bound (hT ⟨i, by omega⟩) (hLT ⟨i, by omega⟩),
    fun i hi ↦ bound (hN ⟨i, by omega⟩) (hLN ⟨i, by omega⟩)⟩

#print axioms middleTailBernsteinModels_sound
#print axioms middleTailGap_signs_of_replay


private structure ReplayBox where
  uLo : ℚ
  uHi : ℚ
  hLo : ℚ
  hHi : ℚ

namespace ReplayBox

private def Contains (b : ReplayBox) (h u : ℝ) : Prop :=
  (b.uLo : ℝ) ≤ u ∧ u ≤ (b.uHi : ℝ) ∧ (b.hLo : ℝ) ≤ h ∧ h ≤ (b.hHi : ℝ)

private def uModel (b : ReplayBox) : Model :=
  Model.affineCoordinate 0 ((b.uHi + b.uLo) / 2) ((b.uHi - b.uLo) / 2)

private def hModel (b : ReplayBox) : Model :=
  Model.affineCoordinate 1 ((b.hHi + b.hLo) / 2) ((b.hHi - b.hLo) / 2)

private def negU (b : ReplayBox) : Model := Model.zero.sub b.uModel
private def negHU (b : ReplayBox) : Model := b.hModel.mul b.negU
private def gapArgument (b : ReplayBox) : Model :=
  b.hModel.mul (b.uModel.mul (Model.ofRat (-1 / 2)))

private def gapModel (b : ReplayBox) : Model := middleGapModel b.hModel b.uModel

private def inverseGap (b : ReplayBox) (F : Model) : Model :=
  reciprocalFrom F (CompactMiddleBox.gapInverseCandidate b.hModel b.uModel
    ((b.uHi + b.uLo) / 2)) F.lower.toNat

private def allLowerPositive {n : ℕ} (m : Fin n → Model) : Bool :=
  (List.finRange n).all fun i ↦ decide (0 < (m i).lower)

private theorem lower_positive_of_all {n : ℕ} {m : Fin n → Model}
    (hc : allLowerPositive m = true) (i : Fin n) : 1 ≤ (m i).lower := by
  have h := List.all_eq_true.mp hc i (List.mem_finRange i)
  have hpos := of_decide_eq_true h
  omega

local instance (M : Model) : Decidable M.expChecks := by
  unfold Model.expChecks
  infer_instance

private def check (b : ReplayBox) : Bool :=
  if b.uLo < b.uHi ∧ b.hLo < b.hHi ∧ b.gapArgument.argumentRadius ≤ 2 ∧
      b.gapArgument.expChecks ∧ b.negU.expChecks ∧ b.negHU.expChecks then
    let F := b.gapModel
    if 0 < F.lower then
      let m := middleTailBernsteinModels b.hModel F (b.inverseGap F)
        b.negU.centeredExp b.negHU.centeredExp
      decide (0 < m.1.lower) && allLowerPositive m.2.1 && allLowerPositive m.2.2.1 &&
        allLowerPositive m.2.2.2.1 && allLowerPositive m.2.2.2.2
    else false
  else false

private theorem signs_of_check {b : ReplayBox} {h u q : ℝ}
    (hc : b.check = true) (hb : b.Contains h u) (hh : 0 < h) (hu : 0 < u)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ middleTailSlopeCutoff h) (hQ : 0 < middleTailSlopeCutoff h) :
    let B := middleTailGapPolynomials h u q
    B.upperSlopeCoefficient < 0 ∧ 0 < B.linearLoss ∧
      0 < B.decayCoefficient ∧ B.numerator < 0 := by
  unfold check at hc
  split at hc
  · rename_i hchecks
    obtain ⟨huw, hhw, hgSize, hgExp, hxExp, hrExp⟩ := hchecks
    dsimp only at hc
    split at hc
    · rename_i hFpos
      let s := (2 * u - ((b.uHi : ℝ) + b.uLo)) / ((b.uHi : ℝ) - b.uLo)
      let t := (2 * h - ((b.hHi : ℝ) + b.hLo)) / ((b.hHi : ℝ) - b.hLo)
      obtain ⟨hs, hsEq⟩ := CompactMiddleBox.affine_coordinates huw hb.1 hb.2.1
      obtain ⟨ht, htEq⟩ := CompactMiddleBox.affine_coordinates hhw hb.2.2.1 hb.2.2.2
      change |s| ≤ 1 at hs
      change |t| ≤ 1 at ht
      change u = ((b.uHi : ℝ) + b.uLo) / 2 + s * (((b.uHi : ℝ) - b.uLo) / 2) at hsEq
      change h = ((b.hHi : ℝ) + b.hLo) / 2 + t * (((b.hHi : ℝ) - b.hLo) / 2) at htEq
      have hcBox : InBox s t 0 := ⟨hs, ht, by norm_num⟩
      have hU : b.uModel.Encloses s t 0 u := by
        simpa only [uModel, show (![s, t, 0] : Fin 3 → ℝ) 0 = s by rfl,
          Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat, ← hsEq] using
          Model.affineCoordinate_sound hcBox 0 ((b.uHi + b.uLo) / 2) ((b.uHi - b.uLo) / 2)
      have hH : b.hModel.Encloses s t 0 h := by
        simpa only [hModel, show (![s, t, 0] : Fin 3 → ℝ) 1 = t by rfl,
          Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_ofNat, ← htEq] using
          Model.affineCoordinate_sound hcBox 1 ((b.hHi + b.hLo) / 2) ((b.hHi - b.hLo) / 2)
      have hF : b.gapModel.Encloses s t 0 (upperTailGap h u) :=
        middleGapModel_sound hcBox hH hU hh.ne' hu.ne' hgSize hgExp
      have hInvF : (b.inverseGap b.gapModel).Encloses s t 0 (upperTailGap h u)⁻¹ := by
        simpa only [one_div, inverseGap] using
          reciprocalFrom_lower_sound hcBox hF
            (CompactMiddleBox.gapInverseCandidate b.hModel b.uModel
              ((b.uHi + b.uLo) / 2)) hFpos
      have hNegU : b.negU.Encloses s t 0 (-u) := by
        simpa only [zero_sub, negU] using Model.sub_sound (Model.zero_sound s t 0) hU
      have hX := Model.expChecks_sound hcBox hNegU hxExp
      have hR : b.negHU.centeredExp.Encloses s t 0 (Real.exp (-(h * u))) := by
        simpa only [negHU, mul_neg] using Model.expChecks_sound hcBox
          (Model.mul_sound hcBox hH hNegU) hrExp
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨⟨_, hC⟩, hU'⟩, hT⟩, hN⟩ := hc
      exact middleTailGap_signs_of_replay hcBox hh hu hH hF hInvF hX hR hq₀ hq₁ hQ
        (show (0 : ℤ) < 1 by decide)
        ⟨lower_positive_of_all hC, lower_positive_of_all hU',
          lower_positive_of_all hT, lower_positive_of_all hN⟩
    · contradiction
  · contradiction

private def splitU (b : ReplayBox) : ReplayBox × ReplayBox :=
  let mid := (b.uLo + b.uHi) / 2
  ({ b with uHi := mid }, { b with uLo := mid })

private def splitH (b : ReplayBox) : ReplayBox × ReplayBox :=
  let mid := (b.hLo + b.hHi) / 2
  ({ b with hHi := mid }, { b with hLo := mid })

private def halves (b : ReplayBox) : ReplayBox × ReplayBox :=
  if 8 * (b.hHi - b.hLo) ≤ b.uHi - b.uLo then b.splitU else b.splitH

private theorem contains_halves {b : ReplayBox} {h u : ℝ} (hb : b.Contains h u) :
    b.halves.1.Contains h u ∨ b.halves.2.Contains h u := by
  unfold halves
  split
  · by_cases hm : u ≤ (((b.uLo + b.uHi) / 2 : ℚ) : ℝ)
    · exact Or.inl ⟨hb.1, hm, hb.2.2⟩
    · exact Or.inr ⟨le_of_not_ge hm, hb.2⟩
  · by_cases hm : h ≤ (((b.hLo + b.hHi) / 2 : ℚ) : ℝ)
    · exact Or.inl ⟨hb.1, hb.2.1, hb.2.2.1, hm⟩
    · exact Or.inr ⟨hb.1, hb.2.1, le_of_not_ge hm, hb.2.2.2⟩

private inductive Partition
  | leaf
  | split (left right : Partition)

private def Partition.Checked : Partition → ReplayBox → Prop
  | .leaf, b => b.check = true
  | .split left right, b => left.Checked b.halves.1 ∧ right.Checked b.halves.2

private theorem exists_checked_of_partition {tree : Partition} {b : ReplayBox} {h u : ℝ}
    (hc : tree.Checked b) (hb : b.Contains h u) :
    ∃ leaf : ReplayBox, leaf.check = true ∧ leaf.Contains h u := by
  induction tree generalizing b with
  | leaf => exact ⟨b, hc, hb⟩
  | split _ _ ihl ihr =>
    exact (contains_halves hb).elim (ihl hc.1) (ihr hc.2)

private def region : ReplayBox := ⟨1 / 2, 4, 0, 3 / 11⟩

private def partition : Partition :=
  (.split
    (.split
      (.split
        (.split
          (.split
            (.split
              (.split (.split (.split .leaf .leaf) (.split .leaf .leaf)) .leaf)
              (.split (.split (.split .leaf .leaf) (.split .leaf .leaf)) .leaf))
            (.split (.split .leaf .leaf) .leaf))
          (.split
            (.split
              (.split (.split (.split .leaf .leaf) (.split .leaf .leaf)) .leaf)
              (.split (.split (.split .leaf .leaf) (.split .leaf .leaf)) .leaf))
            (.split .leaf .leaf)))
        (.split (.split .leaf .leaf) (.split .leaf .leaf)))
      (.split
        (.split
          (.split
            (.split
              (.split (.split (.split .leaf .leaf) (.split .leaf .leaf)) .leaf)
              (.split (.split (.split .leaf .leaf) (.split .leaf .leaf)) .leaf))
            .leaf)
          (.split
            (.split
              (.split (.split .leaf .leaf) .leaf)
              (.split (.split .leaf .leaf) .leaf))
            .leaf))
        (.split .leaf .leaf)))
    (.split
      (.split .leaf (.split (.split .leaf (.split .leaf .leaf)) .leaf))
      (.split .leaf .leaf)))

set_option maxHeartbeats 0 in
-- Each leaf checks the elementary models and all 23 lower bounds.
set_option maxRecDepth 20000 in
private theorem partition_checked : partition.Checked region := by
  simp only [partition, Partition.Checked]
  repeat' apply And.intro
  all_goals as_aux_lemma => decide +kernel

end ReplayBox

/-- The certified Bernstein coefficients give the mixed sign on the central upper gap band. -/
theorem logKernel_mixed_neg_middleTail_bernstein {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 4)
    (hd₀ : 13 / 4 ≤ v - u) (hd₁ : v - u ≤ 7 / 2) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₀ : (0 : ℝ) < p := by linarith only [hpR]
  have hh : 0 < h := div_pos (by norm_num) hp₀
  have hhmax : h ≤ 3 / 11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hRegion : ReplayBox.region.Contains h u := by
    simpa only [ReplayBox.Contains, ReplayBox.region, Rat.cast_zero, Rat.cast_one, Rat.cast_div,
      Rat.cast_ofNat] using And.intro hu₀ (And.intro hu₁ (And.intro hh.le hhmax))
  obtain ⟨leaf, hleaf, hmem⟩ :=
    ReplayBox.exists_checked_of_partition ReplayBox.partition_checked hRegion
  have hd₄ : v - u ≤ 4 := by linarith only [hd₁]
  obtain ⟨hq, hqle, -, -⟩ := middleTail_gap_bounds hh hhmax hd₀ hd₄
  have hQ : 0 < middleTailSlopeCutoff h := hq.trans_le hqle
  apply logKernel_mixed_neg_of_middleTail_polynomials hp hu₀ hu₁ hd₀ (by linarith only [hd₁])
  exact ReplayBox.signs_of_check hleaf hmem hh (by linarith only [hu₀]) hq.le hqle hQ

#print axioms logKernel_mixed_neg_middleTail_bernstein

end RefinedBMV.PositiveCenter.CompactTaylorModel
