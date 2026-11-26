/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactTaylorResiduals
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer residual tests for reciprocal and square-root Taylor approximations. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorModel
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPackedPolynomial

/-! Residual tests for rational polynomial witnesses. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open DimThree.Certificate (Sparse checkPackedProduct)

local notation "S" => (scale : ℝ)

private def candidate (q : Sparse) : Model := ⟨q, 0⟩

private theorem candidate_sound (q : Sparse) (s t u : ℝ) :
    (candidate q).Encloses s t u ((candidate q).eval s t u) := by
  simp [Model.Encloses, candidate]

def reciprocalResidual (p : Model) (q : Sparse) : Model :=
  (Model.ofRat 1).sub (p.mul (candidate q))

/-- A bounded multiplicative residual and a positive real lower bound certify a reciprocal. -/
theorem reciprocalUsing_sound {product : Model} {s t u x : ℝ} {lower radius : ℕ}
    (hb : InBox s t u) (q : Sparse)
    (hproduct : product.Encloses s t u (x * (candidate q).eval s t u))
    (hpos : 0 < lower) (hlo : (lower : ℝ) / S ≤ x)
    (hr : ((Model.ofRat 1).sub product).absUpper * scale ≤ radius * lower) :
    (⟨q, radius⟩ : Model).Encloses s t u (1 / x) := by
  have hlo₀ : (0 : ℝ) < (lower : ℝ) / S :=
    div_pos (by exact_mod_cast hpos) scale_real_pos
  have hres : ((Model.ofRat 1).sub product).Encloses s t u
      (1 - x * (candidate q).eval s t u) :=
    Model.sub_sound (by simpa using Model.ofRat_sound 1 s t u) hproduct
  have hscaled : (((Model.ofRat 1).sub product).absUpper : ℝ) ≤
      (radius : ℝ) * ((lower : ℝ) / S) := by
    rw [← mul_div_assoc, le_div_iff₀ scale_real_pos]
    exact_mod_cast hr
  exact Model.inverse_candidate_sound hb hlo₀ hlo hres hscaled

theorem reciprocal_sound {p : Model} {s t u x : ℝ} {lower radius : ℕ}
    (hb : InBox s t u) (hx : p.Encloses s t u x) (q : Sparse)
    (hpos : 0 < lower) (hlo : (lower : ℝ) / S ≤ x)
    (hr : (reciprocalResidual p q).absUpper * scale ≤ radius * lower) :
    (⟨q, radius⟩ : Model).Encloses s t u (1 / x) :=
  reciprocalUsing_sound hb q (Model.mul_sound hb hx (candidate_sound q s t u)) hpos hlo hr

/-- Use the computed residual to choose the reciprocal error radius. -/
def reciprocalFrom (p : Model) (q : Sparse) (lower : ℕ) : Model :=
  ⟨q, ((reciprocalResidual p q).absUpper * scale) ⌈/⌉ lower⟩

theorem reciprocalFrom_sound {p : Model} {s t u x : ℝ} {lower : ℕ}
    (hb : InBox s t u) (hx : p.Encloses s t u x) (q : Sparse)
    (hpos : 0 < lower) (hlo : (lower : ℝ) / S ≤ x) :
    (reciprocalFrom p q lower).Encloses s t u (1 / x) :=
  reciprocal_sound hb hx q hpos hlo (by
    rw [Nat.mul_comm _ lower]
    exact (ceilDiv_le_iff_le_mul hpos).1 le_rfl)

/-- Use an explicit exact product to bound the reciprocal residual. -/
def reciprocalFromPacked (p : Model) (q exactProduct : Sparse) (lower : ℕ) : Model :=
  let product := p.mulUsing (candidate q) exactProduct
  ⟨q, (((Model.ofRat 1).sub product).absUpper * scale) ⌈/⌉ lower⟩

theorem reciprocalFromPacked_sound {p : Model} {s t u x : ℝ} {lower : ℕ}
    (hb : InBox s t u) (hx : p.Encloses s t u x) (q exactProduct : Sparse)
    (hcheck : checkPackedProduct p.polynomial.terms q.terms exactProduct.terms = true)
    (hpos : 0 < lower) (hlo : (lower : ℝ) / S ≤ x) :
    (reciprocalFromPacked p q exactProduct lower).Encloses s t u (1 / x) := by
  have hproduct := Model.mulUsingPacked_sound hb hx (candidate_sound q s t u) hcheck
  apply reciprocalUsing_sound hb q hproduct hpos hlo
  rw [Nat.mul_comm _ lower]
  exact (ceilDiv_le_iff_le_mul hpos).1 le_rfl

theorem reciprocalFrom_lower_sound {p : Model} {s t u x : ℝ}
    (hb : InBox s t u) (hx : p.Encloses s t u x) (q : Sparse) (hpos : 0 < p.lower) :
    (reciprocalFrom p q p.lower.toNat).Encloses s t u (1 / x) := by
  refine reciprocalFrom_sound hb hx q (by omega) ?_
  have hcast : ((p.lower.toNat : ℕ) : ℝ) = (p.lower : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hpos.le
  rw [hcast]
  exact Model.lower_sound hb hx

def radicalResidual (p : Model) (q : Sparse) : Model :=
  p.sub ((candidate q).mul (candidate q))

/-- Compare the squared polynomial with the radicand and divide by the sum of the roots. -/
theorem radicalUsing_sound {p square : Model} {s t u x : ℝ}
    {lower rootLower polynomialLower radius : ℕ}
    (hb : InBox s t u) (hx : p.Encloses s t u x) (q : Sparse)
    (hsquare : square.Encloses s t u ((candidate q).eval s t u ^ 2))
    (hlo : (lower : ℝ) / S ≤ x) (hroot : rootLower ^ 2 ≤ lower * scale)
    (hpoly : (polynomialLower : ℝ) / S ≤ (candidate q).eval s t u)
    (hpos : 0 < rootLower + polynomialLower)
    (hr : (p.sub square).absUpper * scale ≤ radius * (rootLower + polynomialLower)) :
    (⟨q, radius⟩ : Model).Encloses s t u (Real.sqrt x) := by
  have hnonneg : (0 : ℝ) ≤ (lower : ℝ) / S :=
    div_nonneg (Nat.cast_nonneg _) scale_real_pos.le
  have hroot₀ : (rootLower : ℝ) / S ≤ Real.sqrt ((lower : ℝ) / S) := by
    refine (Real.le_sqrt (div_nonneg (Nat.cast_nonneg _) scale_real_pos.le) hnonneg).2 ?_
    rw [div_pow, div_le_iff₀ (pow_pos scale_real_pos _)]
    rw [show (lower : ℝ) / S * S ^ 2 = (lower : ℝ) * S by
      field_simp [scale_real_pos.ne']]
    exact_mod_cast hroot
  have hsum : 0 < (rootLower : ℝ) / S + (polynomialLower : ℝ) / S := by
    rw [← add_div]
    exact div_pos (by exact_mod_cast hpos) scale_real_pos
  have hres : (p.sub square).Encloses s t u
      (x - (candidate q).eval s t u ^ 2) := by
    exact Model.sub_sound hx hsquare
  have hscaled : ((p.sub square).absUpper : ℝ) ≤ (radius : ℝ) *
      ((rootLower : ℝ) / S + (polynomialLower : ℝ) / S) := by
    rw [← add_div, ← mul_div_assoc, le_div_iff₀ scale_real_pos]
    exact_mod_cast hr
  exact Model.sqrt_candidate_sound hb hnonneg hlo hroot₀ hpoly hsum hres hscaled

theorem radical_sound {p : Model} {s t u x : ℝ} {lower rootLower polynomialLower radius : ℕ}
    (hb : InBox s t u) (hx : p.Encloses s t u x) (q : Sparse)
    (hlo : (lower : ℝ) / S ≤ x) (hroot : rootLower ^ 2 ≤ lower * scale)
    (hpoly : (polynomialLower : ℝ) / S ≤ (candidate q).eval s t u)
    (hpos : 0 < rootLower + polynomialLower)
    (hr : (radicalResidual p q).absUpper * scale ≤ radius * (rootLower + polynomialLower)) :
    (⟨q, radius⟩ : Model).Encloses s t u (Real.sqrt x) := by
  have hc := candidate_sound q s t u
  exact radicalUsing_sound hb hx q (by simpa only [pow_two] using Model.mul_sound hb hc hc)
    hlo hroot hpoly hpos hr

/-- Use the computed square residual to choose the square-root error radius. -/
def radicalFrom (p : Model) (q : Sparse) (rootLower polynomialLower : ℕ) : Model :=
  ⟨q, ((radicalResidual p q).absUpper * scale) ⌈/⌉ (rootLower + polynomialLower)⟩

theorem radicalFrom_sound {p : Model} {s t u x : ℝ} {lower rootLower polynomialLower : ℕ}
    (hb : InBox s t u) (hx : p.Encloses s t u x) (q : Sparse)
    (hlo : (lower : ℝ) / S ≤ x) (hroot : rootLower ^ 2 ≤ lower * scale)
    (hpoly : (polynomialLower : ℝ) / S ≤ (candidate q).eval s t u)
    (hpos : 0 < rootLower + polynomialLower) :
    (radicalFrom p q rootLower polynomialLower).Encloses s t u (Real.sqrt x) :=
  radical_sound hb hx q hlo hroot hpoly hpos (by
    rw [Nat.mul_comm _ (rootLower + polynomialLower)]
    exact (ceilDiv_le_iff_le_mul hpos).1 le_rfl)

theorem radicalFrom_lower_sound {p : Model} {s t u x : ℝ} {rootLower : ℕ}
    (hb : InBox s t u) (hx : p.Encloses s t u x) (q : Sparse) (hp : 0 ≤ p.lower)
    (hq : 0 < (candidate q).lower)
    (hroot : rootLower ^ 2 ≤ p.lower.toNat * scale) :
    (radicalFrom p q rootLower (candidate q).lower.toNat).Encloses s t u (Real.sqrt x) := by
  have hcast {a : ℤ} (ha : 0 ≤ a) : (a.toNat : ℝ) = (a : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg ha
  refine radicalFrom_sound hb hx q ?_ hroot ?_ (by omega)
  · rw [hcast hp]
    exact Model.lower_sound hb hx
  · rw [hcast hq.le]
    exact Model.lower_sound hb (candidate_sound q s t u)

end RefinedBMV.PositiveCenter.CompactTaylorModel
