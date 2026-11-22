/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactPolynomialBounds
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered fixed-point polynomial enclosures for the compact refined BMV box. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThreeCertificate
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Degree-eight polynomial enclosure arithmetic on the centered unit box. -/

namespace RefinedBMV.PositiveCenter.CompactPolynomialBounds

open DimThree (evalTerms)
open DimThree.Certificate (Sparse Term)

private def scale : ℕ := 2 ^ 100

local notation "S" => (scale : ℝ)

private theorem scale_pos : 0 < scale := by norm_num [scale]
private theorem scale_real_pos : 0 < S := by exact_mod_cast scale_pos

private def InBox (s t u : ℝ) : Prop := |s| ≤ 1 ∧ |t| ≤ 1 ∧ |u| ≤ 1

/-- Coefficients and the absolute error radius are in units of `1 / scale`. -/
private structure Model where
  polynomial : Sparse
  radius : ℕ

private noncomputable def Model.eval (p : Model) (s t u : ℝ) : ℝ :=
  p.polynomial.eval s t u / S

private def Model.Encloses (p : Model) (s t u f : ℝ) : Prop :=
  |f - p.eval s t u| ≤ (p.radius : ℝ) / S

private def coefficientMass (xs : List Term) : ℕ :=
  (xs.map fun a => a.coefficient.natAbs).sum

/-- The constant coefficient contributes exactly. Positive even monomials contribute at
least zero, and every other monomial contributes at least minus its absolute coefficient. -/
private def lowerContribution (a : Term) : ℤ :=
  if a.exponents = (0, 0, 0) then a.coefficient
  else if 0 ≤ a.coefficient ∧ Even a.exponents.1 ∧
      Even a.exponents.2.1 ∧ Even a.exponents.2.2 then 0
  else -(a.coefficient.natAbs : ℤ)

private def Model.lower (p : Model) : ℤ :=
  (p.polynomial.terms.map lowerContribution).sum - (p.radius : ℤ)

private def Model.absUpper (p : Model) : ℕ :=
  coefficientMass p.polynomial.terms + p.radius

private theorem abs_cast_eq_natAbs (n : ℤ) : |(n : ℝ)| = (n.natAbs : ℝ) := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

private theorem abs_eval_term_le {s t u : ℝ} (hb : InBox s t u) (a : Term) :
    |a.eval s t u| ≤ (a.coefficient.natAbs : ℝ) := by
  rw [← abs_cast_eq_natAbs]
  simp only [Term.eval, abs_mul, abs_pow]
  exact (mul_le_of_le_one_right (by positivity) (pow_le_one₀ (abs_nonneg _) hb.2.2)).trans
    ((mul_le_of_le_one_right (by positivity) (pow_le_one₀ (abs_nonneg _) hb.2.1)).trans
      (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hb.1)))

private theorem abs_eval_terms_le {s t u : ℝ} (hb : InBox s t u) (xs : List Term) :
    |evalTerms s t u xs| ≤ (coefficientMass xs : ℝ) := by
  induction xs with
  | nil => simp [evalTerms, coefficientMass]
  | cons a xs ih =>
    change |a.eval s t u + evalTerms s t u xs| ≤
      ((a.coefficient.natAbs + coefficientMass xs : ℕ) : ℝ)
    rw [Nat.cast_add]
    exact (abs_add_le ..).trans (add_le_add (abs_eval_term_le hb a) ih)

private theorem lowerContribution_le_eval {s t u : ℝ} (hb : InBox s t u) (a : Term) :
    (lowerContribution a : ℝ) ≤ a.eval s t u := by
  unfold lowerContribution
  split
  · rename_i h
    simp [Term.eval, h]
  · split
    · rename_i h
      simp only [Int.cast_zero, Term.eval]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by exact_mod_cast h.1)
        (h.2.1.pow_nonneg s)) (h.2.2.1.pow_nonneg t)) (h.2.2.2.pow_nonneg u)
    · push_cast
      rw [abs_cast_eq_natAbs]
      exact (abs_le.mp (abs_eval_term_le hb a)).1

private theorem lower_sum_le_eval {s t u : ℝ} (hb : InBox s t u) (xs : List Term) :
    (((xs.map lowerContribution).sum : ℤ) : ℝ) ≤ evalTerms s t u xs := by
  induction xs with
  | nil => simp [evalTerms]
  | cons a xs ih =>
    change ((lowerContribution a + (xs.map lowerContribution).sum : ℤ) : ℝ) ≤
      a.eval s t u + evalTerms s t u xs
    rw [Int.cast_add]
    exact add_le_add (lowerContribution_le_eval hb a) ih

private theorem Model.lower_sound {p : Model} {s t u f : ℝ}
    (hb : InBox s t u) (hf : p.Encloses s t u f) :
    (p.lower : ℝ) / S ≤ f := by
  have hp : (((p.polynomial.terms.map lowerContribution).sum : ℤ) : ℝ) / S ≤ p.eval s t u :=
    div_le_div_of_nonneg_right (lower_sum_le_eval hb _) scale_real_pos.le
  unfold Model.lower
  rw [Int.cast_sub, Int.cast_natCast, sub_div]
  linarith only [hp, (abs_le.mp hf).1]

private theorem Model.abs_eval_le (p : Model) {s t u : ℝ} (hb : InBox s t u) :
    |p.eval s t u| ≤ (coefficientMass p.polynomial.terms : ℝ) / S := by
  rw [Model.eval, abs_div, abs_of_pos scale_real_pos]
  exact div_le_div_of_nonneg_right (abs_eval_terms_le hb _) scale_real_pos.le

private theorem Model.absUpper_sound {p : Model} {s t u f : ℝ}
    (hb : InBox s t u) (hf : p.Encloses s t u f) :
    |f| ≤ (p.absUpper : ℝ) / S := by
  calc
    |f| = |p.eval s t u + (f - p.eval s t u)| := by
      congr 1
      ring
    _ ≤ (coefficientMass p.polynomial.terms : ℝ) / S + (p.radius : ℝ) / S :=
      (abs_add_le ..).trans (add_le_add (p.abs_eval_le hb) hf)
    _ = (p.absUpper : ℝ) / S := by rw [Model.absUpper, Nat.cast_add, add_div]

private def Model.add (p q : Model) : Model :=
  ⟨p.polynomial + q.polynomial, p.radius + q.radius⟩

private def Model.sub (p q : Model) : Model :=
  ⟨p.polynomial - q.polynomial, p.radius + q.radius⟩

private theorem Model.add_sound {p q : Model} {s t u f g : ℝ}
    (hf : p.Encloses s t u f) (hg : q.Encloses s t u g) :
    (p.add q).Encloses s t u (f + g) := by
  change |f + g - (p.polynomial + q.polynomial).eval s t u / S| ≤
    ((p.radius + q.radius : ℕ) : ℝ) / S
  rw [DimThree.eval_add, add_div, Nat.cast_add, add_div]
  change |f + g - (p.eval s t u + q.eval s t u)| ≤ (p.radius : ℝ) / S + (q.radius : ℝ) / S
  rw [show f + g - (p.eval s t u + q.eval s t u) =
      (f - p.eval s t u) + (g - q.eval s t u) by ring]
  exact (abs_add_le ..).trans (add_le_add hf hg)

private theorem Model.sub_sound {p q : Model} {s t u f g : ℝ}
    (hf : p.Encloses s t u f) (hg : q.Encloses s t u g) :
    (p.sub q).Encloses s t u (f - g) := by
  change |f - g - (p.polynomial - q.polynomial).eval s t u / S| ≤
    ((p.radius + q.radius : ℕ) : ℝ) / S
  rw [DimThree.eval_sub, sub_div, Nat.cast_add, add_div]
  change |f - g - (p.eval s t u - q.eval s t u)| ≤ (p.radius : ℝ) / S + (q.radius : ℝ) / S
  rw [show f - g - (p.eval s t u - q.eval s t u) =
      (f - p.eval s t u) + -(g - q.eval s t u) by ring]
  exact (abs_add_le ..).trans (add_le_add hf (by
    rw [abs_neg]
    exact hg))

/-- Round to the nearest integer, with ties rounded toward positive infinity.
Terms above degree eight have rounded coefficient zero. -/
private def roundedCoefficient (a : Term) : ℤ :=
  if a.exponents.1 + a.exponents.2.1 + a.exponents.2.2 ≤ 8 then
    (2 * a.coefficient + (scale : ℤ)) / (2 * (scale : ℤ))
  else 0

private def roundedTerm (a : Term) : Term :=
  ⟨a.exponents, roundedCoefficient a⟩

private def roundedTerms (xs : List Term) : List Term :=
  xs.filterMap fun a =>
    let b := roundedTerm a
    if b.coefficient = 0 then none else some b

private def residualTerm (a : Term) : Term :=
  ⟨a.exponents, a.coefficient - (scale : ℤ) * roundedCoefficient a⟩

private theorem eval_residualTerm (s t u : ℝ) (a : Term) :
    (residualTerm a).eval s t u = a.eval s t u - S * (roundedTerm a).eval s t u := by
  simp only [Term.eval, residualTerm, roundedTerm, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  ring

private theorem eval_residualTerms (s t u : ℝ) (xs : List Term) :
    evalTerms s t u (xs.map residualTerm) =
      evalTerms s t u xs - S * evalTerms s t u (roundedTerms xs) := by
  induction xs with
  | nil => simp [evalTerms, roundedTerms]
  | cons a xs ih =>
    change (residualTerm a).eval s t u + evalTerms s t u (xs.map residualTerm) =
      (a.eval s t u + evalTerms s t u xs) - S * evalTerms s t u (roundedTerms (a :: xs))
    rw [eval_residualTerm, ih]
    by_cases h : (roundedTerm a).coefficient = 0
    · have hz : (roundedTerm a).eval s t u = 0 := by simp [Term.eval, h]
      rw [show roundedTerms (a :: xs) = roundedTerms xs by simp [roundedTerms, h], hz]
      ring
    · rw [show roundedTerms (a :: xs) = roundedTerm a :: roundedTerms xs by
        simp [roundedTerms, h]]
      change _ = (a.eval s t u + evalTerms s t u xs) -
        S * ((roundedTerm a).eval s t u + evalTerms s t u (roundedTerms xs))
      ring

private def Model.mul (p q : Model) : Model :=
  let exactProduct := p.polynomial * q.polynomial
  let inputError := coefficientMass p.polynomial.terms * q.radius +
    p.radius * (coefficientMass q.polynomial.terms + q.radius)
  let residual := coefficientMass (exactProduct.terms.map residualTerm)
  ⟨⟨roundedTerms exactProduct.terms⟩, (inputError + residual) ⌈/⌉ scale⟩

private theorem Model.mul_sound {p q : Model} {s t u f g : ℝ}
    (hb : InBox s t u) (hf : p.Encloses s t u f) (hg : q.Encloses s t u g) :
    (p.mul q).Encloses s t u (f * g) := by
  let exactProduct := p.polynomial * q.polynomial
  let P := p.eval s t u
  let Q := q.eval s t u
  let rounded := evalTerms s t u (roundedTerms exactProduct.terms) / S
  let inputError := coefficientMass p.polynomial.terms * q.radius +
    p.radius * (coefficientMass q.polynomial.terms + q.radius)
  let residual := coefficientMass (exactProduct.terms.map residualTerm)
  have hp : |P| ≤ (coefficientMass p.polynomial.terms : ℝ) / S := p.abs_eval_le hb
  have hg' := q.absUpper_sound hb hg
  rw [Model.absUpper, Nat.cast_add] at hg'
  have hinput : |f * g - P * Q| ≤ (inputError : ℝ) / S ^ 2 := by
    rw [show f * g - P * Q = P * (g - Q) + (f - P) * g by ring]
    calc
      _ ≤ |P| * |g - Q| + |f - P| * |g| := by
        simpa only [abs_mul] using abs_add_le (P * (g - Q)) ((f - P) * g)
      _ ≤ ((coefficientMass p.polynomial.terms : ℝ) / S) * ((q.radius : ℝ) / S) +
          ((p.radius : ℝ) / S) *
            (((coefficientMass q.polynomial.terms : ℝ) + q.radius) / S) :=
        add_le_add
          (mul_le_mul hp hg (abs_nonneg _) (by positivity))
          (mul_le_mul hf hg' (abs_nonneg _) (by positivity))
      _ = _ := by
        dsimp only [inputError]
        push_cast
        field_simp [scale_real_pos.ne']
  have hscaled : P * Q - rounded =
      evalTerms s t u (exactProduct.terms.map residualTerm) / S ^ 2 := by
    have hexact : evalTerms s t u exactProduct.terms =
        p.polynomial.eval s t u * q.polynomial.eval s t u :=
      DimThree.eval_mul s t u p.polynomial q.polynomial
    rw [eval_residualTerms, hexact]
    dsimp only [P, Q, rounded, Model.eval]
    field_simp [scale_real_pos.ne']
  have hround : |P * Q - rounded| ≤ (residual : ℝ) / S ^ 2 := by
    rw [hscaled, abs_div, abs_of_nonneg (pow_nonneg scale_real_pos.le _)]
    exact div_le_div_of_nonneg_right (abs_eval_terms_le hb _) (pow_nonneg scale_real_pos.le _)
  have hceil : ((inputError + residual : ℕ) : ℝ) ≤
      S * (((inputError + residual) ⌈/⌉ scale : ℕ) : ℝ) := by
    have h : inputError + residual ≤ scale * ((inputError + residual) ⌈/⌉ scale) := by
      exact (ceilDiv_le_iff_le_mul scale_pos).1 le_rfl
    exact_mod_cast h
  change |f * g - rounded| ≤ (((inputError + residual) ⌈/⌉ scale : ℕ) : ℝ) / S
  calc
    _ ≤ |f * g - P * Q| + |P * Q - rounded| := abs_sub_le ..
    _ ≤ (inputError : ℝ) / S ^ 2 + (residual : ℝ) / S ^ 2 := add_le_add hinput hround
    _ ≤ _ := by
      rw [← add_div]
      apply (div_le_iff₀ (pow_pos scale_real_pos 2)).2
      rw [show (((inputError + residual) ⌈/⌉ scale : ℕ) : ℝ) / S * S ^ 2 =
        S * (((inputError + residual) ⌈/⌉ scale : ℕ) : ℝ) by
          field_simp [scale_real_pos.ne']]
      exact_mod_cast hceil

/-- A bound on the residual in fixed-point units certifies the proposed inverse radius. -/
private theorem Model.inverse_candidate_sound {p residual : Model} {s t u f lo : ℝ} {radius : ℕ}
    (hb : InBox s t u) (hlo : 0 < lo) (hf : lo ≤ f)
    (hres : residual.Encloses s t u (1 - f * p.eval s t u))
    (hradius : (residual.absUpper : ℝ) ≤ radius * lo) :
    (⟨p.polynomial, radius⟩ : Model).Encloses s t u (1 / f) := by
  have hf' : 0 < f := hlo.trans_le hf
  change |1 / f - p.eval s t u| ≤ (radius : ℝ) / S
  rw [show 1 / f - p.eval s t u = (1 - f * p.eval s t u) / f by field_simp [hf'.ne'],
    abs_div, abs_of_pos hf']
  calc
    _ ≤ |1 - f * p.eval s t u| / lo :=
      div_le_div_of_nonneg_left (abs_nonneg _) hlo hf
    _ ≤ ((residual.absUpper : ℝ) / S) / lo :=
      div_le_div_of_nonneg_right (residual.absUpper_sound hb hres) hlo.le
    _ ≤ _ := by
      rw [div_right_comm]
      exact div_le_div_of_nonneg_right ((div_le_iff₀ hlo).2 hradius) scale_real_pos.le

/-- A certified lower bound for the radical and candidate sum controls the square-root error. -/
private theorem Model.sqrt_candidate_sound {p residual : Model}
    {s t u f lo rootLower candidateLower : ℝ} {radius : ℕ}
    (hb : InBox s t u) (hlo : 0 ≤ lo) (hf : lo ≤ f)
    (hroot : rootLower ≤ Real.sqrt lo) (hp : candidateLower ≤ p.eval s t u)
    (hden : 0 < rootLower + candidateLower)
    (hres : residual.Encloses s t u (f - p.eval s t u ^ 2))
    (hradius : (residual.absUpper : ℝ) ≤ radius * (rootLower + candidateLower)) :
    (⟨p.polynomial, radius⟩ : Model).Encloses s t u (Real.sqrt f) := by
  let P := p.eval s t u
  have hsum : rootLower + candidateLower ≤ Real.sqrt f + P :=
    add_le_add (hroot.trans (Real.sqrt_le_sqrt hf)) hp
  have hsum' : 0 < Real.sqrt f + P := hden.trans_le hsum
  change |Real.sqrt f - P| ≤ (radius : ℝ) / S
  rw [show Real.sqrt f - P = (f - P ^ 2) / (Real.sqrt f + P) by
      apply (eq_div_iff hsum'.ne').2
      nlinarith only [Real.sq_sqrt (hlo.trans hf)],
    abs_div, abs_of_pos hsum']
  calc
    _ ≤ |f - P ^ 2| / (rootLower + candidateLower) :=
      div_le_div_of_nonneg_left (abs_nonneg _) hden hsum
    _ ≤ ((residual.absUpper : ℝ) / S) / (rootLower + candidateLower) :=
      div_le_div_of_nonneg_right (residual.absUpper_sound hb hres) hden.le
    _ ≤ _ := by
      rw [div_right_comm]
      exact div_le_div_of_nonneg_right ((div_le_iff₀ hden).2 hradius) scale_real_pos.le

end RefinedBMV.PositiveCenter.CompactPolynomialBounds
