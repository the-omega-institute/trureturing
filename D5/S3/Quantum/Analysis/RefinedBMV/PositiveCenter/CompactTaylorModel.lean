/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactTaylorModel
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-point polynomial enclosures for the compact refined BMV region. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThreeCertificate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactBernstein
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPackedPolynomial
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open DimThree (evalTerms)
open DimThree.Certificate (Sparse Term checkedProduct eval_checkedProduct
  checkPackedProduct eval_of_checkPackedProduct)

def scale : ℕ := 2 ^ 100

local notation "S" => (scale : ℝ)

theorem scale_pos : 0 < scale := by norm_num [scale]
theorem scale_real_pos : 0 < S := by exact_mod_cast scale_pos

def InBox (s t u : ℝ) : Prop := |s| ≤ 1 ∧ |t| ≤ 1 ∧ |u| ≤ 1

/-- Coefficients and the absolute error radius are in units of `1 / scale`. -/
structure Model where
  polynomial : Sparse
  radius : ℕ

noncomputable def Model.eval (p : Model) (s t u : ℝ) : ℝ :=
  p.polynomial.eval s t u / S

def Model.Encloses (p : Model) (s t u f : ℝ) : Prop :=
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

def Model.lower (p : Model) : ℤ :=
  (p.polynomial.terms.map lowerContribution).sum - (p.radius : ℤ)

def Model.absUpper (p : Model) : ℕ :=
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

private def keepTerm (degree : ℕ) (a : Term) : Bool :=
  decide (a.exponents.1 + a.exponents.2.1 + a.exponents.2.2 ≤ degree)

/-- Move higher-degree terms into the absolute error before bounding the polynomial. -/
def Model.truncate (p : Model) (degree : ℕ) : Model :=
  ⟨⟨p.polynomial.terms.filter (keepTerm degree)⟩,
    p.radius + coefficientMass (p.polynomial.terms.filter (fun a ↦ !keepTerm degree a))⟩

theorem Model.truncate_degree (p : Model) (degree : ℕ) {a : Term}
    (ha : a ∈ (p.truncate degree).polynomial.terms) :
    a.exponents.1 ≤ degree ∧ a.exponents.2.1 ≤ degree ∧ a.exponents.2.2 ≤ degree := by
  have h : a.exponents.1 + a.exponents.2.1 + a.exponents.2.2 ≤ degree :=
    of_decide_eq_true ((List.mem_filter.mp ha).2)
  exact ⟨by omega, by omega, by omega⟩

private theorem evalTerms_split (test : Term → Bool) (s t u : ℝ) (xs : List Term) :
    evalTerms s t u xs =
      evalTerms s t u (xs.filter test) + evalTerms s t u (xs.filter (fun a ↦ !test a)) := by
  induction xs with
  | nil => simp [evalTerms]
  | cons a xs ih =>
    cases h : test a <;> simp [evalTerms, h] at ih ⊢ <;> linarith only [ih]

theorem Model.truncate_sound {p : Model} {s t u f : ℝ} (degree : ℕ)
    (hb : InBox s t u) (hf : p.Encloses s t u f) : (p.truncate degree).Encloses s t u f := by
  let tail := p.polynomial.terms.filter (fun a ↦ !keepTerm degree a)
  have htail : |evalTerms s t u tail / S| ≤ (coefficientMass tail : ℝ) / S := by
    rw [abs_div, abs_of_pos scale_real_pos]
    exact div_le_div_of_nonneg_right (abs_eval_terms_le hb tail) scale_real_pos.le
  have hdiff :
      f - (p.truncate degree).eval s t u = (f - p.eval s t u) + evalTerms s t u tail / S := by
    unfold Model.eval Sparse.eval Model.truncate
    rw [evalTerms_split (keepTerm degree) s t u p.polynomial.terms]
    dsimp only [tail]
    ring
  unfold Model.Encloses
  rw [hdiff]
  have h := (abs_add_le (f - p.eval s t u) (evalTerms s t u tail / S)).trans (add_le_add hf htail)
  simpa only [Model.truncate, tail, Nat.cast_add, add_div] using h

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

theorem Model.lower_sound {p : Model} {s t u f : ℝ}
    (hb : InBox s t u) (hf : p.Encloses s t u f) :
    (p.lower : ℝ) / S ≤ f := by
  have hp : (((p.polynomial.terms.map lowerContribution).sum : ℤ) : ℝ) / S ≤ p.eval s t u :=
    div_le_div_of_nonneg_right (lower_sum_le_eval hb _) scale_real_pos.le
  unfold Model.lower
  rw [Int.cast_sub, Int.cast_natCast, sub_div]
  linarith only [hp, (abs_le.mp hf).1]

/-- A lower bound for the Bernstein coefficients improves the enclosure lower endpoint. -/
theorem Model.lower_of_bernstein {p : Model} {D : ℕ} {L : ℚ} {s t u f : ℝ}
    (hb : InBox s t u) (hf : p.Encloses s t u f)
    (hD : ∀ a ∈ p.polynomial.terms,
      a.exponents.1 ≤ D ∧ a.exponents.2.1 ≤ D ∧ a.exponents.2.2 ≤ D)
    (hL : ∀ i ≤ D, ∀ j ≤ D, ∀ k ≤ D,
      L ≤ CompactBernstein.tensorCoefficient p.polynomial.terms D i j k) :
    ((L : ℝ) - p.radius) / S ≤ f := by
  have hp : (L : ℝ) / S ≤ p.eval s t u :=
    div_le_div_of_nonneg_right
      (CompactBernstein.le_evalTerms_of_coefficients p.polynomial.terms hD hL hb.1 hb.2.1 hb.2.2)
      scale_real_pos.le
  rw [sub_div]
  linarith only [hp, (abs_le.mp hf).1]

private theorem Model.abs_eval_le (p : Model) {s t u : ℝ} (hb : InBox s t u) :
    |p.eval s t u| ≤ (coefficientMass p.polynomial.terms : ℝ) / S := by
  rw [Model.eval, abs_div, abs_of_pos scale_real_pos]
  exact div_le_div_of_nonneg_right (abs_eval_terms_le hb _) scale_real_pos.le

theorem Model.absUpper_sound {p : Model} {s t u f : ℝ}
    (hb : InBox s t u) (hf : p.Encloses s t u f) :
    |f| ≤ (p.absUpper : ℝ) / S := by
  calc
    |f| = |p.eval s t u + (f - p.eval s t u)| := by
      congr 1
      ring
    _ ≤ (coefficientMass p.polynomial.terms : ℝ) / S + (p.radius : ℝ) / S :=
      (abs_add_le ..).trans (add_le_add (p.abs_eval_le hb) hf)
    _ = (p.absUpper : ℝ) / S := by rw [Model.absUpper, Nat.cast_add, add_div]

def Model.add (p q : Model) : Model :=
  ⟨p.polynomial + q.polynomial, p.radius + q.radius⟩

def Model.sub (p q : Model) : Model :=
  ⟨p.polynomial - q.polynomial, p.radius + q.radius⟩

theorem Model.add_sound {p q : Model} {s t u f g : ℝ}
    (hf : p.Encloses s t u f) (hg : q.Encloses s t u g) :
    (p.add q).Encloses s t u (f + g) := by
  change |f + g - (p.polynomial + q.polynomial).eval s t u / S| ≤
    ((p.radius + q.radius : ℕ) : ℝ) / S
  rw [DimThree.eval_add, add_div, Nat.cast_add, add_div]
  change |f + g - (p.eval s t u + q.eval s t u)| ≤ (p.radius : ℝ) / S + (q.radius : ℝ) / S
  rw [show f + g - (p.eval s t u + q.eval s t u) =
      (f - p.eval s t u) + (g - q.eval s t u) by ring]
  exact (abs_add_le ..).trans (add_le_add hf hg)

theorem Model.sub_sound {p q : Model} {s t u f g : ℝ}
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
Terms above degree twelve have rounded coefficient zero. -/
private def roundedCoefficient (a : Term) : ℤ :=
  if a.exponents.1 + a.exponents.2.1 + a.exponents.2.2 ≤ 12 then
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

/-- Round the exact product once its coefficients have been obtained. -/
def Model.mulUsing (p q : Model) (exactProduct : Sparse) : Model :=
  let inputError := coefficientMass p.polynomial.terms * q.radius +
    p.radius * (coefficientMass q.polynomial.terms + q.radius)
  let residual := coefficientMass (exactProduct.terms.map residualTerm)
  ⟨⟨roundedTerms exactProduct.terms⟩, (inputError + residual) ⌈/⌉ scale⟩

def Model.mul (p q : Model) : Model :=
  (p.mulUsing q ⟨checkedProduct p.polynomial.terms q.polynomial.terms⟩).truncate 6

theorem Model.mulUsing_sound {p q : Model} {s t u f g : ℝ} {exactProduct : Sparse}
    (hb : InBox s t u) (hf : p.Encloses s t u f) (hg : q.Encloses s t u g)
    (hexact : exactProduct.eval s t u = p.polynomial.eval s t u * q.polynomial.eval s t u) :
    (p.mulUsing q exactProduct).Encloses s t u (f * g) := by
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
    change evalTerms s t u exactProduct.terms = _ at hexact
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

theorem Model.mul_sound {p q : Model} {s t u f g : ℝ}
    (hb : InBox s t u) (hf : p.Encloses s t u f) (hg : q.Encloses s t u g) :
    (p.mul q).Encloses s t u (f * g) :=
  Model.truncate_sound 6 hb
    (Model.mulUsing_sound hb hf hg (eval_checkedProduct s t u p.polynomial.terms q.polynomial.terms))

/-- A supplied polynomial can be used directly once its packed product check passes. -/
theorem Model.mulUsingPacked_sound {p q : Model} {s t u f g : ℝ} {product : Sparse}
    (hb : InBox s t u) (hf : p.Encloses s t u f) (hg : q.Encloses s t u g)
    (hc : checkPackedProduct p.polynomial.terms q.polynomial.terms product.terms = true) :
    (p.mulUsing q product).Encloses s t u (f * g) :=
  Model.mulUsing_sound hb hf hg (eval_of_checkPackedProduct s t u hc)

/-- A bound on the residual in fixed-point units certifies the proposed inverse radius. -/
theorem Model.inverse_candidate_sound {p residual : Model} {s t u f lo : ℝ} {radius : ℕ}
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
theorem Model.sqrt_candidate_sound {p residual : Model}
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

def Model.zero : Model := ⟨⟨[]⟩, 0⟩

theorem Model.zero_sound (s t z : ℝ) : Model.zero.Encloses s t z 0 := by
  simp [Model.Encloses, Model.eval, Model.zero, Sparse.eval, evalTerms]

def Model.ofRat (r : ℚ) : Model :=
  let q := r * scale
  let c := round q
  ⟨if c = 0 then ⟨[]⟩ else ⟨[⟨(0, 0, 0), c⟩]⟩, if (c : ℚ) = q then 0 else 1⟩

theorem Model.ofRat_sound (r : ℚ) (s t z : ℝ) :
    (Model.ofRat r).Encloses s t z (r : ℝ) := by
  let q : ℚ := r * scale
  let c : ℤ := round q
  have he : (Model.ofRat r).eval s t z = (c : ℝ) / S := by
    unfold Model.ofRat Model.eval
    change (if c = 0 then (⟨[]⟩ : Sparse) else ⟨[⟨(0, 0, 0), c⟩]⟩).eval s t z / S = _
    split <;> simp_all [Sparse.eval, evalTerms, Term.eval]
  change |(r : ℝ) - (Model.ofRat r).eval s t z| ≤
    ((if (c : ℚ) = q then (0 : ℕ) else 1 : ℕ) : ℝ) / S
  rw [he, ← div_mul_cancel₀ (r : ℝ) scale_real_pos.ne', div_mul_eq_mul_div, ← sub_div,
    abs_div, abs_of_pos scale_real_pos, div_le_div_iff_of_pos_right scale_real_pos]
  have hcast : (↑q : ℝ) = (↑r : ℝ) * S := by
    simp [q]
  rw [← hcast]
  split
  · rename_i h
    have h' : (c : ℝ) = (q : ℝ) := by exact_mod_cast h
    simp [h']
  · have h : |q - (c : ℚ)| ≤ 1 := (abs_sub_round q).trans (by norm_num)
    simpa using (show |(q : ℝ) - (c : ℝ)| ≤ 1 by exact_mod_cast h)

/-- A coordinate with no approximation error. -/
def Model.coordinate (axis : Fin 3) : Model :=
  ⟨⟨[⟨(if axis = 0 then 1 else 0, if axis = 1 then 1 else 0, if axis = 2 then 1 else 0),
    scale⟩]⟩, 0⟩

theorem Model.coordinate_sound (axis : Fin 3) (s t z : ℝ) :
    (Model.coordinate axis).Encloses s t z (![s, t, z] axis) := by
  fin_cases axis <;>
    simp [Model.coordinate, Model.Encloses, Model.eval, Sparse.eval, evalTerms, Term.eval,
      scale_real_pos.ne']

def Model.affineCoordinate (axis : Fin 3) (center radius : ℚ) : Model :=
  (Model.ofRat center).add ((Model.coordinate axis).mul (Model.ofRat radius))

theorem Model.affineCoordinate_sound {s t z : ℝ} (hb : InBox s t z)
    (axis : Fin 3) (center radius : ℚ) :
    (Model.affineCoordinate axis center radius).Encloses s t z
      ((center : ℝ) + ![s, t, z] axis * (radius : ℝ)) :=
  Model.add_sound (Model.ofRat_sound center s t z)
    (Model.mul_sound hb (Model.coordinate_sound axis s t z) (Model.ofRat_sound radius s t z))

def Model.widen (p : Model) (r : ℚ) : Model :=
  ⟨p.polynomial, p.radius + (⌈r * scale⌉ : ℤ).toNat⟩

theorem Model.widen_sound {p : Model} {s t z f g : ℝ} {r : ℚ}
    (hp : p.Encloses s t z g) (he : |f - g| ≤ (r : ℝ)) :
    (p.widen r).Encloses s t z f := by
  have hb : (r : ℝ) * S ≤ ((⌈r * scale⌉ : ℤ).toNat : ℝ) := by
    have hc : r * (scale : ℚ) ≤ ((⌈r * scale⌉ : ℤ).toNat : ℚ) :=
      (Int.le_ceil _).trans (by exact_mod_cast Int.self_le_toNat _)
    exact_mod_cast hc
  change |f - p.eval s t z| ≤ ((p.radius + (⌈r * scale⌉ : ℤ).toNat : ℕ) : ℝ) / S
  rw [Nat.cast_add, add_div]
  calc
    _ ≤ |f - g| + |g - p.eval s t z| := abs_sub_le ..
    _ ≤ ((⌈r * scale⌉ : ℤ).toNat : ℝ) / S + (p.radius : ℝ) / S :=
      add_le_add (he.trans ((le_div_iff₀ scale_real_pos).2 hb)) hp
    _ = _ := add_comm ..

def Model.series : ℕ → (ℕ → Model) → Model → Model
  | 0, _, _ => Model.zero
  | n + 1, c, x => (Model.series n (fun i => c (i + 1)) x).mul x |>.add (c 0)

theorem Model.series_sound {s t z x : ℝ} {X : Model}
    (hb : InBox s t z) (hx : X.Encloses s t z x)
    (n : ℕ) (c : ℕ → Model) (f : ℕ → ℝ)
    (hc : ∀ i < n, (c i).Encloses s t z (f i)) :
    (Model.series n c X).Encloses s t z (∑ i ∈ Finset.range n, f i * x ^ i) := by
  induction n generalizing c f with
  | zero => simpa [Model.series] using Model.zero_sound s t z
  | succ n ih =>
    have hi := ih (fun i => c (i + 1)) (fun i => f (i + 1))
      (fun i hi => hc (i + 1) (Nat.succ_lt_succ hi))
    rw [Finset.sum_range_succ', pow_zero, mul_one]
    simp only [pow_succ, ← mul_assoc, ← Finset.sum_mul]
    exact Model.add_sound (Model.mul_sound hb hi hx) (hc 0 (Nat.zero_lt_succ _))

def Model.horner (cs : List ℚ) (x : Model) : Model :=
  cs.foldr (fun c r => (r.mul x).add (Model.ofRat c)) Model.zero

def Model.sum : ℕ → (ℕ → Model) → Model
  | 0, _ => Model.zero
  | n + 1, c => (Model.sum n c).add (c n)

theorem Model.sum_sound {s t z : ℝ}
    (n : ℕ) (c : ℕ → Model) (f : ℕ → ℝ) (hc : ∀ i < n, (c i).Encloses s t z (f i)) :
    (Model.sum n c).Encloses s t z (∑ i ∈ Finset.range n, f i) := by
  induction n with
  | zero => simpa [Model.sum] using Model.zero_sound s t z
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact Model.add_sound (ih fun i hi => hc i (Nat.lt_succ_of_lt hi)) (hc n (Nat.lt_succ_self n))

def Model.pow (p : Model) : ℕ → Model
  | 0 => Model.ofRat 1
  | 1 => p
  | n + 2 =>
    let k := (n + 2) / 2
    let q := p.pow k
    let q2 := q.mul q
    if (n + 2) % 2 = 0 then q2 else q2.mul p
termination_by n => n
decreasing_by omega

theorem Model.pow_sound {s t z f : ℝ} {p : Model}
    (hb : InBox s t z) (hp : p.Encloses s t z f) (n : ℕ) :
    (p.pow n).Encloses s t z (f ^ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simpa [Model.pow] using Model.ofRat_sound 1 s t z
    | 1 => simpa [Model.pow] using hp
    | n + 2 =>
      rw [Model.pow]
      have hh := ih ((n + 2) / 2) (by omega)
      have h2 := Model.mul_sound hb hh hh
      split
      · rename_i he
        rwa [← pow_add, show (n + 2) / 2 + (n + 2) / 2 = n + 2 by omega] at h2
      · rename_i ho
        have h := Model.mul_sound hb h2 hp
        rwa [← pow_add, ← pow_succ, show (n + 2) / 2 + (n + 2) / 2 + 1 = n + 2 by omega] at h

end RefinedBMV.PositiveCenter.CompactTaylorModel
