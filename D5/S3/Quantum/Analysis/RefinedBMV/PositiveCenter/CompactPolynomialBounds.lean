/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactPolynomialBounds
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered fixed-point polynomial enclosures for the compact refined BMV box. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThreeCertificate
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMarginalTails
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactScalarTails
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactSquareWitnesses
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Rat.Floor
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

private def Model.zero : Model := ⟨⟨[]⟩, 0⟩

private theorem Model.zero_sound (s t z : ℝ) : Model.zero.Encloses s t z 0 := by
  simp [Model.Encloses, Model.eval, Model.zero, Sparse.eval, evalTerms]

private def Model.ofRat (r : ℚ) : Model :=
  let q := r * scale
  let c := round q
  ⟨if c = 0 then ⟨[]⟩ else ⟨[⟨(0, 0, 0), c⟩]⟩, if (c : ℚ) = q then 0 else 1⟩

private theorem Model.ofRat_sound (r : ℚ) (s t z : ℝ) :
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

private def Model.widen (p : Model) (r : ℚ) : Model :=
  ⟨p.polynomial, p.radius + (⌈r * scale⌉ : ℤ).toNat⟩

private theorem Model.widen_sound {p : Model} {s t z f g : ℝ} {r : ℚ}
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

private def Model.series : ℕ → (ℕ → Model) → Model → Model
  | 0, _, _ => Model.zero
  | n + 1, c, x => (Model.series n (fun i => c (i + 1)) x).mul x |>.add (c 0)

private theorem Model.series_sound {s t z x : ℝ} {X : Model}
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

private def Model.horner (cs : List ℚ) (x : Model) : Model :=
  cs.foldr (fun c r => (r.mul x).add (Model.ofRat c)) Model.zero

private theorem Model.horner_sound {s t z x : ℝ} {X : Model} (hb : InBox s t z)
    (hx : X.Encloses s t z x) (cs : List ℚ) :
    (Model.horner cs X).Encloses s t z (SmallCorner.momentHorner x cs) := by
  induction cs with
  | nil => exact Model.zero_sound s t z
  | cons c cs ih =>
    simpa only [Model.horner, List.foldr_cons, SmallCorner.momentHorner, mul_comm x, add_comm (c : ℝ)]
      using Model.add_sound (Model.mul_sound hb ih hx) (Model.ofRat_sound c s t z)

private def Model.sum : ℕ → (ℕ → Model) → Model
  | 0, _ => Model.zero
  | n + 1, c => (Model.sum n c).add (c n)

private theorem Model.sum_sound {s t z : ℝ}
    (n : ℕ) (c : ℕ → Model) (f : ℕ → ℝ) (hc : ∀ i < n, (c i).Encloses s t z (f i)) :
    (Model.sum n c).Encloses s t z (∑ i ∈ Finset.range n, f i) := by
  induction n with
  | zero => simpa [Model.sum] using Model.zero_sound s t z
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact Model.add_sound (ih fun i hi => hc i (Nat.lt_succ_of_lt hi)) (hc n (Nat.lt_succ_self n))

private def Model.pow (p : Model) : ℕ → Model
  | 0 => Model.ofRat 1
  | 1 => p
  | n + 2 =>
    let k := (n + 2) / 2
    let q := p.pow k
    let q2 := q.mul q
    if (n + 2) % 2 = 0 then q2 else q2.mul p
termination_by n => n
decreasing_by omega

private theorem Model.pow_sound {s t z f : ℝ} {p : Model}
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

open SmallCorner (jointTaylorMoment marginalTaylorPolynomial momentHorner
  normalizedMomentCoeffs normalized_moment_eval_swap normalized_moment_eval_joint
  continuedMarginalJet_isAt affineMarginalJet)

private theorem marginalTaylor_eq_moments {p : ℕ} (hp : 0 < p) (k : ℕ) (x : ℝ) :
    marginalTaylorPolynomial p k x =
      ∑ i ∈ Finset.range (23 - k),
        (momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs 0 (k + i + 2)) *
          ((k + i).factorial : ℝ) / (i.factorial : ℝ)) * x ^ i := by
  unfold marginalTaylorPolynomial
  apply Finset.sum_congr rfl
  intro i _
  rw [normalized_moment_eval_swap 0 (k + i + 2) (by omega), normalized_moment_eval_joint hp]
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one]
  rw [Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_succ, Nat.cast_succ]
  field_simp [show (0 : ℝ) < (k + i).factorial by positivity,
    show (0 : ℝ) < i.factorial by positivity,
    show (0 : ℝ) < (↑(k + i) : ℝ) + 1 by positivity,
    show (0 : ℝ) < (↑(k + i) : ℝ) + 1 + 1 by positivity,
    show (0 : ℝ) < (↑(k + i) : ℝ) + 2 by positivity]
  <;> ring

private theorem deriv_compositionMoment_eq {p : ℕ} (hp : 0 < p) (d : ℝ) :
    deriv (compositionMoment p 0) d =
      compactKappa p * d * compactZ p d * (2 + d * compactZSlope p d) := by
  have hv : compactKappa p = compositionMarginalVariance p / 2 := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have hN : (0 : ℝ) < (DimThree.gaps p).length := by
      exact_mod_cast (DimThree.word_counts_all p).2.1
    unfold compositionMarginalVariance
    rw [(centered_marginal_sums hp).2]
    unfold compactKappa
    field_simp [hpR, hN.ne']
    norm_num
  have hz : HasDerivAt (compactZ p)
      (SmallCorner.integralMarginalDerivative p (compactKappa p) 1 d) d := by
    change HasDerivAt (SmallCorner.integralMarginalDerivative p (compactKappa p) 0) _ d
    rw [hv]
    simpa [affineMarginalJet] using (continuedMarginalJet_isAt p 0 0 1 0 d).2.1
  have hpoly : HasDerivAt (fun x : ℝ => compactKappa p * x ^ 2)
      (compactKappa p * (2 * d)) d := by
    simpa using (hasDerivAt_pow 2 d).const_mul (compactKappa p)
  rw [show compositionMoment p 0 = fun x => compactKappa p * x ^ 2 * compactZ p x
      from funext (compositionMoment_eq_compactZ hp), (hpoly.fun_mul hz).deriv,
    compactZSlope_eq hp]
  field_simp [(compactZ_pos hp d).ne']

private theorem compactMixedT_eq_cutoff {p : ℕ} (hp : 0 < p) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) (J : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    let d := v - u
    let a := 1 / u - compactZSlope p (-u) / 2
    let b := 1 / v - compactZSlope p (-v) / 2
    let k := 1 / upperTailGap h u
    let γ := 1 + k + a
    compactMixedT p u v J =
      (-γ) * (2 + h - b) * J - γ * k * Real.exp (-(1 + h) * u) *
        (1 + compactKappa p * v ^ 2 * compactZ p v) +
      k * Real.exp u * ((γ - b) * (1 + compactKappa p * d ^ 2 * compactZ p d) +
        compactKappa p * d * compactZ p d * (2 + d * compactZSlope p d)) - a * b := by
  dsimp only [compactMixedT]
  rw [reflectedHalfLogSlope_eq_compactZSlope hp hu.ne',
    reflectedHalfLogSlope_eq_compactZSlope hp hv.ne',
    compositionMoment_eq_compactZ hp v, compositionMoment_eq_compactZ hp (v - u),
    deriv_compositionMoment_eq hp]
  have hk : (3 / (p : ℝ)) / (1 - Real.exp (-(3 / (p : ℝ)) * u)) =
      1 / upperTailGap (3 / (p : ℝ)) u := by
    unfold upperTailGap
    rw [neg_mul, one_div_div]
  change (-_) * _ * J - _ + _ - _ = _
  rw [← hk]
  rfl

private def uModel : Model := ⟨⟨[⟨(0, 0, 0), (3 * scale / 4 : ℕ)⟩,
  ⟨(1, 0, 0), (scale / 4 : ℕ)⟩]⟩, 0⟩

private def dModel : Model := ⟨⟨[⟨(0, 0, 0), (3 * scale / 4 : ℕ)⟩,
  ⟨(0, 1, 0), (scale / 4 : ℕ)⟩]⟩, 0⟩

private def hModel : Model := ⟨⟨[⟨(0, 0, 0), round (3 / 22 * (scale : ℚ))⟩,
  ⟨(0, 0, 1), round (3 / 22 * (scale : ℚ))⟩]⟩, 2⟩

private theorem uModel_sound (u d h : ℝ) :
    uModel.Encloses (4 * u - 3) (4 * d - 3) (22 * h / 3 - 1) u := by
  unfold Model.Encloses Model.eval uModel
  norm_num [Sparse.eval, evalTerms, Term.eval, scale, abs_le]
  constructor <;> linarith

private theorem dModel_sound (u d h : ℝ) :
    dModel.Encloses (4 * u - 3) (4 * d - 3) (22 * h / 3 - 1) d := by
  unfold Model.Encloses Model.eval dModel
  norm_num [Sparse.eval, evalTerms, Term.eval, scale, abs_le]
  constructor <;> linarith

private theorem hModel_sound {u d h : ℝ} (hb : InBox (4 * u - 3) (4 * d - 3) (22 * h / 3 - 1)) :
    hModel.Encloses (4 * u - 3) (4 * d - 3) (22 * h / 3 - 1) h := by
  let z := 22 * h / 3 - 1
  let c : ℤ := round (3 / 22 * (scale : ℚ))
  have hc : |(3 / 22 : ℝ) - (c : ℝ) / S| ≤ 1 / S := by
    have e : round (3 / 22 * (scale : ℚ)) = 172861445485667645658641346188 := by decide +kernel
    norm_num [c, e, scale]
  have he : h - hModel.eval (4 * u - 3) (4 * d - 3) z =
      (3 / 22 - (c : ℝ) / S) + z * (3 / 22 - (c : ℝ) / S) := by
    simp [hModel, Model.eval, Sparse.eval, evalTerms, Term.eval, c, z]
    ring
  change |h - hModel.eval (4 * u - 3) (4 * d - 3) z| ≤ 2 / S
  rw [he]
  calc
    _ ≤ |(3 / 22 : ℝ) - (c : ℝ) / S| + |z| * |(3 / 22 : ℝ) - (c : ℝ) / S| := by
      rw [← abs_mul]; exact abs_add_le ..
    _ ≤ 1 / S + 1 * (1 / S) :=
      add_le_add hc (mul_le_mul hb.2.2 hc (abs_nonneg _) zero_le_one)
    _ = _ := by ring

private def oneModel : Model := Model.ofRat 1
private def twoModel : Model := Model.ofRat 2
private def halfModel : Model := Model.ofRat (1 / 2)
private def kappaModel : Model := (oneModel.add hModel).mul (Model.ofRat (1 / 4))
private def cModel : Model := twoModel.add hModel

private def normMomentModel (n : ℕ) : Model :=
  Model.horner (normalizedMomentCoeffs 0 n) hModel

private def rawMomentModel : ℕ → Model
  | 0 => oneModel
  | 1 => Model.zero
  | n + 2 => (kappaModel.mul (Model.ofRat ((n + 2).factorial : ℚ))).mul (normMomentModel (n + 2))

private def marginalModel (k : ℕ) (x : Model) : Model :=
  (Model.series (23 - k) (fun i =>
    (normMomentModel (k + i + 2)).mul (Model.ofRat (((k + i).factorial : ℚ) / i.factorial))) x).widen
    ((2 : ℚ) ^ (k + 2) * 4 ^ (23 - k) / ((23 - k).factorial * 24 * 25))

private theorem marginalModel_sound {p : ℕ} (hp : 0 < p) {s t z x : ℝ} {X : Model}
    (hb : InBox s t z) (hh : hModel.Encloses s t z (3 / (p : ℝ)))
    (hx : X.Encloses s t z x) {k : ℕ} (hk : k ≤ 2) (hr : |x| ≤ 2) :
    (marginalModel k X).Encloses s t z (iteratedDeriv k (compactZ p) x) := by
  apply Model.widen_sound (g := marginalTaylorPolynomial p k x)
  · rw [marginalTaylor_eq_moments hp]
    apply Model.series_sound hb hx
    intro i _
    simpa only [normMomentModel, Rat.cast_div, Rat.cast_natCast, mul_div_assoc] using
      Model.mul_sound hb (Model.horner_sound hb hh (normalizedMomentCoeffs 0 (k + i + 2)))
        (Model.ofRat_sound (((k + i).factorial : ℚ) / i.factorial) s t z)
  · push_cast
    exact iteratedDeriv_compactZ_sub_taylor_le_two hp hk hr

private theorem rawMomentModel_sound {s t z h : ℝ} (hb : InBox s t z)
    (hh : hModel.Encloses s t z h) (n : ℕ) :
    (rawMomentModel n).Encloses s t z (compactCenteredMomentPolynomial h n) := by
  match n with
  | 0 => simpa [rawMomentModel, oneModel, compactCenteredMomentPolynomial] using Model.ofRat_sound 1 s t z
  | 1 => exact Model.zero_sound s t z
  | n + 2 =>
    have hκ : kappaModel.Encloses s t z ((1 + h) / 4) := by
      have hm := Model.mul_sound hb (Model.add_sound (Model.ofRat_sound 1 s t z) hh)
        (Model.ofRat_sound (1 / 4) s t z)
      push_cast at hm
      simpa [kappaModel, oneModel, div_eq_mul_inv] using hm
    have hf : (Model.ofRat ((n + 2).factorial : ℚ)).Encloses s t z ((n + 2).factorial : ℝ) := by
      exact_mod_cast Model.ofRat_sound ((n + 2).factorial : ℚ) s t z
    exact Model.mul_sound hb (Model.mul_sound hb hκ hf) (Model.horner_sound hb hh _)

private def weightedMomentModel (j : ℕ) (x : Model) : Model :=
  let coeff (n : ℕ) := (Model.sum (j + 1) (fun l =>
    ((cModel.pow (j - l)).mul (rawMomentModel (n + l))).mul
      (Model.ofRat ((-1 : ℚ) ^ l * (j.choose l : ℚ))))).mul (Model.ofRat (1 / (n.factorial : ℚ)))
  (Model.series (25 - j) coeff x).widen ((36 / 11 : ℚ) ^ j * (7 / 22) * 3 ^ (25 - j) / ((25 - j).factorial : ℚ))

private theorem weightedMomentModel_sound {p : ℕ} (hp : 11 ≤ p) {s t z x : ℝ} {X : Model}
    (hb : InBox s t z) (hh : hModel.Encloses s t z (3 / (p : ℝ)))
    (hx : X.Encloses s t z x) {j : ℕ} (hj : j ≤ 6) (hr : |x| ≤ 3 / 2) :
    (weightedMomentModel j X).Encloses s t z (compactPositiveMoment p j x) := by
  apply Model.widen_sound (g := compactPositiveMomentTaylor (3 / (p : ℝ)) j x)
  · unfold compactPositiveMomentTaylor
    apply Model.series_sound hb hx
    intro n _
    have hc : cModel.Encloses s t z (2 + 3 / (p : ℝ)) := by
      simpa [cModel, twoModel] using Model.add_sound (Model.ofRat_sound 2 s t z) hh
    have hsum := Model.sum_sound (j + 1) _ _ (fun l _ =>
      Model.mul_sound hb (Model.mul_sound hb (Model.pow_sound hb hc (j - l))
        (rawMomentModel_sound hb hh (n + l))) (Model.ofRat_sound ((-1 : ℚ) ^ l * (j.choose l : ℚ)) s t z))
    have he : (∑ l ∈ Finset.range (j + 1), (2 + 3 / (p : ℝ)) ^ (j - l) *
        compactCenteredMomentPolynomial (3 / (p : ℝ)) (n + l) *
          ↑((-1 : ℚ) ^ l * (j.choose l : ℚ))) = compactPositiveMomentCoefficient (3 / (p : ℝ)) j n := by
      apply Finset.sum_congr rfl
      intro l _
      push_cast
      ring
    rw [he] at hsum
    have hm := Model.mul_sound hb hsum (Model.ofRat_sound (1 / (n.factorial : ℚ)) s t z)
    push_cast at hm
    simpa only [div_eq_mul_inv, one_mul] using hm
  · push_cast
    exact compactPositiveMoment_sub_taylor_abs_le hp hj hr

private def expModel (x : Model) : Model :=
  (Model.series 25 (fun n => Model.ofRat (1 / (n.factorial : ℚ))) x).widen
    (2 * (3 / 2 : ℚ) ^ 25 / ((25 : ℕ).factorial : ℚ))

private theorem expModel_sound {s t z x : ℝ} {X : Model} (hb : InBox s t z)
    (hx : X.Encloses s t z x) (hr : |x| ≤ 3 / 2) :
    (expModel X).Encloses s t z (Real.exp x) := by
  apply Model.widen_sound (g := compactExpTaylor x)
  · change (Model.series _ _ _).Encloses _ _ _ (∑ n ∈ Finset.range 25, x ^ n / (n.factorial : ℝ))
    simp only [div_eq_inv_mul]
    apply Model.series_sound hb hx
    intro n _
    simpa using Model.ofRat_sound (1 / (n.factorial : ℚ)) s t z
  · push_cast
    exact compactExp_sub_taylor_abs_le hr

private def sinhcModel (x : Model) : Model :=
  (Model.series 25 (fun n => Model.ofRat (if n % 2 = 0 then 1 / ((n + 1).factorial : ℚ) else 0)) x)
    |>.widen (2 * (3 / 22 : ℚ) ^ 25 / ((26 : ℕ).factorial : ℚ))

private theorem sinhcModel_sound {s t z x : ℝ} {X : Model} (hb : InBox s t z)
    (hx : X.Encloses s t z x) (hx₀ : 0 < x) (hr : x ≤ 3 / 22) :
    (sinhcModel X).Encloses s t z (Real.sinh x / x) := by
  apply Model.widen_sound (g := compactSinhcTaylor x)
  · unfold compactSinhcTaylor
    have he : (∑ n ∈ Finset.range 25, (if Even n then x ^ n / ((n + 1).factorial : ℝ) else 0)) =
        ∑ n ∈ Finset.range 25,
          ((if n % 2 = 0 then 1 / ((n + 1).factorial : ℚ) else 0 : ℚ) : ℝ) * x ^ n := by
      apply Finset.sum_congr rfl
      intro n _
      by_cases he : n % 2 = 0
      · simp [he, Nat.even_iff, div_eq_mul_inv, mul_comm]
      · simp [he, Nat.even_iff]
    rw [he]
    exact Model.series_sound hb hx 25 _ _ (fun n _ => Model.ofRat_sound _ s t z)
  · push_cast
    exact compactSinhc_sub_taylor_abs_le hx₀ hr

private def cutoffModel (x y : Model) : Model :=
  x.mul ((Model.series 25 (fun n => Model.ofRat (1 / ((n + 1).factorial : ℚ)))
    (Model.zero.sub (y.mul x))).widen (2 * (3 / 11 : ℚ) ^ 25 / ((26 : ℕ).factorial : ℚ)))

private theorem cutoffModel_sound {p : ℕ} (hp : 11 ≤ p) {s t z x : ℝ} {X : Model}
    (hb : InBox s t z) (hh : hModel.Encloses s t z (3 / (p : ℝ)))
    (hx : X.Encloses s t z x) (hx₀ : 0 < x) (hx₁ : x ≤ 1) :
    (cutoffModel X hModel).Encloses s t z (upperTailGap (3 / (p : ℝ)) x) := by
  let h : ℝ := 3 / (p : ℝ)
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₀ : (0 : ℝ) < p := by linarith
  have hh₀ : 0 < h := div_pos (by norm_num) hp₀
  have hh₁ : h ≤ 3 / 11 := (div_le_iff₀ hp₀).2 (by linarith)
  have harg : 0 < |-(h * x)| := by rw [abs_neg, abs_of_pos (mul_pos hh₀ hx₀)]; positivity
  have hbound : |-(h * x)| ≤ 3 / 11 := by
    rw [abs_neg, abs_of_pos (mul_pos hh₀ hx₀)]
    exact (mul_le_of_le_one_right hh₀.le hx₁).trans hh₁
  have hm : (Model.zero.sub (hModel.mul X)).Encloses s t z (-(h * x)) := by
    simpa only [zero_sub] using Model.sub_sound (Model.zero_sound s t z) (Model.mul_sound hb hh hx)
  have hseries : (Model.series 25 (fun n => Model.ofRat (1 / ((n + 1).factorial : ℚ)))
      (Model.zero.sub (hModel.mul X))).Encloses s t z (compactPhiTaylor (-(h * x))) := by
    unfold compactPhiTaylor
    simp only [div_eq_inv_mul]
    apply Model.series_sound hb hm
    intro i _
    simpa using Model.ofRat_sound (1 / ((i + 1).factorial : ℚ)) s t z
  have he : |(Real.exp (-(h * x)) - 1) / (-(h * x)) - compactPhiTaylor (-(h * x))| ≤
    ((2 * (3 / 11 : ℚ) ^ 25 / ((26 : ℕ).factorial : ℚ) : ℚ) : ℝ) := by
    push_cast
    exact compactPhi_sub_taylor_abs_le harg hbound
  have heng := Model.mul_sound hb hx (Model.widen_sound hseries he)
  have heq : upperTailGap h x = x * ((Real.exp (-(h * x)) - 1) / (-(h * x))) := by
    unfold upperTailGap
    field_simp [hh₀.ne', hx₀.ne']
    ring
  change (cutoffModel X hModel).Encloses s t z (upperTailGap h x)
  rw [heq]
  exact heng

private def Model.candidate (terms : Sparse) (radius : ℕ) : Model := ⟨terms, radius⟩

private def Model.inverseResidual (p : Model) (q : Sparse) : Model :=
  oneModel.sub (p.mul (Model.candidate q 0))

private theorem Model.candidate_eval_sound (q : Sparse) (s t z : ℝ) :
    (Model.candidate q 0).Encloses s t z ((Model.candidate q 0).eval s t z) := by
  simp [Model.Encloses, Model.candidate]

private theorem Model.inverse_of_checked {p : Model} {s t z f : ℝ} {lo r : ℕ}
    (hb : InBox s t z) (hp : p.Encloses s t z f) (q : Sparse)
    (hlo₀ : 0 < lo) (hlo : (lo : ℤ) ≤ p.lower)
    (hr : (p.inverseResidual q).absUpper * scale ≤ r * lo) :
    (Model.candidate q r).Encloses s t z (1 / f) := by
  have hf : (lo : ℝ) / S ≤ f := by
    apply le_trans _ (Model.lower_sound hb hp)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hlo) scale_real_pos.le
  have hr' : ((p.inverseResidual q).absUpper : ℝ) ≤ (r : ℝ) * ((lo : ℝ) / S) := by
    rw [← mul_div_assoc, le_div_iff₀ scale_real_pos]
    exact_mod_cast hr
  exact Model.inverse_candidate_sound (p := Model.candidate q 0) hb
    (div_pos (by exact_mod_cast hlo₀) scale_real_pos) hf
    (Model.sub_sound (by simpa [oneModel] using Model.ofRat_sound 1 s t z)
      (Model.mul_sound hb hp (Model.candidate_eval_sound q s t z))) hr'

private def Model.sqrtResidual (p : Model) (q : Sparse) : Model :=
  p.sub ((Model.candidate q 0).mul (Model.candidate q 0))

private theorem Model.sqrt_of_checked {p : Model} {s t z f : ℝ} {r : ℕ}
    (hb : InBox s t z) (hp : p.Encloses s t z f) (q : Sparse)
    (hf : (scale : ℤ) * 81 ≤ p.lower * 100)
    (hq : (scale : ℤ) ≤ (Model.candidate q 0).lower)
    (hr : (p.sqrtResidual q).absUpper * 10 ≤ r * 19) :
    (Model.candidate q r).Encloses s t z (Real.sqrt f) := by
  have hrad : (81 / 100 : ℝ) ≤ f := by
    have hh := Model.lower_sound hb hp
    have he : S * 81 ≤ (p.lower : ℝ) * 100 := by exact_mod_cast hf
    exact ((le_div_iff₀ scale_real_pos).2 (by linarith)).trans hh
  have hcand : 1 ≤ (Model.candidate q 0).eval s t z := by
    have hh := Model.lower_sound hb (Model.candidate_eval_sound q s t z)
    have he : S ≤ ((Model.candidate q 0).lower : ℝ) := by exact_mod_cast hq
    exact ((le_div_iff₀ scale_real_pos).2 (by simpa using he)).trans hh
  have hroot : (9 / 10 : ℝ) ≤ Real.sqrt (81 / 100) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hres := Model.sub_sound hp (Model.mul_sound hb
    (Model.candidate_eval_sound q s t z) (Model.candidate_eval_sound q s t z))
  rw [← pow_two] at hres
  have hrr : ((p.sqrtResidual q).absUpper : ℝ) * 10 ≤ (r : ℝ) * 19 := by exact_mod_cast hr
  exact Model.sqrt_candidate_sound hb (by norm_num) hrad hroot hcand (by norm_num)
    hres (by change ((p.sqrtResidual q).absUpper : ℝ) ≤ _; linarith)

open CompactSquareWitnesses in
private def invUModel : Model := Model.candidate u 128900000000000000000000000
open CompactSquareWitnesses in
private def invVModel : Model := Model.candidate v 64410000000000000000000000
open CompactSquareWitnesses in
private def invNegUModel : Model := Model.candidate negU 710200000000000000000
open CompactSquareWitnesses in
private def invNegVModel : Model := Model.candidate negV 56510000000000000000000
open CompactSquareWitnesses in
private def invPosVModel : Model := Model.candidate posV 2023000000000000000000000
open CompactSquareWitnesses in
private def invPosDModel : Model := Model.candidate posD 5632000000000000000000
open CompactSquareWitnesses in
private def rootModel : Model := Model.candidate radical 6500000000000000000000000
open CompactSquareWitnesses in
private def invSinhcModel : Model := Model.candidate sinhc 121600000000000000000
open CompactSquareWitnesses in
private def invCutoffModel : Model := Model.candidate cutoff 158600000000000000000000000

private def vModel : Model := uModel.add dModel
private def negUModel : Model := Model.zero.sub uModel
private def negVModel : Model := Model.zero.sub vModel
private def aModel : Model := uModel.mul halfModel
private def tModel : Model := vModel.sub aModel
private def expArgModel : Model := (Model.zero.sub (oneModel.add hModel)).mul uModel
private def zNegU : Model := marginalModel 0 negUModel
private def zNegV : Model := marginalModel 0 negVModel
private def zPosV : Model := marginalModel 0 vModel
private def zPosD : Model := marginalModel 0 dModel
private def zNegU' : Model := marginalModel 1 negUModel
private def zNegV' : Model := marginalModel 1 negVModel
private def zPosV' : Model := marginalModel 1 vModel
private def zPosD' : Model := marginalModel 1 dModel
private def zPosD'' : Model := marginalModel 2 dModel
private def radicandModel : Model := zPosV.mul zPosD
private def sinhcInputModel : Model := sinhcModel (hModel.mul aModel)
private def cutoffInputModel : Model := cutoffModel uModel hModel
private def jointMom0 : Model := weightedMomentModel 0 tModel
private def jointMom2 : Model := weightedMomentModel 2 tModel
private def jointMom4 : Model := weightedMomentModel 4 tModel
private def jointMom6 : Model := weightedMomentModel 6 tModel

private def suModel : Model := zNegU'.mul invNegUModel
private def svModel : Model := zNegV'.mul invNegVModel
private def tvModel : Model := zPosV'.mul invPosVModel
private def tdModel : Model := zPosD'.mul invPosDModel
private def wdModel : Model := (zPosD''.mul invPosDModel).sub (tdModel.pow 2)
private def leftSlopeModel : Model := invUModel.sub (suModel.mul halfModel)
private def rightSlopeModel : Model := invVModel.sub (svModel.mul halfModel)
private def rvModel : Model := (kappaModel.mul (vModel.pow 2)).mul zPosV
private def rdModel : Model := (kappaModel.mul (dModel.pow 2)).mul zPosD
private def rdPrimeModel : Model :=
  ((kappaModel.mul dModel).mul zPosD).mul (twoModel.add (dModel.mul tdModel))

private def radicalModel : Model :=
  let x := tdModel.sub suModel
  let y := (tvModel.add tdModel).add svModel
  let r := ((y.mul invUModel).mul halfModel).add ((x.mul y).mul (Model.ofRat (1 / 4)))
  let br := (invUModel.add ((x.add y).mul halfModel)).add
    (dModel.mul (r.add (wdModel.mul halfModel)))
  (((Model.zero.sub kappaModel).mul vModel).mul rootModel).mul br

private def jointModel : Model :=
  let m2 := ((aModel.pow 2).mul (Model.ofRat (1 / 6))).mul jointMom2
  let m4 := ((aModel.pow 4).mul (Model.ofRat (1 / 120))).mul jointMom4
  let m6 := ((Model.ofRat (287 / 1458000)).mul (aModel.pow 6)).mul jointMom6
  (((jointMom0.add m2).add m4).add m6).mul invSinhcModel

private def affineModel : Model :=
  let γ := (oneModel.add invCutoffModel).add leftSlopeModel
  let a := ((Model.zero.sub γ).mul (cModel.sub rightSlopeModel)).mul jointModel
  let b := ((γ.mul invCutoffModel).mul (expModel expArgModel)).mul (oneModel.add rvModel)
  let c := ((invCutoffModel.mul (expModel uModel))).mul
    ((((γ.sub rightSlopeModel).mul (oneModel.add rdModel))).add rdPrimeModel)
  ((a.sub b).add c).sub (leftSlopeModel.mul rightSlopeModel)

private def comparisonModel : Model := radicalModel.sub affineModel

private def Model.InverseChecked (p : Model) (q : Sparse) (r lo : ℕ) : Prop :=
  (lo : ℤ) ≤ p.lower ∧ (p.inverseResidual q).absUpper * scale ≤ r * lo

private structure CompactChecks : Prop where
  invU : uModel.InverseChecked invUModel.polynomial invUModel.radius 633825300000000000000000000000
  invV : vModel.InverseChecked invVModel.polynomial invVModel.radius 1267650600000000000000000000000
  invNegU : zNegU.InverseChecked invNegUModel.polynomial invNegUModel.radius
    1199359340000000000000000000000
  invNegV : zNegV.InverseChecked invNegVModel.polynomial invNegVModel.radius
    1142294860000000000000000000000
  invPosV : zPosV.InverseChecked invPosVModel.polynomial invPosVModel.radius
    1222476740000000000000000000000
  invPosD : zPosD.InverseChecked invPosDModel.polynomial invPosDModel.radius
    1345722040000000000000000000000
  radicand : (scale : ℤ) * 81 ≤ radicandModel.lower * 100
  root : (scale : ℤ) ≤ (Model.candidate rootModel.polynomial 0).lower
  rootResidual : (radicandModel.sqrtResidual rootModel.polynomial).absUpper * 10 ≤ rootModel.radius * 19
  sinhc : sinhcInputModel.InverseChecked invSinhcModel.polynomial invSinhcModel.radius
    1265499490000000000000000000000
  cutoff : cutoffInputModel.InverseChecked invCutoffModel.polynomial invCutoffModel.radius
    531865370000000000000000000000
  comparison : (11 : ℤ) * scale ≤ 2500 * comparisonModel.lower

private theorem Model.inverse_of_check {p q : Model} {s t z f : ℝ} {lo : ℕ}
    (hb : InBox s t z) (hp : p.Encloses s t z f)
    (hlo : 0 < lo) (hcheck : p.InverseChecked q.polynomial q.radius lo) :
    q.Encloses s t z (1 / f) := by
  exact Model.inverse_of_checked hb hp q.polynomial hlo hcheck.1 hcheck.2

set_option maxHeartbeats 1500000 in
private theorem comparison_of_checked (cert : CompactChecks) {p : ℕ} (hp : 11 ≤ p)
    {u d : ℝ} (hu : 1 / 2 ≤ u) (hu' : u ≤ 1) (hd : 1 / 2 ≤ d) (hd' : d ≤ 1) :
    (11 / 2500 : ℝ) ≤ compactMixedQ p u (u + d) -
      compactMixedT p u (u + d) (compositionMomentSixth p u (u + d)) := by
  let h : ℝ := 3 / (p : ℝ)
  let v := u + d
  let a := u / 2
  let s := 4 * u - 3
  let t := 4 * d - 3
  let z := 22 * h / 3 - 1
  have hv : v - u = d := by dsimp [v]; ring
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hpR₀ : (0 : ℝ) < p := by linarith
  have hh₀ : 0 < h := div_pos (by norm_num) hpR₀
  have hh₁ : h ≤ 3 / 11 := (div_le_iff₀ hpR₀).2 (by linarith)
  have hu₀ : 0 < u := by linarith
  have hv₀ : 0 < v := by dsimp [v]; linarith
  have ha₀ : 0 < a := by dsimp [a]; linarith
  have ha₁ : a ≤ 1 / 2 := by dsimp [a]; linarith
  have huv : u < v := by dsimp [v]; linarith
  have hb : InBox s t z := ⟨abs_le.mpr ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩,
    abs_le.mpr ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩,
    abs_le.mpr ⟨by dsimp [z]; linarith, by dsimp [z]; linarith⟩⟩
  have U : uModel.Encloses s t z u := uModel_sound u d h
  have D : dModel.Encloses s t z d := dModel_sound u d h
  have H : hModel.Encloses s t z h := hModel_sound hb
  have O : oneModel.Encloses s t z 1 := by simpa [oneModel] using Model.ofRat_sound 1 s t z
  have W : twoModel.Encloses s t z 2 := by simpa [twoModel] using Model.ofRat_sound 2 s t z
  have F : halfModel.Encloses s t z (1 / 2) := by
    simpa [halfModel] using Model.ofRat_sound (1 / 2) s t z
  have V : vModel.Encloses s t z v := Model.add_sound U D
  have Um : negUModel.Encloses s t z (-u) := by
    simpa only [negUModel, zero_sub] using Model.sub_sound (Model.zero_sound s t z) U
  have Vm : negVModel.Encloses s t z (-v) := by
    simpa only [negVModel, zero_sub] using Model.sub_sound (Model.zero_sound s t z) V
  have HU : |-u| ≤ 2 := by rw [abs_neg, abs_of_pos hu₀]; linarith
  have HV : |v| ≤ 2 := by rw [abs_of_pos hv₀]; dsimp [v]; linarith
  have HD : |d| ≤ 2 := by rw [abs_of_nonneg (by linarith : 0 ≤ d)]; linarith
  have zu : zNegU.Encloses s t z (compactZ p (-u)) := by
    simpa only [zNegU, iteratedDeriv_zero] using marginalModel_sound hp₀ hb H Um (k := 0) (by omega) HU
  have zv : zNegV.Encloses s t z (compactZ p (-v)) := by
    simpa only [zNegV, iteratedDeriv_zero] using marginalModel_sound hp₀ hb H Vm (k := 0) (by omega)
      (by simpa only [abs_neg] using HV)
  have ZV : zPosV.Encloses s t z (compactZ p v) := by
    simpa only [zPosV, iteratedDeriv_zero] using marginalModel_sound hp₀ hb H V (k := 0) (by omega) HV
  have ZD : zPosD.Encloses s t z (compactZ p d) := by
    simpa only [zPosD, iteratedDeriv_zero] using marginalModel_sound hp₀ hb H D (k := 0) (by omega) HD
  have slopeU : suModel.Encloses s t z (compactZSlope p (-u)) := by
    rw [compactZSlope_eq hp₀, ← iteratedDeriv_compactZ_eq_integral hp₀ 1, div_eq_mul_one_div]
    exact Model.mul_sound hb (marginalModel_sound hp₀ hb H Um (by omega) HU)
      (Model.inverse_of_check hb zu (by decide) cert.invNegU)
  have slopeV : svModel.Encloses s t z (compactZSlope p (-v)) := by
    rw [compactZSlope_eq hp₀, ← iteratedDeriv_compactZ_eq_integral hp₀ 1, div_eq_mul_one_div]
    exact Model.mul_sound hb (marginalModel_sound hp₀ hb H Vm (by omega)
      (by simpa only [abs_neg] using HV)) (Model.inverse_of_check hb zv (by decide) cert.invNegV)
  have slopeVp : tvModel.Encloses s t z (compactZSlope p v) := by
    rw [compactZSlope_eq hp₀, ← iteratedDeriv_compactZ_eq_integral hp₀ 1, div_eq_mul_one_div]
    exact Model.mul_sound hb (marginalModel_sound hp₀ hb H V (by omega) HV)
      (Model.inverse_of_check hb ZV (by decide) cert.invPosV)
  have invZD := Model.inverse_of_check hb ZD (by decide) cert.invPosD
  have slopeD : tdModel.Encloses s t z (compactZSlope p d) := by
    rw [compactZSlope_eq hp₀, ← iteratedDeriv_compactZ_eq_integral hp₀ 1, div_eq_mul_one_div]
    exact Model.mul_sound hb (marginalModel_sound hp₀ hb H D (by omega) HD) invZD
  have curvatureD : wdModel.Encloses s t z (deriv (compactZSlope p) d) := by
    rw [deriv_compactZSlope hp₀, ← iteratedDeriv_compactZ_eq_integral hp₀ 2, div_eq_mul_one_div]
    exact Model.sub_sound (Model.mul_sound hb
      (marginalModel_sound hp₀ hb H D (by omega) HD) invZD) (Model.pow_sound hb slopeD 2)
  have K : kappaModel.Encloses s t z (compactKappa p) := by
    have hm := Model.mul_sound hb (Model.add_sound O H) (Model.ofRat_sound (1 / 4) s t z)
    push_cast at hm
    simpa [kappaModel, compactKappa, h, div_eq_mul_inv] using hm
  have Iu := Model.inverse_of_check hb U (by decide) cert.invU
  have Iv := Model.inverse_of_check hb V (by decide) cert.invV
  have sqrtVd : rootModel.Encloses s t z (Real.sqrt (compactZ p v * compactZ p d)) :=
    Model.sqrt_of_checked hb (show radicandModel.Encloses s t z _ from Model.mul_sound hb ZV ZD)
      rootModel.polynomial cert.radicand cert.root cert.rootResidual
  have Hq : radicalModel.Encloses s t z (compactMixedQ p u v) := by
    rw [compactMixedQ_eq_regularized hp₀ hu₀ huv]
    unfold compactRegularizedQ
    dsimp only
    rw [hv]
    have X := Model.sub_sound slopeD slopeU
    have Y := Model.add_sound (Model.add_sound slopeVp slopeD) slopeV
    have R := Model.add_sound
      (Model.mul_sound hb (Model.mul_sound hb Y Iu) F)
      (Model.mul_sound hb (Model.mul_sound hb X Y) (Model.ofRat_sound (1 / 4) s t z))
    have B := Model.add_sound (Model.add_sound Iu (Model.mul_sound hb (Model.add_sound X Y) F))
      (Model.mul_sound hb D (Model.add_sound R (Model.mul_sound hb curvatureD F)))
    have q := Model.mul_sound hb (Model.mul_sound hb
      (Model.mul_sound hb (Model.sub_sound (Model.zero_sound s t z) K) V) sqrtVd) B
    push_cast at q
    unfold radicalModel
    convert q using 1 <;> ring
  have A : aModel.Encloses s t z a := by
    change (uModel.mul halfModel).Encloses s t z (u / 2)
    rw [show u / 2 = u * (1 / 2) by ring]
    exact Model.mul_sound hb U F
  have TJ : tModel.Encloses s t z (v - a) := Model.sub_sound V A
  have hTJ : |v - a| ≤ 3 / 2 := abs_le.mpr ⟨by dsimp [v, a]; linarith, by dsimp [v, a]; linarith⟩
  have J0 : jointMom0.Encloses s t z (compactPositiveMoment p 0 (v - a)) :=
    weightedMomentModel_sound hp hb H TJ (by omega) hTJ
  have J2 : jointMom2.Encloses s t z (compactPositiveMoment p 2 (v - a)) :=
    weightedMomentModel_sound hp hb H TJ (by omega) hTJ
  have J4 : jointMom4.Encloses s t z (compactPositiveMoment p 4 (v - a)) :=
    weightedMomentModel_sound hp hb H TJ (by omega) hTJ
  have J6 : jointMom6.Encloses s t z (compactPositiveMoment p 6 (v - a)) :=
    weightedMomentModel_sound hp hb H TJ (by omega) hTJ
  have Sinc : sinhcInputModel.Encloses s t z (Real.sinh (h * a) / (h * a)) :=
    sinhcModel_sound hb (Model.mul_sound hb H A) (mul_pos hh₀ ha₀)
      ((mul_le_mul hh₁ ha₁ ha₀.le (by norm_num)).trans (by norm_num))
  have HJ : jointModel.Encloses s t z (compositionMomentSixth p u v) := by
    have si := Model.inverse_of_check hb Sinc (by decide) cert.sinhc
    have m2 := Model.mul_sound hb (Model.mul_sound hb (Model.pow_sound hb A 2)
      (Model.ofRat_sound (1 / 6) s t z)) J2
    have m4 := Model.mul_sound hb (Model.mul_sound hb (Model.pow_sound hb A 4)
      (Model.ofRat_sound (1 / 120) s t z)) J4
    have m6 := Model.mul_sound hb (Model.mul_sound hb (Model.ofRat_sound (287 / 1458000) s t z)
      (Model.pow_sound hb A 6)) J6
    have eq := Model.mul_sound hb (Model.add_sound (Model.add_sound (Model.add_sound J0 m2) m4) m6) si
    unfold compositionMomentSixth
    dsimp only
    change jointModel.Encloses s t z ((h * a / Real.sinh (h * a)) * _)
    push_cast at eq
    rw [one_div_div] at eq
    unfold jointModel
    convert eq using 1 <;> ring
  have Cut : cutoffInputModel.Encloses s t z (upperTailGap h u) :=
    cutoffModel_sound hp hb H U hu₀ hu'
  have IK := Model.inverse_of_check hb Cut (by decide) cert.cutoff
  have EXPu : (expModel uModel).Encloses s t z (Real.exp u) :=
    expModel_sound hb U (by rw [abs_of_pos hu₀]; linarith)
  have EXPdecay : (expModel expArgModel).Encloses s t z (Real.exp (-(1 + h) * u)) := by
    apply expModel_sound hb
    · simpa only [expArgModel, zero_sub] using Model.mul_sound hb
        (Model.sub_sound (Model.zero_sound s t z) (Model.add_sound O H)) U
    · rw [neg_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (1 + h) * u)]
      exact (mul_le_of_le_one_right (by positivity : 0 ≤ 1 + h) hu').trans (by linarith)
  have HT : affineModel.Encloses s t z (compactMixedT p u v (compositionMomentSixth p u v)) := by
    rw [compactMixedT_eq_cutoff hp₀ hu₀ hv₀, hv]
    have RA := Model.sub_sound Iu (Model.mul_sound hb slopeU F)
    have RB := Model.sub_sound Iv (Model.mul_sound hb slopeV F)
    have Y := Model.add_sound (Model.add_sound O IK) RA
    have C := Model.add_sound W H
    have RV := Model.mul_sound hb (Model.mul_sound hb K (Model.pow_sound hb V 2)) ZV
    have RD := Model.mul_sound hb (Model.mul_sound hb K (Model.pow_sound hb D 2)) ZD
    have RDP := Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb K D) ZD)
      (Model.add_sound W (Model.mul_sound hb D slopeD))
    have e1 := Model.mul_sound hb (Model.mul_sound hb (Model.sub_sound (Model.zero_sound s t z) Y)
      (Model.sub_sound C RB)) HJ
    have e2 := Model.mul_sound hb (Model.mul_sound hb (Model.mul_sound hb Y IK) EXPdecay)
      (Model.add_sound O RV)
    have e3 := Model.mul_sound hb (Model.mul_sound hb IK EXPu)
      (Model.add_sound (Model.mul_sound hb (Model.sub_sound Y RB) (Model.add_sound O RD)) RDP)
    have eq := Model.sub_sound (Model.add_sound (Model.sub_sound e1 e2) e3) (Model.mul_sound hb RA RB)
    unfold affineModel leftSlopeModel rightSlopeModel cModel rvModel rdModel rdPrimeModel
    convert eq using 1 <;> ring
  have hbound := Model.lower_sound hb
    (show comparisonModel.Encloses s t z _ from Model.sub_sound Hq HT)
  have hconst : 11 * S ≤ 2500 * (comparisonModel.lower : ℝ) := by exact_mod_cast cert.comparison
  exact ((le_div_iff₀ scale_real_pos).2 (by linarith)).trans hbound

private theorem logKernel_mixed_neg_of_compactChecks (cert : CompactChecks) {p : ℕ} (hp : 11 ≤ p)
    {u v : ℝ} (hu : 1 / 2 ≤ u) (hu' : u ≤ 1)
    (hd : 1 / 2 ≤ v - u) (hd' : v - u ≤ 1) :
    deriv (fun y => deriv (fun x => logKernel p x y) u) v < 0 := by
  have hc := comparison_of_checked cert hp hu hu' hd hd'
  rw [show u + (v - u) = v by ring] at hc
  exact logKernel_mixed_neg_of_sixth (by omega) (by linarith) (by linarith) (by linarith)
    ((by norm_num : (0 : ℝ) ≤ 11 / 2500).trans hc)

#print axioms logKernel_mixed_neg_of_compactChecks

private instance (p : Model) (q : Sparse) (r lo : ℕ) :
    Decidable (p.InverseChecked q r lo) := inferInstanceAs
  (Decidable ((lo : ℤ) ≤ p.lower ∧ (p.inverseResidual q).absUpper * scale ≤ r * lo))

set_option maxRecDepth 4096 in
private theorem invU_checked :
    uModel.InverseChecked invUModel.polynomial invUModel.radius 633825300000000000000000000000 := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem invV_checked :
    vModel.InverseChecked invVModel.polynomial invVModel.radius 1267650600000000000000000000000 := by
  decide +kernel

deriving instance DecidableEq for Term, Sparse, Model

private def Model.seriesTrace (x : Model) : ℕ → (ℕ → Model) → List Model → Bool
  | 0, _, [p] => decide (p = Model.zero)
  | n + 1, c, p :: q :: rest =>
    decide (p = (q.mul x).add (c 0)) && Model.seriesTrace x n (fun i => c (i + 1)) (q :: rest)
  | _, _, _ => false

private theorem Model.seriesTrace_eq (x : Model) (n : ℕ) (c : ℕ → Model)
    (p : Model) (xs : List Model) (hc : Model.seriesTrace x n c (p :: xs) = true) :
    Model.series n c x = p := by
  induction n generalizing c p xs with
  | zero =>
    cases xs with
    | nil => exact (of_decide_eq_true hc).symm
    | cons _ _ => simp [Model.seriesTrace] at hc
  | succ n ih =>
    cases xs with
    | nil => simp [Model.seriesTrace] at hc
    | cons q rest =>
      have hs := Bool.and_eq_true_iff.mp hc
      rw [Model.series, ih (fun i => c (i + 1)) q rest hs.2]
      exact (of_decide_eq_true hs.1).symm

private def sinhcCoefficients (n : ℕ) : Model :=
  Model.ofRat (if n % 2 = 0 then 1 / ((n + 1).factorial : ℚ) else 0)

private def phiCoefficients (n : ℕ) : Model :=
  Model.ofRat (1 / ((n + 1).factorial : ℚ))

private def sinhcTrace := CompactSquareWitnesses.sinhcHornerStates.map fun p => Model.candidate p.1 p.2
private def phiTrace := CompactSquareWitnesses.cutoffHornerStates.map fun p => Model.candidate p.1 p.2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- The list contains one checkpoint for each of the 25 Horner multiplications.
private theorem sinhcSeries_checked :
    Model.seriesTrace (hModel.mul aModel) 25 sinhcCoefficients sinhcTrace = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- The list contains one checkpoint for each of the 25 Horner multiplications.
private theorem phiSeries_checked :
    Model.seriesTrace (Model.zero.sub (hModel.mul uModel)) 25 phiCoefficients phiTrace = true := by
  decide +kernel

private theorem sinhcSeries_eq :
    Model.series 25 sinhcCoefficients (hModel.mul aModel) = sinhcTrace.headD Model.zero :=
  Model.seriesTrace_eq _ 25 _ _ _ sinhcSeries_checked

private theorem phiSeries_eq :
    Model.series 25 phiCoefficients (Model.zero.sub (hModel.mul uModel)) = phiTrace.headD Model.zero :=
  Model.seriesTrace_eq _ 25 _ _ _ phiSeries_checked

set_option maxRecDepth 4096 in
private theorem invSinhc_checked :
    sinhcInputModel.InverseChecked invSinhcModel.polynomial invSinhcModel.radius
      1265499490000000000000000000000 := by
  unfold sinhcInputModel sinhcModel
  change ((Model.series 25 sinhcCoefficients _).widen _).InverseChecked _ _ _
  rw [sinhcSeries_eq]
  decide +kernel

set_option maxRecDepth 4096 in
private theorem invCutoff_checked :
    cutoffInputModel.InverseChecked invCutoffModel.polynomial invCutoffModel.radius
      531865370000000000000000000000 := by
  unfold cutoffInputModel cutoffModel
  change (uModel.mul ((Model.series 25 phiCoefficients _).widen _)).InverseChecked _ _ _
  rw [phiSeries_eq]
  decide +kernel

set_option maxRecDepth 4096 in
private theorem root_checked : (scale : ℤ) ≤ (Model.candidate rootModel.polynomial 0).lower := by
  decide +kernel

private theorem Model.seriesTrace_head_eq (x : Model) (n : ℕ) (c : ℕ → Model)
    (xs : List Model) (hc : Model.seriesTrace x n c xs = true) :
    Model.series n c x = xs.headD Model.zero := by
  cases xs with
  | nil => cases n <;> simp [Model.seriesTrace] at hc
  | cons p ps => exact Model.seriesTrace_eq x n c p ps hc

private theorem Model.horner_eq_series (cs : List ℚ) (x : Model) :
    Model.horner cs x =
      Model.series cs.length (fun i => Model.ofRat (cs[i]?.getD 0)) x := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [Model.horner, List.foldr_cons, List.length_cons, Model.series, List.getElem?_cons_zero,
      Option.getD_some, List.getElem?_cons_succ]
    rw [← ih]
    rfl

private def traceModels (data : List (Sparse × Nat)) : List Model :=
  data.map fun p => Model.candidate p.1 p.2

private def computedNorm : ℕ → Model := fun n =>
  if 2 ≤ n ∧ n ≤ 24 then
    (traceModels (CompactSquareWitnesses.normalizedTraces n)).headD Model.zero
  else normMomentModel n


set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow2_eq :
    normalizedMomentCoeffs 0 2 = CompactSquareWitnesses.normalizedRows 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel2_eq : normMomentModel 2 = computedNorm 2 := by
  unfold normMomentModel
  rw [normRow2_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 2).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 2)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 2)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow3_eq :
    normalizedMomentCoeffs 0 3 = CompactSquareWitnesses.normalizedRows 3 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel3_eq : normMomentModel 3 = computedNorm 3 := by
  unfold normMomentModel
  rw [normRow3_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 3).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 3)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 3)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow4_eq :
    normalizedMomentCoeffs 0 4 = CompactSquareWitnesses.normalizedRows 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel4_eq : normMomentModel 4 = computedNorm 4 := by
  unfold normMomentModel
  rw [normRow4_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 4).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 4)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 4)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow5_eq :
    normalizedMomentCoeffs 0 5 = CompactSquareWitnesses.normalizedRows 5 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel5_eq : normMomentModel 5 = computedNorm 5 := by
  unfold normMomentModel
  rw [normRow5_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 5).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 5)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 5)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow6_eq :
    normalizedMomentCoeffs 0 6 = CompactSquareWitnesses.normalizedRows 6 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel6_eq : normMomentModel 6 = computedNorm 6 := by
  unfold normMomentModel
  rw [normRow6_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 6).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 6)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 6)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow7_eq :
    normalizedMomentCoeffs 0 7 = CompactSquareWitnesses.normalizedRows 7 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel7_eq : normMomentModel 7 = computedNorm 7 := by
  unfold normMomentModel
  rw [normRow7_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 7).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 7)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 7)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow8_eq :
    normalizedMomentCoeffs 0 8 = CompactSquareWitnesses.normalizedRows 8 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel8_eq : normMomentModel 8 = computedNorm 8 := by
  unfold normMomentModel
  rw [normRow8_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 8).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 8)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 8)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow9_eq :
    normalizedMomentCoeffs 0 9 = CompactSquareWitnesses.normalizedRows 9 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel9_eq : normMomentModel 9 = computedNorm 9 := by
  unfold normMomentModel
  rw [normRow9_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 9).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 9)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 9)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow10_eq :
    normalizedMomentCoeffs 0 10 = CompactSquareWitnesses.normalizedRows 10 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel10_eq : normMomentModel 10 = computedNorm 10 := by
  unfold normMomentModel
  rw [normRow10_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 10).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 10)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 10)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow11_eq :
    normalizedMomentCoeffs 0 11 = CompactSquareWitnesses.normalizedRows 11 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel11_eq : normMomentModel 11 = computedNorm 11 := by
  unfold normMomentModel
  rw [normRow11_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 11).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 11)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 11)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow12_eq :
    normalizedMomentCoeffs 0 12 = CompactSquareWitnesses.normalizedRows 12 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel12_eq : normMomentModel 12 = computedNorm 12 := by
  unfold normMomentModel
  rw [normRow12_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 12).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 12)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 12)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow13_eq :
    normalizedMomentCoeffs 0 13 = CompactSquareWitnesses.normalizedRows 13 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel13_eq : normMomentModel 13 = computedNorm 13 := by
  unfold normMomentModel
  rw [normRow13_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 13).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 13)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 13)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow14_eq :
    normalizedMomentCoeffs 0 14 = CompactSquareWitnesses.normalizedRows 14 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel14_eq : normMomentModel 14 = computedNorm 14 := by
  unfold normMomentModel
  rw [normRow14_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 14).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 14)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 14)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow15_eq :
    normalizedMomentCoeffs 0 15 = CompactSquareWitnesses.normalizedRows 15 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel15_eq : normMomentModel 15 = computedNorm 15 := by
  unfold normMomentModel
  rw [normRow15_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 15).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 15)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 15)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow16_eq :
    normalizedMomentCoeffs 0 16 = CompactSquareWitnesses.normalizedRows 16 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel16_eq : normMomentModel 16 = computedNorm 16 := by
  unfold normMomentModel
  rw [normRow16_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 16).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 16)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 16)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow17_eq :
    normalizedMomentCoeffs 0 17 = CompactSquareWitnesses.normalizedRows 17 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel17_eq : normMomentModel 17 = computedNorm 17 := by
  unfold normMomentModel
  rw [normRow17_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 17).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 17)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 17)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow18_eq :
    normalizedMomentCoeffs 0 18 = CompactSquareWitnesses.normalizedRows 18 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel18_eq : normMomentModel 18 = computedNorm 18 := by
  unfold normMomentModel
  rw [normRow18_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 18).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 18)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 18)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow19_eq :
    normalizedMomentCoeffs 0 19 = CompactSquareWitnesses.normalizedRows 19 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel19_eq : normMomentModel 19 = computedNorm 19 := by
  unfold normMomentModel
  rw [normRow19_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 19).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 19)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 19)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow20_eq :
    normalizedMomentCoeffs 0 20 = CompactSquareWitnesses.normalizedRows 20 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel20_eq : normMomentModel 20 = computedNorm 20 := by
  unfold normMomentModel
  rw [normRow20_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 20).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 20)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 20)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow21_eq :
    normalizedMomentCoeffs 0 21 = CompactSquareWitnesses.normalizedRows 21 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel21_eq : normMomentModel 21 = computedNorm 21 := by
  unfold normMomentModel
  rw [normRow21_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 21).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 21)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 21)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow22_eq :
    normalizedMomentCoeffs 0 22 = CompactSquareWitnesses.normalizedRows 22 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel22_eq : normMomentModel 22 = computedNorm 22 := by
  unfold normMomentModel
  rw [normRow22_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 22).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 22)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 22)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow23_eq :
    normalizedMomentCoeffs 0 23 = CompactSquareWitnesses.normalizedRows 23 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel23_eq : normMomentModel 23 = computedNorm 23 := by
  unfold normMomentModel
  rw [normRow23_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 23).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 23)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 23)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normRow24_eq :
    normalizedMomentCoeffs 0 24 = CompactSquareWitnesses.normalizedRows 24 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem normModel24_eq : normMomentModel 24 = computedNorm 24 := by
  unfold normMomentModel
  rw [normRow24_eq, Model.horner_eq_series]
  have h : Model.seriesTrace hModel (CompactSquareWitnesses.normalizedRows 24).length
      (fun i => Model.ofRat ((CompactSquareWitnesses.normalizedRows 24)[i]?.getD 0))
      (traceModels (CompactSquareWitnesses.normalizedTraces 24)) = true := by decide +kernel
  exact Model.seriesTrace_eq _ _ _ _ _ h

private theorem normMomentModel_eq_computedNorm : normMomentModel = computedNorm := by
  funext n
  by_cases hn : 2 ≤ n ∧ n ≤ 24
  · have hmin := hn.1
    have hmax := hn.2
    interval_cases n
    · exact normModel2_eq
    · exact normModel3_eq
    · exact normModel4_eq
    · exact normModel5_eq
    · exact normModel6_eq
    · exact normModel7_eq
    · exact normModel8_eq
    · exact normModel9_eq
    · exact normModel10_eq
    · exact normModel11_eq
    · exact normModel12_eq
    · exact normModel13_eq
    · exact normModel14_eq
    · exact normModel15_eq
    · exact normModel16_eq
    · exact normModel17_eq
    · exact normModel18_eq
    · exact normModel19_eq
    · exact normModel20_eq
    · exact normModel21_eq
    · exact normModel22_eq
    · exact normModel23_eq
    · exact normModel24_eq
  · simp [computedNorm, hn]

private def checkedMarginalCoeff (k i : ℕ) : Model :=
  (computedNorm (k + i + 2)).mul (Model.ofRat (((k + i).factorial : ℚ) / i.factorial))

private def checkedRawMoment : ℕ → Model
  | 0 => oneModel
  | 1 => Model.zero
  | n + 2 => (kappaModel.mul (Model.ofRat ((n + 2).factorial : ℚ))).mul (computedNorm (n + 2))

private theorem rawMomentModel_eq_checkedRawMoment : rawMomentModel = checkedRawMoment := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [rawMomentModel, checkedRawMoment, normMomentModel_eq_computedNorm]

private def checkedWeightedCoeff (j n : ℕ) : Model :=
  (Model.sum (j + 1) (fun l =>
    ((cModel.pow (j - l)).mul (checkedRawMoment (n + l))).mul
      (Model.ofRat ((-1 : ℚ) ^ l * (j.choose l : ℚ))))).mul (Model.ofRat (1 / (n.factorial : ℚ)))

private def expCoefficients (n : ℕ) : Model := Model.ofRat (1 / (n.factorial : ℚ))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem zNegUSeries_checked :
    Model.seriesTrace negUModel (23 - 0) (checkedMarginalCoeff 0)
      (traceModels CompactSquareWitnesses.zNegUTrace) = true := by
  decide +kernel

private theorem zNegU_eq : zNegU =
    ((traceModels CompactSquareWitnesses.zNegUTrace).headD Model.zero).widen
      ((2 : ℚ) ^ (0 + 2) * 4 ^ (23 - 0) / ((23 - 0).factorial * 24 * 25)) := by
  unfold zNegU marginalModel
  rw [normMomentModel_eq_computedNorm]
  change (Model.series (23 - 0) (checkedMarginalCoeff 0) negUModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ zNegUSeries_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem zNegVSeries_checked :
    Model.seriesTrace negVModel (23 - 0) (checkedMarginalCoeff 0)
      (traceModels CompactSquareWitnesses.zNegVTrace) = true := by
  decide +kernel

private theorem zNegV_eq : zNegV =
    ((traceModels CompactSquareWitnesses.zNegVTrace).headD Model.zero).widen
      ((2 : ℚ) ^ (0 + 2) * 4 ^ (23 - 0) / ((23 - 0).factorial * 24 * 25)) := by
  unfold zNegV marginalModel
  rw [normMomentModel_eq_computedNorm]
  change (Model.series (23 - 0) (checkedMarginalCoeff 0) negVModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ zNegVSeries_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem zPosVSeries_checked :
    Model.seriesTrace vModel (23 - 0) (checkedMarginalCoeff 0)
      (traceModels CompactSquareWitnesses.zPosVTrace) = true := by
  decide +kernel

private theorem zPosV_eq : zPosV =
    ((traceModels CompactSquareWitnesses.zPosVTrace).headD Model.zero).widen
      ((2 : ℚ) ^ (0 + 2) * 4 ^ (23 - 0) / ((23 - 0).factorial * 24 * 25)) := by
  unfold zPosV marginalModel
  rw [normMomentModel_eq_computedNorm]
  change (Model.series (23 - 0) (checkedMarginalCoeff 0) vModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ zPosVSeries_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem zPosDSeries_checked :
    Model.seriesTrace dModel (23 - 0) (checkedMarginalCoeff 0)
      (traceModels CompactSquareWitnesses.zPosDTrace) = true := by
  decide +kernel

private theorem zPosD_eq : zPosD =
    ((traceModels CompactSquareWitnesses.zPosDTrace).headD Model.zero).widen
      ((2 : ℚ) ^ (0 + 2) * 4 ^ (23 - 0) / ((23 - 0).factorial * 24 * 25)) := by
  unfold zPosD marginalModel
  rw [normMomentModel_eq_computedNorm]
  change (Model.series (23 - 0) (checkedMarginalCoeff 0) dModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ zPosDSeries_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem zNegUPrimeSeries_checked :
    Model.seriesTrace negUModel (23 - 1) (checkedMarginalCoeff 1)
      (traceModels CompactSquareWitnesses.zNegUPrimeTrace) = true := by
  decide +kernel

private theorem zNegUPrime_eq : zNegU' =
    ((traceModels CompactSquareWitnesses.zNegUPrimeTrace).headD Model.zero).widen
      ((2 : ℚ) ^ (1 + 2) * 4 ^ (23 - 1) / ((23 - 1).factorial * 24 * 25)) := by
  unfold zNegU' marginalModel
  rw [normMomentModel_eq_computedNorm]
  change (Model.series (23 - 1) (checkedMarginalCoeff 1) negUModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ zNegUPrimeSeries_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem zNegVPrimeSeries_checked :
    Model.seriesTrace negVModel (23 - 1) (checkedMarginalCoeff 1)
      (traceModels CompactSquareWitnesses.zNegVPrimeTrace) = true := by
  decide +kernel

private theorem zNegVPrime_eq : zNegV' =
    ((traceModels CompactSquareWitnesses.zNegVPrimeTrace).headD Model.zero).widen
      ((2 : ℚ) ^ (1 + 2) * 4 ^ (23 - 1) / ((23 - 1).factorial * 24 * 25)) := by
  unfold zNegV' marginalModel
  rw [normMomentModel_eq_computedNorm]
  change (Model.series (23 - 1) (checkedMarginalCoeff 1) negVModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ zNegVPrimeSeries_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem zPosVPrimeSeries_checked :
    Model.seriesTrace vModel (23 - 1) (checkedMarginalCoeff 1)
      (traceModels CompactSquareWitnesses.zPosVPrimeTrace) = true := by
  decide +kernel

private theorem zPosVPrime_eq : zPosV' =
    ((traceModels CompactSquareWitnesses.zPosVPrimeTrace).headD Model.zero).widen
      ((2 : ℚ) ^ (1 + 2) * 4 ^ (23 - 1) / ((23 - 1).factorial * 24 * 25)) := by
  unfold zPosV' marginalModel
  rw [normMomentModel_eq_computedNorm]
  change (Model.series (23 - 1) (checkedMarginalCoeff 1) vModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ zPosVPrimeSeries_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem zPosDPrimeSeries_checked :
    Model.seriesTrace dModel (23 - 1) (checkedMarginalCoeff 1)
      (traceModels CompactSquareWitnesses.zPosDPrimeTrace) = true := by
  decide +kernel

private theorem zPosDPrime_eq : zPosD' =
    ((traceModels CompactSquareWitnesses.zPosDPrimeTrace).headD Model.zero).widen
      ((2 : ℚ) ^ (1 + 2) * 4 ^ (23 - 1) / ((23 - 1).factorial * 24 * 25)) := by
  unfold zPosD' marginalModel
  rw [normMomentModel_eq_computedNorm]
  change (Model.series (23 - 1) (checkedMarginalCoeff 1) dModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ zPosDPrimeSeries_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem zPosDSecondSeries_checked :
    Model.seriesTrace dModel (23 - 2) (checkedMarginalCoeff 2)
      (traceModels CompactSquareWitnesses.zPosDSecondTrace) = true := by
  decide +kernel

private theorem zPosDSecond_eq : zPosD'' =
    ((traceModels CompactSquareWitnesses.zPosDSecondTrace).headD Model.zero).widen
      ((2 : ℚ) ^ (2 + 2) * 4 ^ (23 - 2) / ((23 - 2).factorial * 24 * 25)) := by
  unfold zPosD'' marginalModel
  rw [normMomentModel_eq_computedNorm]
  change (Model.series (23 - 2) (checkedMarginalCoeff 2) dModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ zPosDSecondSeries_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem jointMom0Series_checked :
    Model.seriesTrace tModel (25 - 0) (checkedWeightedCoeff 0)
      (traceModels CompactSquareWitnesses.jointMom0Trace) = true := by
  decide +kernel

private theorem jointMom0_eq : jointMom0 =
    ((traceModels CompactSquareWitnesses.jointMom0Trace).headD Model.zero).widen
      ((36 / 11 : ℚ) ^ 0 * (7 / 22) * 3 ^ (25 - 0) / ((25 - 0).factorial : ℚ)) := by
  unfold jointMom0 weightedMomentModel
  rw [rawMomentModel_eq_checkedRawMoment]
  change (Model.series (25 - 0) (checkedWeightedCoeff 0) tModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ jointMom0Series_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem jointMom2Series_checked :
    Model.seriesTrace tModel (25 - 2) (checkedWeightedCoeff 2)
      (traceModels CompactSquareWitnesses.jointMom2Trace) = true := by
  decide +kernel

private theorem jointMom2_eq : jointMom2 =
    ((traceModels CompactSquareWitnesses.jointMom2Trace).headD Model.zero).widen
      ((36 / 11 : ℚ) ^ 2 * (7 / 22) * 3 ^ (25 - 2) / ((25 - 2).factorial : ℚ)) := by
  unfold jointMom2 weightedMomentModel
  rw [rawMomentModel_eq_checkedRawMoment]
  change (Model.series (25 - 2) (checkedWeightedCoeff 2) tModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ jointMom2Series_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem jointMom4Series_checked :
    Model.seriesTrace tModel (25 - 4) (checkedWeightedCoeff 4)
      (traceModels CompactSquareWitnesses.jointMom4Trace) = true := by
  decide +kernel

private theorem jointMom4_eq : jointMom4 =
    ((traceModels CompactSquareWitnesses.jointMom4Trace).headD Model.zero).widen
      ((36 / 11 : ℚ) ^ 4 * (7 / 22) * 3 ^ (25 - 4) / ((25 - 4).factorial : ℚ)) := by
  unfold jointMom4 weightedMomentModel
  rw [rawMomentModel_eq_checkedRawMoment]
  change (Model.series (25 - 4) (checkedWeightedCoeff 4) tModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ jointMom4Series_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem jointMom6Series_checked :
    Model.seriesTrace tModel (25 - 6) (checkedWeightedCoeff 6)
      (traceModels CompactSquareWitnesses.jointMom6Trace) = true := by
  decide +kernel

private theorem jointMom6_eq : jointMom6 =
    ((traceModels CompactSquareWitnesses.jointMom6Trace).headD Model.zero).widen
      ((36 / 11 : ℚ) ^ 6 * (7 / 22) * 3 ^ (25 - 6) / ((25 - 6).factorial : ℚ)) := by
  unfold jointMom6 weightedMomentModel
  rw [rawMomentModel_eq_checkedRawMoment]
  change (Model.series (25 - 6) (checkedWeightedCoeff 6) tModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ jointMom6Series_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem expUSeries_checked :
    Model.seriesTrace uModel 25 expCoefficients (traceModels CompactSquareWitnesses.expUTrace) = true := by
  decide +kernel

private theorem expU_eq : expModel uModel =
    ((traceModels CompactSquareWitnesses.expUTrace).headD Model.zero).widen
      (2 * (3 / 2 : ℚ) ^ 25 / ((25 : ℕ).factorial : ℚ)) := by
  change (Model.series 25 expCoefficients uModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ expUSeries_checked]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
-- Check one finite coefficient row or polynomial trace.
private theorem expDecaySeries_checked :
    Model.seriesTrace expArgModel 25 expCoefficients (traceModels CompactSquareWitnesses.expDecayTrace) = true := by
  decide +kernel

private theorem expDecay_eq : expModel expArgModel =
    ((traceModels CompactSquareWitnesses.expDecayTrace).headD Model.zero).widen
      (2 * (3 / 2 : ℚ) ^ 25 / ((25 : ℕ).factorial : ℚ)) := by
  change (Model.series 25 expCoefficients expArgModel).widen _ = _
  rw [Model.seriesTrace_head_eq _ _ _ _ expDecaySeries_checked]

private def modelDatum (p : Sparse × Nat) : Model := Model.candidate p.1 p.2

private def comparisonStep1Expr : Model := (zNegU').mul (invNegUModel)
private def comparisonStep1Value : Model := modelDatum CompactSquareWitnesses.comparisonStep1Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep1_eq : comparisonStep1Expr = comparisonStep1Value := by
  unfold comparisonStep1Expr
  rw [zNegUPrime_eq]
  decide +kernel

private def comparisonStep2Expr : Model := (zNegV').mul (invNegVModel)
private def comparisonStep2Value : Model := modelDatum CompactSquareWitnesses.comparisonStep2Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep2_eq : comparisonStep2Expr = comparisonStep2Value := by
  unfold comparisonStep2Expr
  rw [zNegVPrime_eq]
  decide +kernel

private def comparisonStep3Expr : Model := (zPosV').mul (invPosVModel)
private def comparisonStep3Value : Model := modelDatum CompactSquareWitnesses.comparisonStep3Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep3_eq : comparisonStep3Expr = comparisonStep3Value := by
  unfold comparisonStep3Expr
  rw [zPosVPrime_eq]
  decide +kernel

private def comparisonStep4Expr : Model := (zPosD').mul (invPosDModel)
private def comparisonStep4Value : Model := modelDatum CompactSquareWitnesses.comparisonStep4Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep4_eq : comparisonStep4Expr = comparisonStep4Value := by
  unfold comparisonStep4Expr
  rw [zPosDPrime_eq]
  decide +kernel

private def comparisonStep5Expr : Model := (zPosD'').mul (invPosDModel)
private def comparisonStep5Value : Model := modelDatum CompactSquareWitnesses.comparisonStep5Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep5_eq : comparisonStep5Expr = comparisonStep5Value := by
  unfold comparisonStep5Expr
  rw [zPosDSecond_eq]
  decide +kernel

private def comparisonStep6Expr : Model := (comparisonStep4Expr).mul (comparisonStep4Expr)
private def comparisonStep6Value : Model := modelDatum CompactSquareWitnesses.comparisonStep6Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep6_eq : comparisonStep6Expr = comparisonStep6Value := by
  unfold comparisonStep6Expr
  rw [comparisonStep4_eq]
  decide +kernel

private def comparisonStep7Expr : Model := (comparisonStep5Expr).sub (comparisonStep6Expr)
private def comparisonStep7Value : Model := modelDatum CompactSquareWitnesses.comparisonStep7Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep7_eq : comparisonStep7Expr = comparisonStep7Value := by
  unfold comparisonStep7Expr
  rw [comparisonStep5_eq, comparisonStep6_eq]
  decide +kernel

private def comparisonStep8Expr : Model := (comparisonStep1Expr).mul (halfModel)
private def comparisonStep8Value : Model := modelDatum CompactSquareWitnesses.comparisonStep8Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep8_eq : comparisonStep8Expr = comparisonStep8Value := by
  unfold comparisonStep8Expr
  rw [comparisonStep1_eq]
  decide +kernel

private def comparisonStep9Expr : Model := (invUModel).sub (comparisonStep8Expr)
private def comparisonStep9Value : Model := modelDatum CompactSquareWitnesses.comparisonStep9Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep9_eq : comparisonStep9Expr = comparisonStep9Value := by
  unfold comparisonStep9Expr
  rw [comparisonStep8_eq]
  decide +kernel

private def comparisonStep10Expr : Model := (comparisonStep2Expr).mul (halfModel)
private def comparisonStep10Value : Model := modelDatum CompactSquareWitnesses.comparisonStep10Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep10_eq : comparisonStep10Expr = comparisonStep10Value := by
  unfold comparisonStep10Expr
  rw [comparisonStep2_eq]
  decide +kernel

private def comparisonStep11Expr : Model := (invVModel).sub (comparisonStep10Expr)
private def comparisonStep11Value : Model := modelDatum CompactSquareWitnesses.comparisonStep11Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep11_eq : comparisonStep11Expr = comparisonStep11Value := by
  unfold comparisonStep11Expr
  rw [comparisonStep10_eq]
  decide +kernel

private def comparisonStep12Expr : Model := (dModel).mul (dModel)
private def comparisonStep12Value : Model := modelDatum CompactSquareWitnesses.comparisonStep12Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep12_eq : comparisonStep12Expr = comparisonStep12Value := by
  decide +kernel

private def comparisonStep13Expr : Model := (kappaModel).mul (comparisonStep12Expr)
private def comparisonStep13Value : Model := modelDatum CompactSquareWitnesses.comparisonStep13Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep13_eq : comparisonStep13Expr = comparisonStep13Value := by
  unfold comparisonStep13Expr
  rw [comparisonStep12_eq]
  decide +kernel

private def comparisonStep14Expr : Model := (comparisonStep13Expr).mul (zPosD)
private def comparisonStep14Value : Model := modelDatum CompactSquareWitnesses.comparisonStep14Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep14_eq : comparisonStep14Expr = comparisonStep14Value := by
  unfold comparisonStep14Expr
  rw [comparisonStep13_eq, zPosD_eq]
  decide +kernel

private def comparisonStep15Expr : Model := (vModel).mul (vModel)
private def comparisonStep15Value : Model := modelDatum CompactSquareWitnesses.comparisonStep15Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep15_eq : comparisonStep15Expr = comparisonStep15Value := by
  decide +kernel

private def comparisonStep16Expr : Model := (kappaModel).mul (comparisonStep15Expr)
private def comparisonStep16Value : Model := modelDatum CompactSquareWitnesses.comparisonStep16Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep16_eq : comparisonStep16Expr = comparisonStep16Value := by
  unfold comparisonStep16Expr
  rw [comparisonStep15_eq]
  decide +kernel

private def comparisonStep17Expr : Model := (comparisonStep16Expr).mul (zPosV)
private def comparisonStep17Value : Model := modelDatum CompactSquareWitnesses.comparisonStep17Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep17_eq : comparisonStep17Expr = comparisonStep17Value := by
  unfold comparisonStep17Expr
  rw [comparisonStep16_eq, zPosV_eq]
  decide +kernel

private def comparisonStep18Expr : Model := (kappaModel).mul (dModel)
private def comparisonStep18Value : Model := modelDatum CompactSquareWitnesses.comparisonStep18Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep18_eq : comparisonStep18Expr = comparisonStep18Value := by
  decide +kernel

private def comparisonStep19Expr : Model := (comparisonStep18Expr).mul (zPosD)
private def comparisonStep19Value : Model := modelDatum CompactSquareWitnesses.comparisonStep19Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep19_eq : comparisonStep19Expr = comparisonStep19Value := by
  unfold comparisonStep19Expr
  rw [comparisonStep18_eq, zPosD_eq]
  decide +kernel

private def comparisonStep20Expr : Model := (dModel).mul (comparisonStep4Expr)
private def comparisonStep20Value : Model := modelDatum CompactSquareWitnesses.comparisonStep20Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep20_eq : comparisonStep20Expr = comparisonStep20Value := by
  unfold comparisonStep20Expr
  rw [comparisonStep4_eq]
  decide +kernel

private def comparisonStep21Expr : Model := (twoModel).add (comparisonStep20Expr)
private def comparisonStep21Value : Model := modelDatum CompactSquareWitnesses.comparisonStep21Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep21_eq : comparisonStep21Expr = comparisonStep21Value := by
  unfold comparisonStep21Expr
  rw [comparisonStep20_eq]
  decide +kernel

private def comparisonStep22Expr : Model := (comparisonStep19Expr).mul (comparisonStep21Expr)
private def comparisonStep22Value : Model := modelDatum CompactSquareWitnesses.comparisonStep22Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep22_eq : comparisonStep22Expr = comparisonStep22Value := by
  unfold comparisonStep22Expr
  rw [comparisonStep19_eq, comparisonStep21_eq]
  decide +kernel

private def comparisonStep23Expr : Model := (comparisonStep4Expr).sub (comparisonStep1Expr)
private def comparisonStep23Value : Model := modelDatum CompactSquareWitnesses.comparisonStep23Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep23_eq : comparisonStep23Expr = comparisonStep23Value := by
  unfold comparisonStep23Expr
  rw [comparisonStep4_eq, comparisonStep1_eq]
  decide +kernel

private def comparisonStep24Expr : Model := (comparisonStep3Expr).add (comparisonStep4Expr)
private def comparisonStep24Value : Model := modelDatum CompactSquareWitnesses.comparisonStep24Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep24_eq : comparisonStep24Expr = comparisonStep24Value := by
  unfold comparisonStep24Expr
  rw [comparisonStep3_eq, comparisonStep4_eq]
  decide +kernel

private def comparisonStep25Expr : Model := (comparisonStep24Expr).add (comparisonStep2Expr)
private def comparisonStep25Value : Model := modelDatum CompactSquareWitnesses.comparisonStep25Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep25_eq : comparisonStep25Expr = comparisonStep25Value := by
  unfold comparisonStep25Expr
  rw [comparisonStep24_eq, comparisonStep2_eq]
  decide +kernel

private def comparisonStep26Expr : Model := (comparisonStep25Expr).mul (invUModel)
private def comparisonStep26Value : Model := modelDatum CompactSquareWitnesses.comparisonStep26Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep26_eq : comparisonStep26Expr = comparisonStep26Value := by
  unfold comparisonStep26Expr
  rw [comparisonStep25_eq]
  decide +kernel

private def comparisonStep27Expr : Model := (comparisonStep26Expr).mul (halfModel)
private def comparisonStep27Value : Model := modelDatum CompactSquareWitnesses.comparisonStep27Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep27_eq : comparisonStep27Expr = comparisonStep27Value := by
  unfold comparisonStep27Expr
  rw [comparisonStep26_eq]
  decide +kernel

private def comparisonStep28Expr : Model := (comparisonStep23Expr).mul (comparisonStep25Expr)
private def comparisonStep28Value : Model := modelDatum CompactSquareWitnesses.comparisonStep28Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep28_eq : comparisonStep28Expr = comparisonStep28Value := by
  unfold comparisonStep28Expr
  rw [comparisonStep23_eq, comparisonStep25_eq]
  decide +kernel

private def comparisonStep29Expr : Model := (comparisonStep28Expr).mul (Model.ofRat (1 / 4))
private def comparisonStep29Value : Model := modelDatum CompactSquareWitnesses.comparisonStep29Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep29_eq : comparisonStep29Expr = comparisonStep29Value := by
  unfold comparisonStep29Expr
  rw [comparisonStep28_eq]
  decide +kernel

private def comparisonStep30Expr : Model := (comparisonStep27Expr).add (comparisonStep29Expr)
private def comparisonStep30Value : Model := modelDatum CompactSquareWitnesses.comparisonStep30Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep30_eq : comparisonStep30Expr = comparisonStep30Value := by
  unfold comparisonStep30Expr
  rw [comparisonStep27_eq, comparisonStep29_eq]
  decide +kernel

private def comparisonStep31Expr : Model := (comparisonStep23Expr).add (comparisonStep25Expr)
private def comparisonStep31Value : Model := modelDatum CompactSquareWitnesses.comparisonStep31Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep31_eq : comparisonStep31Expr = comparisonStep31Value := by
  unfold comparisonStep31Expr
  rw [comparisonStep23_eq, comparisonStep25_eq]
  decide +kernel

private def comparisonStep32Expr : Model := (comparisonStep31Expr).mul (halfModel)
private def comparisonStep32Value : Model := modelDatum CompactSquareWitnesses.comparisonStep32Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep32_eq : comparisonStep32Expr = comparisonStep32Value := by
  unfold comparisonStep32Expr
  rw [comparisonStep31_eq]
  decide +kernel

private def comparisonStep33Expr : Model := (invUModel).add (comparisonStep32Expr)
private def comparisonStep33Value : Model := modelDatum CompactSquareWitnesses.comparisonStep33Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep33_eq : comparisonStep33Expr = comparisonStep33Value := by
  unfold comparisonStep33Expr
  rw [comparisonStep32_eq]
  decide +kernel

private def comparisonStep34Expr : Model := (comparisonStep7Expr).mul (halfModel)
private def comparisonStep34Value : Model := modelDatum CompactSquareWitnesses.comparisonStep34Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep34_eq : comparisonStep34Expr = comparisonStep34Value := by
  unfold comparisonStep34Expr
  rw [comparisonStep7_eq]
  decide +kernel

private def comparisonStep35Expr : Model := (comparisonStep30Expr).add (comparisonStep34Expr)
private def comparisonStep35Value : Model := modelDatum CompactSquareWitnesses.comparisonStep35Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep35_eq : comparisonStep35Expr = comparisonStep35Value := by
  unfold comparisonStep35Expr
  rw [comparisonStep30_eq, comparisonStep34_eq]
  decide +kernel

private def comparisonStep36Expr : Model := (dModel).mul (comparisonStep35Expr)
private def comparisonStep36Value : Model := modelDatum CompactSquareWitnesses.comparisonStep36Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep36_eq : comparisonStep36Expr = comparisonStep36Value := by
  unfold comparisonStep36Expr
  rw [comparisonStep35_eq]
  decide +kernel

private def comparisonStep37Expr : Model := (comparisonStep33Expr).add (comparisonStep36Expr)
private def comparisonStep37Value : Model := modelDatum CompactSquareWitnesses.comparisonStep37Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep37_eq : comparisonStep37Expr = comparisonStep37Value := by
  unfold comparisonStep37Expr
  rw [comparisonStep33_eq, comparisonStep36_eq]
  decide +kernel

private def comparisonStep38Expr : Model := (Model.zero).sub (kappaModel)
private def comparisonStep38Value : Model := modelDatum CompactSquareWitnesses.comparisonStep38Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep38_eq : comparisonStep38Expr = comparisonStep38Value := by
  decide +kernel

private def comparisonStep39Expr : Model := (comparisonStep38Expr).mul (vModel)
private def comparisonStep39Value : Model := modelDatum CompactSquareWitnesses.comparisonStep39Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep39_eq : comparisonStep39Expr = comparisonStep39Value := by
  unfold comparisonStep39Expr
  rw [comparisonStep38_eq]
  decide +kernel

private def comparisonStep40Expr : Model := (comparisonStep39Expr).mul (rootModel)
private def comparisonStep40Value : Model := modelDatum CompactSquareWitnesses.comparisonStep40Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep40_eq : comparisonStep40Expr = comparisonStep40Value := by
  unfold comparisonStep40Expr
  rw [comparisonStep39_eq]
  decide +kernel

private def computedRadicalExpr : Model := (comparisonStep40Expr).mul (comparisonStep37Expr)
private def computedRadicalValue : Model := modelDatum CompactSquareWitnesses.computedRadicalData

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem computedRadical_eq : computedRadicalExpr = computedRadicalValue := by
  unfold computedRadicalExpr
  rw [comparisonStep40_eq, comparisonStep37_eq]
  decide +kernel

private def comparisonStep42Expr : Model := (aModel).mul (aModel)
private def comparisonStep42Value : Model := modelDatum CompactSquareWitnesses.comparisonStep42Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep42_eq : comparisonStep42Expr = comparisonStep42Value := by
  decide +kernel

private def comparisonStep43Expr : Model := (comparisonStep42Expr).mul (Model.ofRat (1 / 6))
private def comparisonStep43Value : Model := modelDatum CompactSquareWitnesses.comparisonStep43Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep43_eq : comparisonStep43Expr = comparisonStep43Value := by
  unfold comparisonStep43Expr
  rw [comparisonStep42_eq]
  decide +kernel

private def comparisonStep44Expr : Model := (comparisonStep43Expr).mul (jointMom2)
private def comparisonStep44Value : Model := modelDatum CompactSquareWitnesses.comparisonStep44Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep44_eq : comparisonStep44Expr = comparisonStep44Value := by
  unfold comparisonStep44Expr
  rw [comparisonStep43_eq, jointMom2_eq]
  decide +kernel

private def comparisonStep45Expr : Model := (comparisonStep42Expr).mul (comparisonStep42Expr)
private def comparisonStep45Value : Model := modelDatum CompactSquareWitnesses.comparisonStep45Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep45_eq : comparisonStep45Expr = comparisonStep45Value := by
  unfold comparisonStep45Expr
  rw [comparisonStep42_eq]
  decide +kernel

private def comparisonStep46Expr : Model := (comparisonStep45Expr).mul (Model.ofRat (1 / 120))
private def comparisonStep46Value : Model := modelDatum CompactSquareWitnesses.comparisonStep46Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep46_eq : comparisonStep46Expr = comparisonStep46Value := by
  unfold comparisonStep46Expr
  rw [comparisonStep45_eq]
  decide +kernel

private def comparisonStep47Expr : Model := (comparisonStep46Expr).mul (jointMom4)
private def comparisonStep47Value : Model := modelDatum CompactSquareWitnesses.comparisonStep47Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep47_eq : comparisonStep47Expr = comparisonStep47Value := by
  unfold comparisonStep47Expr
  rw [comparisonStep46_eq, jointMom4_eq]
  decide +kernel

private def comparisonStep48Expr : Model := (comparisonStep42Expr).mul (aModel)
private def comparisonStep48Value : Model := modelDatum CompactSquareWitnesses.comparisonStep48Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep48_eq : comparisonStep48Expr = comparisonStep48Value := by
  unfold comparisonStep48Expr
  rw [comparisonStep42_eq]
  decide +kernel

private def comparisonStep49Expr : Model := (comparisonStep48Expr).mul (comparisonStep48Expr)
private def comparisonStep49Value : Model := modelDatum CompactSquareWitnesses.comparisonStep49Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep49_eq : comparisonStep49Expr = comparisonStep49Value := by
  unfold comparisonStep49Expr
  rw [comparisonStep48_eq]
  decide +kernel

private def comparisonStep50Expr : Model := (Model.ofRat (287 / 1458000)).mul (comparisonStep49Expr)
private def comparisonStep50Value : Model := modelDatum CompactSquareWitnesses.comparisonStep50Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep50_eq : comparisonStep50Expr = comparisonStep50Value := by
  unfold comparisonStep50Expr
  rw [comparisonStep49_eq]
  decide +kernel

private def comparisonStep51Expr : Model := (comparisonStep50Expr).mul (jointMom6)
private def comparisonStep51Value : Model := modelDatum CompactSquareWitnesses.comparisonStep51Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep51_eq : comparisonStep51Expr = comparisonStep51Value := by
  unfold comparisonStep51Expr
  rw [comparisonStep50_eq, jointMom6_eq]
  decide +kernel

private def comparisonStep52Expr : Model := (jointMom0).add (comparisonStep44Expr)
private def comparisonStep52Value : Model := modelDatum CompactSquareWitnesses.comparisonStep52Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep52_eq : comparisonStep52Expr = comparisonStep52Value := by
  unfold comparisonStep52Expr
  rw [jointMom0_eq, comparisonStep44_eq]
  decide +kernel

private def comparisonStep53Expr : Model := (comparisonStep52Expr).add (comparisonStep47Expr)
private def comparisonStep53Value : Model := modelDatum CompactSquareWitnesses.comparisonStep53Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep53_eq : comparisonStep53Expr = comparisonStep53Value := by
  unfold comparisonStep53Expr
  rw [comparisonStep52_eq, comparisonStep47_eq]
  decide +kernel

private def comparisonStep54Expr : Model := (comparisonStep53Expr).add (comparisonStep51Expr)
private def comparisonStep54Value : Model := modelDatum CompactSquareWitnesses.comparisonStep54Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep54_eq : comparisonStep54Expr = comparisonStep54Value := by
  unfold comparisonStep54Expr
  rw [comparisonStep53_eq, comparisonStep51_eq]
  decide +kernel

private def comparisonStep55Expr : Model := (comparisonStep54Expr).mul (invSinhcModel)
private def comparisonStep55Value : Model := modelDatum CompactSquareWitnesses.comparisonStep55Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep55_eq : comparisonStep55Expr = comparisonStep55Value := by
  unfold comparisonStep55Expr
  rw [comparisonStep54_eq]
  decide +kernel

private def comparisonStep56Expr : Model := (oneModel).add (invCutoffModel)
private def comparisonStep56Value : Model := modelDatum CompactSquareWitnesses.comparisonStep56Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep56_eq : comparisonStep56Expr = comparisonStep56Value := by
  decide +kernel

private def comparisonStep57Expr : Model := (comparisonStep56Expr).add (comparisonStep9Expr)
private def comparisonStep57Value : Model := modelDatum CompactSquareWitnesses.comparisonStep57Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep57_eq : comparisonStep57Expr = comparisonStep57Value := by
  unfold comparisonStep57Expr
  rw [comparisonStep56_eq, comparisonStep9_eq]
  decide +kernel

private def comparisonStep58Expr : Model := (Model.zero).sub (comparisonStep57Expr)
private def comparisonStep58Value : Model := modelDatum CompactSquareWitnesses.comparisonStep58Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep58_eq : comparisonStep58Expr = comparisonStep58Value := by
  unfold comparisonStep58Expr
  rw [comparisonStep57_eq]
  decide +kernel

private def comparisonStep59Expr : Model := (cModel).sub (comparisonStep11Expr)
private def comparisonStep59Value : Model := modelDatum CompactSquareWitnesses.comparisonStep59Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep59_eq : comparisonStep59Expr = comparisonStep59Value := by
  unfold comparisonStep59Expr
  rw [comparisonStep11_eq]
  decide +kernel

private def comparisonStep60Expr : Model := (comparisonStep58Expr).mul (comparisonStep59Expr)
private def comparisonStep60Value : Model := modelDatum CompactSquareWitnesses.comparisonStep60Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep60_eq : comparisonStep60Expr = comparisonStep60Value := by
  unfold comparisonStep60Expr
  rw [comparisonStep58_eq, comparisonStep59_eq]
  decide +kernel

private def comparisonStep61Expr : Model := (comparisonStep60Expr).mul (comparisonStep55Expr)
private def comparisonStep61Value : Model := modelDatum CompactSquareWitnesses.comparisonStep61Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep61_eq : comparisonStep61Expr = comparisonStep61Value := by
  unfold comparisonStep61Expr
  rw [comparisonStep60_eq, comparisonStep55_eq]
  decide +kernel

private def comparisonStep62Expr : Model := (comparisonStep57Expr).mul (invCutoffModel)
private def comparisonStep62Value : Model := modelDatum CompactSquareWitnesses.comparisonStep62Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep62_eq : comparisonStep62Expr = comparisonStep62Value := by
  unfold comparisonStep62Expr
  rw [comparisonStep57_eq]
  decide +kernel

private def comparisonStep63Expr : Model := (comparisonStep62Expr).mul (expModel expArgModel)
private def comparisonStep63Value : Model := modelDatum CompactSquareWitnesses.comparisonStep63Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep63_eq : comparisonStep63Expr = comparisonStep63Value := by
  unfold comparisonStep63Expr
  rw [comparisonStep62_eq, expDecay_eq]
  decide +kernel

private def comparisonStep64Expr : Model := (oneModel).add (comparisonStep17Expr)
private def comparisonStep64Value : Model := modelDatum CompactSquareWitnesses.comparisonStep64Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep64_eq : comparisonStep64Expr = comparisonStep64Value := by
  unfold comparisonStep64Expr
  rw [comparisonStep17_eq]
  decide +kernel

private def comparisonStep65Expr : Model := (comparisonStep63Expr).mul (comparisonStep64Expr)
private def comparisonStep65Value : Model := modelDatum CompactSquareWitnesses.comparisonStep65Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep65_eq : comparisonStep65Expr = comparisonStep65Value := by
  unfold comparisonStep65Expr
  rw [comparisonStep63_eq, comparisonStep64_eq]
  decide +kernel

private def comparisonStep66Expr : Model := (invCutoffModel).mul (expModel uModel)
private def comparisonStep66Value : Model := modelDatum CompactSquareWitnesses.comparisonStep66Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep66_eq : comparisonStep66Expr = comparisonStep66Value := by
  unfold comparisonStep66Expr
  rw [expU_eq]
  decide +kernel

private def comparisonStep67Expr : Model := (comparisonStep57Expr).sub (comparisonStep11Expr)
private def comparisonStep67Value : Model := modelDatum CompactSquareWitnesses.comparisonStep67Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep67_eq : comparisonStep67Expr = comparisonStep67Value := by
  unfold comparisonStep67Expr
  rw [comparisonStep57_eq, comparisonStep11_eq]
  decide +kernel

private def comparisonStep68Expr : Model := (oneModel).add (comparisonStep14Expr)
private def comparisonStep68Value : Model := modelDatum CompactSquareWitnesses.comparisonStep68Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep68_eq : comparisonStep68Expr = comparisonStep68Value := by
  unfold comparisonStep68Expr
  rw [comparisonStep14_eq]
  decide +kernel

private def comparisonStep69Expr : Model := (comparisonStep67Expr).mul (comparisonStep68Expr)
private def comparisonStep69Value : Model := modelDatum CompactSquareWitnesses.comparisonStep69Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep69_eq : comparisonStep69Expr = comparisonStep69Value := by
  unfold comparisonStep69Expr
  rw [comparisonStep67_eq, comparisonStep68_eq]
  decide +kernel

private def comparisonStep70Expr : Model := (comparisonStep69Expr).add (comparisonStep22Expr)
private def comparisonStep70Value : Model := modelDatum CompactSquareWitnesses.comparisonStep70Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep70_eq : comparisonStep70Expr = comparisonStep70Value := by
  unfold comparisonStep70Expr
  rw [comparisonStep69_eq, comparisonStep22_eq]
  decide +kernel

private def comparisonStep71Expr : Model := (comparisonStep66Expr).mul (comparisonStep70Expr)
private def comparisonStep71Value : Model := modelDatum CompactSquareWitnesses.comparisonStep71Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep71_eq : comparisonStep71Expr = comparisonStep71Value := by
  unfold comparisonStep71Expr
  rw [comparisonStep66_eq, comparisonStep70_eq]
  decide +kernel

private def comparisonStep72Expr : Model := (comparisonStep61Expr).sub (comparisonStep65Expr)
private def comparisonStep72Value : Model := modelDatum CompactSquareWitnesses.comparisonStep72Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep72_eq : comparisonStep72Expr = comparisonStep72Value := by
  unfold comparisonStep72Expr
  rw [comparisonStep61_eq, comparisonStep65_eq]
  decide +kernel

private def comparisonStep73Expr : Model := (comparisonStep72Expr).add (comparisonStep71Expr)
private def comparisonStep73Value : Model := modelDatum CompactSquareWitnesses.comparisonStep73Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep73_eq : comparisonStep73Expr = comparisonStep73Value := by
  unfold comparisonStep73Expr
  rw [comparisonStep72_eq, comparisonStep71_eq]
  decide +kernel

private def comparisonStep74Expr : Model := (comparisonStep9Expr).mul (comparisonStep11Expr)
private def comparisonStep74Value : Model := modelDatum CompactSquareWitnesses.comparisonStep74Data

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem comparisonStep74_eq : comparisonStep74Expr = comparisonStep74Value := by
  unfold comparisonStep74Expr
  rw [comparisonStep9_eq, comparisonStep11_eq]
  decide +kernel

private def computedAffineExpr : Model := (comparisonStep73Expr).sub (comparisonStep74Expr)
private def computedAffineValue : Model := modelDatum CompactSquareWitnesses.computedAffineData

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem computedAffine_eq : computedAffineExpr = computedAffineValue := by
  unfold computedAffineExpr
  rw [comparisonStep73_eq, comparisonStep74_eq]
  decide +kernel

private def computedComparisonExpr : Model := (computedRadicalExpr).sub (computedAffineExpr)
private def computedComparisonValue : Model := modelDatum CompactSquareWitnesses.computedComparisonData

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem computedComparison_eq : computedComparisonExpr = computedComparisonValue := by
  unfold computedComparisonExpr
  rw [computedRadical_eq, computedAffine_eq]
  decide +kernel

private def computedRadicandExpr : Model := (zPosV).mul (zPosD)
private def computedRadicandValue : Model := modelDatum CompactSquareWitnesses.computedRadicandData

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check the operation on previously evaluated operands.
private theorem computedRadicand_eq : computedRadicandExpr = computedRadicandValue := by
  unfold computedRadicandExpr
  rw [zPosV_eq, zPosD_eq]
  decide +kernel


set_option maxRecDepth 8192 in
private theorem Model.pow_two_eq (m : Model) : m.pow 2 = m.mul m := by
  norm_num [Model.pow]

private theorem Model.pow_four_eq (m : Model) :
    m.pow 4 = (m.mul m).mul (m.mul m) := by
  rw [Model.pow]
  norm_num [Model.pow_two_eq]

private theorem Model.pow_six_eq (m : Model) :
    m.pow 6 = ((m.mul m).mul m).mul ((m.mul m).mul m) := by
  rw [Model.pow]
  norm_num [Model.pow, Model.pow_two_eq]

set_option maxRecDepth 4096 in
private theorem comparisonModel_eq : comparisonModel = computedComparisonValue := by
  have he : comparisonModel = computedComparisonExpr := by
    simp only [comparisonModel, radicalModel, affineModel, jointModel, Model.pow_two_eq,
      Model.pow_four_eq, Model.pow_six_eq, suModel, svModel, tvModel, tdModel, wdModel, rdModel,
      rvModel, rdPrimeModel, leftSlopeModel, rightSlopeModel, comparisonStep1Expr,
      comparisonStep2Expr, comparisonStep3Expr, comparisonStep4Expr, comparisonStep5Expr,
      comparisonStep6Expr, comparisonStep7Expr, comparisonStep8Expr, comparisonStep9Expr,
      comparisonStep10Expr, comparisonStep11Expr, comparisonStep12Expr, comparisonStep13Expr,
      comparisonStep14Expr, comparisonStep15Expr, comparisonStep16Expr, comparisonStep17Expr,
      comparisonStep18Expr, comparisonStep19Expr, comparisonStep20Expr, comparisonStep21Expr,
      comparisonStep22Expr, comparisonStep23Expr, comparisonStep24Expr, comparisonStep25Expr,
      comparisonStep26Expr, comparisonStep27Expr, comparisonStep28Expr, comparisonStep29Expr,
      comparisonStep30Expr, comparisonStep31Expr, comparisonStep32Expr, comparisonStep33Expr,
      comparisonStep34Expr, comparisonStep35Expr, comparisonStep36Expr, comparisonStep37Expr,
      comparisonStep38Expr, comparisonStep39Expr, comparisonStep40Expr, computedRadicalExpr,
      comparisonStep42Expr, comparisonStep43Expr, comparisonStep44Expr, comparisonStep45Expr,
      comparisonStep46Expr, comparisonStep47Expr, comparisonStep48Expr, comparisonStep49Expr,
      comparisonStep50Expr, comparisonStep51Expr, comparisonStep52Expr, comparisonStep53Expr,
      comparisonStep54Expr, comparisonStep55Expr, comparisonStep56Expr, comparisonStep57Expr,
      comparisonStep58Expr, comparisonStep59Expr, comparisonStep60Expr, comparisonStep61Expr,
      comparisonStep62Expr, comparisonStep63Expr, comparisonStep64Expr, comparisonStep65Expr,
      comparisonStep66Expr, comparisonStep67Expr, comparisonStep68Expr, comparisonStep69Expr,
      comparisonStep70Expr, comparisonStep71Expr, comparisonStep72Expr, comparisonStep73Expr,
      comparisonStep74Expr, computedAffineExpr, computedComparisonExpr]
  exact he.trans computedComparison_eq

private theorem radicandModel_eq : radicandModel = computedRadicandValue :=
  computedRadicand_eq

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
set_option cbv.maxSteps 3000000 in
private theorem invNegU_checked :
    zNegU.InverseChecked invNegUModel.polynomial invNegUModel.radius
      1199359340000000000000000000000 := by
  rw [zNegU_eq]
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
set_option cbv.maxSteps 3000000 in
private theorem invNegV_checked :
    zNegV.InverseChecked invNegVModel.polynomial invNegVModel.radius
      1142294860000000000000000000000 := by
  rw [zNegV_eq]
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
set_option cbv.maxSteps 3000000 in
private theorem invPosV_checked :
    zPosV.InverseChecked invPosVModel.polynomial invPosVModel.radius
      1222476740000000000000000000000 := by
  rw [zPosV_eq]
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
set_option cbv.maxSteps 3000000 in
private theorem invPosD_checked :
    zPosD.InverseChecked invPosDModel.polynomial invPosDModel.radius
      1345722040000000000000000000000 := by
  rw [zPosD_eq]
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
set_option cbv.maxSteps 3000000 in
private theorem radicand_checked : (scale : ℤ) * 81 ≤ radicandModel.lower * 100 := by
  rw [radicandModel_eq]
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
set_option cbv.maxSteps 3000000 in
private theorem rootResidual_checked :
    (radicandModel.sqrtResidual rootModel.polynomial).absUpper * 10 ≤ rootModel.radius * 19 := by
  rw [radicandModel_eq]
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
set_option cbv.maxSteps 3000000 in
private theorem comparison_checked : (11 : ℤ) * scale ≤ 2500 * comparisonModel.lower := by
  rw [comparisonModel_eq]
  decide +kernel

private theorem compactChecks : CompactChecks :=
  ⟨invU_checked, invV_checked, invNegU_checked, invNegV_checked, invPosV_checked,
   invPosD_checked, radicand_checked, root_checked, rootResidual_checked, invSinhc_checked,
   invCutoff_checked, comparison_checked⟩

/-- Hägele's refined BMV log kernel has strictly negative mixed derivative on the compact
positive-center square, with each coordinate differentiated independently. -/
theorem logKernel_mixed_neg_compact_square {p : ℕ} (hp : 11 ≤ p)
    {u v : ℝ} (hu : 1 / 2 ≤ u) (hu' : u ≤ 1)
    (hd : 1 / 2 ≤ v - u) (hd' : v - u ≤ 1) :
    deriv (fun y => deriv (fun x => logKernel p x y) u) v < 0 :=
  logKernel_mixed_neg_of_compactChecks compactChecks hp hu hu' hd hd'

/--
info: 'RefinedBMV.PositiveCenter.CompactPolynomialBounds.logKernel_mixed_neg_compact_square'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms logKernel_mixed_neg_compact_square

end RefinedBMV.PositiveCenter.CompactPolynomialBounds
