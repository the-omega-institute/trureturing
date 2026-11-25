/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineTableTerms
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recover sparse polynomial exponents from grouped affine rates. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCertificateEvaluation
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.UniformExpansion

/-! The mixed-origin check groups by affine rate pairs. Their constant
parts recover the powers of the fourth-root spectral ratios. -/

open scoped BigOperators
open Polynomial

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

open RefinedBMV.DividedDifference.SparseExpansion

open private rateMonomial
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCertificateEvaluation

private def termExponents (start : ℕ) (u v : AffineRate) (degree : ℕ) : Exponents :=
  ⟨degree, (u.1 - start*u.2)/4, (v.1 - start*v.2)/4, u.2, v.2⟩

private def coefficientTerms (start : ℕ) (u v : AffineRate) (degree : ℕ) :
    List ℤ → List Term
  | [] => []
  | a :: as => ⟨termExponents start u v degree, a⟩ ::
      coefficientTerms start u v (degree+1) as

def Certificate.tableTerms (c : Certificate) (start : ℕ) : List Term :=
  c.terms.flatMap fun (v, group) => coefficientTerms start group.rateU v 0 group.coefficients

private theorem eval_coefficientTerms (start : ℕ) (u v : AffineRate)
    (hu : 4 ∣ u.1 - start*u.2) (hv : 4 ∣ v.1 - start*v.2)
    (x r t U V : ℝ) (degree : ℕ) (cs : List ℤ) :
    evalTerms x (r^4) (t^4) U V (coefficientTerms start u v degree cs) =
      (coefficientPolynomial cs).eval₂ (Int.castRingHom ℝ) x * x^degree *
        rateMonomial start u r U * rateMonomial start v t V := by
  induction cs generalizing degree with
  | nil => simp [coefficientTerms, coefficientPolynomial, evalTerms]
  | cons a as ih =>
    have hu₄ : 4 * ((u.1 - start*u.2)/4) = u.1 - start*u.2 := Nat.mul_div_cancel' hu
    have hv₄ : 4 * ((v.1 - start*v.2)/4) = v.1 - start*v.2 := Nat.mul_div_cancel' hv
    have hr : (r^4)^((u.1 - start*u.2)/4) = r^(u.1 - start*u.2) := by rw [← pow_mul, hu₄]
    have ht : (t^4)^((v.1 - start*v.2)/4) = t^(v.1 - start*v.2) := by rw [← pow_mul, hv₄]
    rw [coefficientTerms]
    change Term.eval x (r^4) (t^4) U V ⟨termExponents start u v degree, a⟩ +
      evalTerms x (r^4) (t^4) U V (coefficientTerms start u v (degree+1) as) = _
    rw [ih]
    simp only [Term.eval, termExponents, hr, ht]
    simp only [coefficientPolynomial, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
      Int.coe_castRingHom, pow_succ, rateMonomial]
    ring

/-- The same integer coefficients have the expected real polynomial meaning
used by the affine mixed-origin sign check. -/
theorem Certificate.eval_tableTerms (c : Certificate) (start : ℕ)
    (hU : ∀ i : c.Index, 4 ∣ (c.rateU i).1 - start*(c.rateU i).2)
    (hV : ∀ i : c.Index, 4 ∣ (c.rateV i).1 - start*(c.rateV i).2)
    (x r t U V : ℝ) :
    evalTerms x (r^4) (t^4) U V (c.tableTerms start) = c.evaluate start x r t U V := by
  have hflatten (xs : List (AffineRate × Group)) (f : AffineRate × Group → List Term)
      (g : Term → ℝ) :
      ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
    induction xs with
    | nil => rfl
    | cons a as ih => simp [List.flatMap_cons, ih]
  rw [evalTerms, Certificate.tableTerms]
  rw [hflatten c.terms, Certificate.evaluate]
  let termValue (a : AffineRate × Group) :=
    ((coefficientTerms start a.2.rateU a.1 0 a.2.coefficients).map
      (Term.eval x (r^4) (t^4) U V)).sum
  change (c.terms.map termValue).sum = _
  rw [← List.ofFn_getElem_eq_map c.terms termValue, ← List.sum_ofFn]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext i
  simpa only [termValue, List.get_eq_getElem, evalTerms, Certificate.weight, Certificate.rateU, Certificate.rateV,
    pow_zero, mul_one] using
    eval_coefficientTerms start (c.rateU i) (c.rateV i) (hU i) (hV i) x r t U V 0
      (c.terms.get i).2.coefficients

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
