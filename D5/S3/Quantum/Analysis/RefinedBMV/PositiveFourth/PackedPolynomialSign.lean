/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/PackedPolynomialSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A packed sign check gives nonnegative sparse polynomial evaluation. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineRadixIdentity

/-! The signed radix mask checks all coefficients at once. Mixed-radix
decoding transfers their signs back to the original exponent tuples. -/

open Polynomial

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity

open RefinedBMV.DividedDifference.SparseExpansion
open private packedPolynomial packedPolynomial_coeff_bound eval_packedPolynomial
  eval_unpackedPolynomial from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineRadixIdentity
open private BoundedExpansion BoundedExpansion.eval BoundedExpansion.degree BoundedExpansion.mass
  BoundedExpansion.terms BoundedExpansion.term_bound BoundedExpansion.mass_bound
  Exponents.bounded from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumBinding

private theorem packedPolynomial_coeff_zero (sizes : Exponents) (ts : List Term)
    (i : ℕ) (h : ∀ t ∈ ts, index sizes t.exponents < i) :
    (packedPolynomial sizes ts).coeff i = 0 := by
  induction ts with
  | nil => simp [packedPolynomial]
  | cons t ts ih =>
    change (monomial (index sizes t.exponents) t.coefficient +
      packedPolynomial sizes ts).coeff i = 0
    rw [coeff_add, coeff_monomial, ite_eq_right (ne_of_lt (h t (by simp))),
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha)), add_zero]

private theorem packedPolynomial_degree_lt (sizes : Exponents) (ts : List Term)
    (digits : ℕ) (hd : 0 < digits) (h : ∀ t ∈ ts, index sizes t.exponents < digits) :
    (packedPolynomial sizes ts).natDegree < digits := by
  by_cases hzero : packedPolynomial sizes ts = 0
  · simpa [hzero] using hd
  · by_contra! hlarge
    apply (leadingCoeff_ne_zero.mpr hzero)
    rw [← coeff_natDegree]
    exact packedPolynomial_coeff_zero sizes ts _ (fun t ht => (h t ht).trans_le hlarge)

open DimThree.PackedCheck (packDigits polynomialMask)

private theorem packDigits_replicate_mul (b a n : ℕ) (hb : 0 < b) :
    packDigits b (List.replicate n a) * (b - 1) = a * (b ^ n - 1) := by
  induction n with
  | zero => simp [packDigits]
  | succ n ih =>
    have hle : b ≤ b * b ^ n := Nat.le_mul_of_pos_right _ (pow_pos hb _)
    simp only [List.replicate_succ, packDigits, Nat.add_mul, Nat.mul_assoc, ih]
    calc
      a * (b - 1) + b * (a * (b ^ n - 1)) = a * ((b - 1) + b * (b ^ n - 1)) := by ring
      _ = a * (b ^ (n + 1) - 1) := by
        rw [pow_succ', Nat.mul_sub, Nat.mul_one]
        congr 1
        omega

private def fastMask (width digits : ℕ) : ℕ :=
  let b := 2 ^ (width + 1)
  2 ^ width * (b ^ digits - 1) / (b - 1)

private theorem fastMask_eq (width digits : ℕ) : fastMask width digits = polynomialMask width digits := by
  symm
  apply Nat.eq_div_of_mul_eq_left
  · have hb : 1 < (2 : ℕ) ^ (width + 1) := one_lt_pow₀ (by decide) (by omega)
    exact Nat.sub_ne_zero_of_lt hb
  · exact packDigits_replicate_mul _ _ _ (by positivity)

def passesSignMask (width digits : ℕ) (value : ℤ) : Bool :=
  let mask := fastMask width digits
  ((value + (mask : ℤ)).toNat &&& mask) == mask

theorem evalTerms_nonneg_of_mask (sizes : Exponents) (width digits : ℕ)
    (terms : List Term) (hfit : ∀ t ∈ terms, Fits sizes t.exponents)
    (hdigits : 0 < digits) (hdegree : ∀ t ∈ terms, index sizes t.exponents < digits)
    (hmass : coefficientMass terms < (2 : ℤ) ^ width)
    (hcheck : passesSignMask width digits (packedEval sizes (radix width) terms) = true)
    (p x y u v : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ evalTerms p x y u v terms := by
  let P := packedPolynomial sizes terms
  have hcoeff : ∀ i, 0 ≤ P.coeff i := by
    apply DimThree.PackedCheck.coeff_nonneg_of_polynomial_mask P
      (n := digits) (w := width) (packedPolynomial_degree_lt sizes terms digits hdigits hdegree)
    · intro i
      have h := abs_lt.mp ((packedPolynomial_coeff_bound sizes terms i).trans_lt hmass)
      exact ⟨h.1.le, h.2⟩
    · simpa only [P, passesSignMask, fastMask_eq, beq_iff_eq, eval_packedPolynomial, radix] using hcheck
  rw [← eval_unpackedPolynomial sizes p x y u v terms hfit]
  unfold Polynomial.sum
  apply Finset.sum_nonneg
  intro i _
  have hi : 0 ≤ (P.coeff i : ℝ) := by exact_mod_cast hcoeff i
  dsimp only [Term.eval]
  positivity

theorem boundedExpansion_nonneg_of_mask (sizes : Exponents) (width digits : ℕ)
    (a : BoundedExpansion) (hfit : Fits sizes (BoundedExpansion.degree a))
    (hdigits : 0 < digits) (hdegree : index sizes (BoundedExpansion.degree a) < digits)
    (hmass : BoundedExpansion.mass a < (2 : ℤ) ^ width)
    (hcheck :
      let b := radix width
      passesSignMask width digits (BoundedExpansion.eval b (b ^ sizes.p)
        (b ^ (sizes.p * sizes.x)) (b ^ (sizes.p * sizes.x * sizes.y))
        (b ^ (sizes.p * sizes.x * sizes.y * sizes.u)) a) = true)
    (p x y u v : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ BoundedExpansion.eval p x y u v a := by
  change 0 ≤ evalTerms p x y u v (BoundedExpansion.terms a)
  refine evalTerms_nonneg_of_mask sizes width digits _ ?_ hdigits ?_
    ((BoundedExpansion.mass_bound a).trans_lt hmass) hcheck p x y u v hp hx hy hu hv
  · intro t ht
    have hb := BoundedExpansion.term_bound a t ht
    unfold Exponents.bounded at hb
    unfold Fits at hfit ⊢
    exact ⟨hb.1.trans_lt hfit.1, hb.2.1.trans_lt hfit.2.1,
      hb.2.2.1.trans_lt hfit.2.2.1, hb.2.2.2.1.trans_lt hfit.2.2.2.1,
      hb.2.2.2.2.trans_lt hfit.2.2.2.2⟩
  · intro t ht
    have hb := BoundedExpansion.term_bound a t ht
    unfold Exponents.bounded at hb
    refine lt_of_le_of_lt ?_ hdegree
    unfold index
    gcongr
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2.1
    · exact hb.2.2.2.1
    · exact hb.2.2.2.2

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity
