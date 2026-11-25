/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineMixedOrigins
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed polynomial origins certify the sign of bivariate exponential sums. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.ExponentialChain
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetBounds
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.JetMask

open scoped BigOperators
open Polynomial

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

noncomputable section

abbrev AffineRate := ℕ × ℕ

private def negativeRate (a : AffineRate) (x : ℝ) : ℝ :=
  -((a.1 : ℝ) + (a.2 : ℝ) * x)

private def ratePolynomial (a : AffineRate) : ℤ[X] :=
  -(C (a.1 : ℤ) + C (a.2 : ℤ) * X)

private theorem eval_ratePolynomial (a : AffineRate) (x : ℝ) :
    (ratePolynomial a).eval₂ (Int.castRingHom ℝ) x = negativeRate a x := by
  simp [ratePolynomial, negativeRate, Polynomial.eval₂_add, Polynomial.eval₂_mul]

private def affineFactor (a : AffineRate) (roots : List AffineRate) : ℤ[X] :=
  (roots.map fun b => ratePolynomial a - ratePolynomial b).prod

private theorem eval_affineFactor (a : AffineRate) (roots : List AffineRate) (x : ℝ) :
    (affineFactor a roots).eval₂ (Int.castRingHom ℝ) x =
      ExponentialChain.factors (roots.map fun b => negativeRate b x) (negativeRate a x) := by
  simp [affineFactor, ExponentialChain.factors, Polynomial.eval₂_list_prod,
    Polynomial.eval₂_sub, eval_ratePolynomial, List.map_map, Function.comp_def]

/-- The mixed initial polynomial in the nonnegative degree parameter. -/
def mixedOrigin {ι : Type*} [Fintype ι] (weight : ι → ℤ[X])
    (rateU rateV : ι → AffineRate) (rootsU rootsV : List AffineRate) : ℤ[X] :=
  ∑ i, weight i * affineFactor (rateU i) rootsU * affineFactor (rateV i) rootsV

def rateDifference (a b : AffineRate) : ℤ × ℤ :=
  ((b.1 : ℤ) - a.1, (b.2 : ℤ) - a.2)

private theorem ratePolynomial_sub (a b : AffineRate) :
    ratePolynomial a - ratePolynomial b =
      C (rateDifference a b).1 + C (rateDifference a b).2 * X := by
  simp only [ratePolynomial, rateDifference, map_sub]
  ring

private theorem affineFactor_degree (a : AffineRate) (roots : List AffineRate) :
    (affineFactor a roots).natDegree ≤ roots.length := by
  induction roots with
  | nil => simp [affineFactor]
  | cons b bs ih =>
    have hb : (ratePolynomial a - ratePolynomial b).natDegree ≤ 1 := by
      rw [ratePolynomial_sub]
      apply natDegree_add_le_of_degree_le
      · simp
      · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
    simpa [affineFactor, Nat.add_comm 1] using natDegree_mul_le_of_le hb ih

/-- A bound on each affine factor and the initial coefficients gives a
single degree and coefficient bound for the exact origin checks. -/
theorem mixedOrigin_bounds {ι : Type*} [Fintype ι]
    (weight : ι → ℤ[X]) (rateU rateV : ι → AffineRate)
    (rootsU rootsV : List AffineRate) (size : ι → ℤ) (degree : ℕ) (cap : ℤ)
    (hsize : ∀ i, 0 ≤ size i) (hcap : 0 ≤ cap)
    (hweight : ∀ i j, |(weight i).coeff j| ≤ size i)
    (hdegree : ∀ i, (weight i).natDegree ≤ degree)
    (hU : ∀ i a, a ∈ rootsU → |(rateDifference (rateU i) a).1| +
      |(rateDifference (rateU i) a).2| ≤ cap)
    (hV : ∀ i a, a ∈ rootsV → |(rateDifference (rateV i) a).1| +
      |(rateDifference (rateV i) a).2| ≤ cap) :
    (∀ j, |(mixedOrigin weight rateU rateV rootsU rootsV).coeff j| ≤
      (∑ i, size i) * cap^(rootsU.length + rootsV.length)) ∧
    (mixedOrigin weight rateU rateV rootsU rootsV).natDegree ≤
      degree + rootsU.length + rootsV.length := by
  let P (i : ι) := weight i * affineFactor (rateU i) rootsU * affineFactor (rateV i) rootsV
  simp only [mixedOrigin]
  rw [Finset.sum_mul]
  apply JetBounds.sum_bounds Finset.univ P
  intro i _
  let L := rootsU.map (rateDifference (rateU i)) ++ rootsV.map (rateDifference (rateV i))
  have hL : ∀ pair ∈ L, |pair.1| + |pair.2| ≤ cap := by
    intro pair hpair
    rcases List.mem_append.mp hpair with hleft | hright
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hleft
      exact hU i a ha
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hright
      exact hV i a ha
  constructor
  · intro j
    have h := JetBounds.coeff_abs_affine_chain L (weight i) (size i) cap
      (hsize i) hcap hL (hweight i) j
    simpa [L, P, affineFactor, ratePolynomial_sub, List.map_map, Function.comp_def,
      List.prod_append, mul_comm, mul_left_comm, mul_assoc] using h
  · exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (hdegree i) (affineFactor_degree _ _))
      (affineFactor_degree _ _)

/-- The exact mask test for each initial polynomial provides the sign of
the decaying bivariate exponential sum for every nonnegative parameter. -/
theorem nonneg_of_mixed_origin_masks {ι : Type*} [Fintype ι]
    (weight : ι → ℤ[X]) (rateU rateV : ι → AffineRate)
    (rootsU rootsV : List AffineRate)
    (hU : ∀ i, rateU i ∈ rootsU) (hV : ∀ i, rateV i ∈ rootsV)
    {digits width : ℕ}
    (hcheck : ∀ k < rootsU.length, ∀ l < rootsV.length,
      let P := mixedOrigin weight rateU rateV (rootsU.take k) (rootsV.take l)
      P.natDegree < digits ∧
      (∀ j, -(2 : ℤ)^width ≤ P.coeff j ∧ P.coeff j < (2 : ℤ)^width) ∧
      ((P.eval (2^(width+1)) + ↑(DimThree.PackedCheck.polynomialMask width digits)).toNat &&&
        DimThree.PackedCheck.polynomialMask width digits =
          DimThree.PackedCheck.polynomialMask width digits))
    (x u v : ℝ) (hx : 0 ≤ x) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ ∑ i, (weight i).eval₂ (Int.castRingHom ℝ) x *
        Real.exp (negativeRate (rateU i) x * u + negativeRate (rateV i) x * v) := by
  let ru := rootsU.map fun a => negativeRate a x
  let rv := rootsV.map fun a => negativeRate a x
  refine ExponentialChain.termwise_sum_nonneg_of_mixed_prefix
    (fun i => negativeRate (rateU i) x) (fun i => negativeRate (rateV i) x)
    ru rv
    (fun i => List.mem_map.mpr ⟨rateU i, hU i, rfl⟩)
    (fun i => List.mem_map.mpr ⟨rateV i, hV i, rfl⟩)
    (fun i => (weight i).eval₂ (Int.castRingHom ℝ) x) ?_ u v hu hv
  intro k hk l hl
  obtain ⟨hdegree, hbound, hmask⟩ :=
    hcheck k (by simpa [ru] using hk) l (by simpa [rv] using hl)
  have hs := DimThree.PackedCheck.eval₂_nonneg_of_polynomial_mask _
    hdegree hbound hmask x hx
  simpa only [mixedOrigin, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, eval_affineFactor,
    ru, rv, ← List.map_take] using hs

end

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
