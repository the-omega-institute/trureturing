/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineCircuit
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded sparse interpretations of the affine sign expressions. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineRadixIdentity
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineSignPolynomials

/-! The existing bounded expansion carries degree and coefficient-mass
estimates through the factored sign expressions. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity

open RefinedBMV.DividedDifference.SparseExpansion
open private BoundedExpansion BoundedExpansion.mk BoundedExpansion.single BoundedExpansion.eval
  BoundedExpansion.degree BoundedExpansion.mass BoundedExpansion.terms
  BoundedExpansion.term_bound BoundedExpansion.mass_bound Exponents.bounded coeffMass
  eval_bounded_add eval_bounded_sub eval_bounded_mul eval_bounded_pow eval_bounded_nat
  eval_bounded_single
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumBinding

local instance : Neg BoundedExpansion := ⟨fun a => 0 - a⟩

private def inputX : BoundedExpansion := BoundedExpansion.single ⟨1,0,0,0,0⟩ 1
private def inputR : BoundedExpansion := BoundedExpansion.single ⟨0,1,0,0,0⟩ 1
private def inputT : BoundedExpansion := BoundedExpansion.single ⟨0,0,1,0,0⟩ 1
private def inputU : BoundedExpansion := BoundedExpansion.single ⟨0,0,0,1,0⟩ 1
private def inputV : BoundedExpansion := BoundedExpansion.single ⟨0,0,0,0,1⟩ 1

def signExpansion (sign : GramSign) : BoundedExpansion :=
  sign.value (affineEntries inputX inputR inputT inputU inputV)

def factorExpansion (sign : GramSign) : BoundedExpansion :=
  sign.removedFactor inputX inputR inputT inputU inputV

private theorem eval_neg {R : Type*} [CommRing R] (x r t u v : R) (a : BoundedExpansion) :
    BoundedExpansion.eval x r t u v (-a) = -BoundedExpansion.eval x r t u v a := by
  change BoundedExpansion.eval x r t u v ((0 : BoundedExpansion) - a) = _
  rw [eval_bounded_sub, eval_bounded_nat]
  simp

private theorem eval_affineEntry {R : Type*} [CommRing R] (x r t u v : R) (i : Fin 12) :
    BoundedExpansion.eval x r t u v (affineEntries inputX inputR inputT inputU inputV i) =
      affineEntries x r t u v i := by
  fin_cases i <;>
    simp [affineEntries, clearedSpectralEntries, commonThreeOne, commonTwoTwo,
      commonTwoOneOne, threeOnePolynomial, twoTwoPolynomial, twoOneOnePolynomial,
      eval_bounded_add, eval_bounded_sub, eval_bounded_mul, eval_bounded_pow,
      eval_bounded_nat x r t u v 1, eval_bounded_nat x r t u v 2,
      eval_bounded_nat x r t u v 3, eval_bounded_nat x r t u v 6,
      eval_bounded_nat x r t u v 12, eval_bounded_nat x r t u v 11,
      eval_bounded_single, eval_neg, inputX, inputR, inputT, inputU, inputV]

theorem eval_signExpansion {R : Type*} [CommRing R] (sign : GramSign) (x r t u v : R) :
    BoundedExpansion.eval x r t u v (signExpansion sign) =
      sign.value (affineEntries x r t u v) := by
  cases sign <;>
    simp [signExpansion, GramSign.value, QuarticData.ofGapEntries,
      QuarticData.axis1, QuarticData.axis2, QuarticData.axis3,
      QuarticData.mixed1, QuarticData.mixed2, QuarticData.mixed3,
      QuarticData.alpha, QuarticData.beta, QuarticData.gamma,
      QuarticData.RX, QuarticData.RY, QuarticData.RZ, QuarticData.J,
      QuarticData.KX, QuarticData.KY, QuarticData.KZ,
      QuarticData.delta1, QuarticData.delta2, QuarticData.delta3, eval_affineEntry,
      eval_bounded_add, eval_bounded_sub, eval_bounded_mul, eval_bounded_pow,
      eval_bounded_nat x r t u v 2, eval_bounded_nat x r t u v 4]

theorem eval_factorExpansion {R : Type*} [CommRing R] (sign : GramSign) (x r t u v : R) :
    BoundedExpansion.eval x r t u v (factorExpansion sign) = sign.removedFactor x r t u v := by
  cases sign <;>
    simp only [factorExpansion, GramSign.removedFactor, eval_affineEntry,
      eval_bounded_add, eval_bounded_sub, eval_bounded_mul, eval_bounded_pow,
      eval_bounded_nat x r t u v 1, eval_bounded_nat x r t u v 16,
      eval_bounded_nat x r t u v 12, eval_bounded_nat x r t u v 14] <;>
    simp [eval_bounded_single, inputX, inputR, inputT, inputU, inputV]

def tableExpansion (terms : List Term) (degree : Exponents)
    (hb : ∀ t ∈ terms, Exponents.bounded t.exponents degree) : BoundedExpansion :=
  BoundedExpansion.mk terms degree (coefficientMass terms) hb le_rfl
    (by simp [coefficientMass, coeffMass, List.sum_nonneg])

/-- The packed integer identity transfers the positive-factor decomposition
to every ring without expanding the circuit during the integer check. -/
theorem factor_mul_evalTerms_eq_signValue {R : Type*} [CommRing R]
    (sign : GramSign) (terms : List Term) (degree sizes : Exponents) (width : ℕ)
    (hb : ∀ t ∈ terms, Exponents.bounded t.exponents degree)
    (hfactored : Fits sizes (BoundedExpansion.degree
      (factorExpansion sign * tableExpansion terms degree hb)))
    (hsign : Fits sizes (BoundedExpansion.degree (signExpansion sign)))
    (hmass : BoundedExpansion.mass (factorExpansion sign * tableExpansion terms degree hb) +
      BoundedExpansion.mass (signExpansion sign) < (2 : ℤ)^width)
    (hcheck :
      let b := radix width
      let r := b^sizes.p
      let t := b^(sizes.p*sizes.x)
      let u := b^(sizes.p*sizes.x*sizes.y)
      let v := b^(sizes.p*sizes.x*sizes.y*sizes.u)
      sign.removedFactor b r t u v * packedEval sizes b terms =
        sign.value (affineEntries b r t u v))
    (x r t u v : R) :
    sign.removedFactor x r t u v * evalTerms x r t u v terms =
      sign.value (affineEntries x r t u v) := by
  let factored := factorExpansion sign * tableExpansion terms degree hb
  have hfit (a : Term) (ha : a ∈ BoundedExpansion.terms factored) : Fits sizes a.exponents := by
    have h := BoundedExpansion.term_bound factored a ha
    unfold Exponents.bounded at h
    change Fits sizes (BoundedExpansion.degree factored) at hfactored
    unfold Fits at hfactored ⊢
    exact ⟨h.1.trans_lt hfactored.1, h.2.1.trans_lt hfactored.2.1,
      h.2.2.1.trans_lt hfactored.2.2.1, h.2.2.2.1.trans_lt hfactored.2.2.2.1,
      h.2.2.2.2.trans_lt hfactored.2.2.2.2⟩
  have hchecked : packedEval sizes (radix width) (BoundedExpansion.terms factored) =
      packedEval sizes (radix width) (BoundedExpansion.terms (signExpansion sign)) := by
    change BoundedExpansion.eval _ _ _ _ _ factored =
      BoundedExpansion.eval _ _ _ _ _ (signExpansion sign)
    unfold factored
    rw [eval_bounded_mul, eval_factorExpansion, eval_signExpansion]
    exact hcheck
  have hm := (add_le_add (BoundedExpansion.mass_bound factored)
    (le_rfl : BoundedExpansion.mass (signExpansion sign) ≤ _)).trans_lt hmass
  have h := evalTerms_eq_boundedExpansion_of_packedEval_eq sizes width
    (BoundedExpansion.terms factored) (signExpansion sign) x r t u v hfit hsign hm hchecked
  change BoundedExpansion.eval x r t u v factored =
    BoundedExpansion.eval x r t u v (signExpansion sign) at h
  unfold factored at h
  rw [eval_bounded_mul, eval_factorExpansion, eval_signExpansion] at h
  exact h

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity
