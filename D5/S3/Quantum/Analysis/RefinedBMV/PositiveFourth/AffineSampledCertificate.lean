/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineSampledCertificate
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Certify the reduced mixed-sign identity using bounded integer evaluations. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCheckedIdentity
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineMixedFactor
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineSliceIdentity

/-! First remove the two shared gap factors. Each remaining check packs four
coordinates, substituting a small integer for the last variable. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity

open RefinedBMV.DividedDifference.SparseExpansion
open GroupedAffineMasks (Certificate)
open private BoundedExpansion BoundedExpansion.degree BoundedExpansion.mass BoundedExpansion.terms
  BoundedExpansion.eval BoundedExpansion.mass_bound BoundedExpansion.term_bound Exponents.bounded
  Exponents.plus eval_bounded_add eval_bounded_sub eval_bounded_mul eval_bounded_pow
  eval_bounded_nat eval_bounded_single from
  D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumBinding
open private inputX inputR inputT inputU inputV eval_affineEntry from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCircuit
open private paddedSizes fits_padded_left fits_padded_right boundedTable tableTerms_bounded
  tableMass tableMass_eq from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCheckedIdentity

local instance : Neg BoundedExpansion := ⟨fun a => 0 - a⟩

private def reducedFactor (sign : GramSign) : BoundedExpansion :=
  sign.removedFactorWithoutSharedGaps inputX inputR inputT inputU inputV

private def reducedSign (sign : GramSign) : BoundedExpansion :=
  sign.valueWithoutSharedGaps (affineEntries inputX inputR inputT inputU inputV)

private theorem eval_reducedFactor {R : Type*} [CommRing R] (s : GramSign) (x r t u v : R) :
    (reducedFactor s).eval x r t u v = s.removedFactorWithoutSharedGaps x r t u v := by
  cases s <;>
    simp only [reducedFactor, GramSign.removedFactorWithoutSharedGaps, GramSign.removedFactor,
      eval_bounded_add, eval_bounded_sub, eval_bounded_mul, eval_bounded_pow,
      eval_bounded_nat x r t u v 1, eval_bounded_nat x r t u v 12,
      eval_bounded_nat x r t u v 14, eval_bounded_nat x r t u v 16] <;>
    simp [inputX, inputR, inputT, inputU, inputV, eval_bounded_single]

private theorem eval_reducedSign {R : Type*} [CommRing R] (s : GramSign) (x r t u v : R) :
    (reducedSign s).eval x r t u v = s.valueWithoutSharedGaps (affineEntries x r t u v) := by
  cases s <;>
    simp [reducedSign, GramSign.valueWithoutSharedGaps, GramSign.value, QuarticData.ofGapEntries,
      QuarticData.axis1, QuarticData.axis2, QuarticData.axis3, QuarticData.alpha,
      QuarticData.beta, QuarticData.gamma, eval_affineEntry, eval_bounded_add,
      eval_bounded_sub, eval_bounded_mul, eval_bounded_pow,
      eval_bounded_nat x r t u v 2, eval_bounded_nat x r t u v 4]

def sampleSizes (s : GramSign) (degree : Exponents) : Exponents :=
  paddedSizes (Exponents.plus (reducedFactor s).degree degree) (reducedSign s).degree

private def sampleMass (s : GramSign) (sizes : Exponents) (mass : ℤ) : ℤ :=
  ((sizes.v - 1 : ℕ) : ℤ) ^ (sizes.v - 1) *
    ((reducedFactor s).mass * mass + (reducedSign s).mass)

def sampleWidth (s : GramSign) (sizes : Exponents) (c : Certificate) : ℕ :=
  (sampleMass s sizes (tableMass c)).toNat.log2 + 1

/-- Compare the grouped quotient and the reduced sign at a fixed last coordinate. -/
def checkSample (s : GramSign) (c : Certificate) (start : ℕ)
    (sizes : Exponents) (width j : ℕ) : Bool :=
  let bits := width + 1
  let x := (1 : ℤ) <<< bits
  let r := (1 : ℤ) <<< (bits * sizes.p)
  let t := (1 : ℤ) <<< (bits * (sizes.p * sizes.x))
  let u := (1 : ℤ) <<< (bits * (sizes.p * sizes.x * sizes.y))
  let rows : Exponents := ⟨sizes.p, sizes.x, sizes.y, sizes.u, 1⟩
  decide (s.removedFactorWithoutSharedGaps x r t u (j : ℤ) *
      (c.sampleTable start j).groupedPackedEval start rows bits =
    s.valueWithoutSharedGaps (affineEntries x r t u (j : ℤ)))

private theorem terms_fit (a : BoundedExpansion) (sizes : Exponents) (hs : Fits sizes a.degree) :
    ∀ t ∈ a.terms, Fits sizes t.exponents := by
  intro t ht
  have h := a.term_bound t ht
  exact ⟨h.1.trans_lt hs.1, h.2.1.trans_lt hs.2.1, h.2.2.1.trans_lt hs.2.2.1,
    h.2.2.2.1.trans_lt hs.2.2.2.1, h.2.2.2.2.trans_lt hs.2.2.2.2⟩

/-- The bounds and exact sample equalities give the original five-variable sign identity. -/
theorem factor_mul_table_of_checkedSamples
    (s : GramSign) (c : Certificate) (start : ℕ) (degree : Exponents)
    (hbound : boundedTable c start degree = true)
    (hv : 1 < (sampleSizes s degree).v)
    (hcheck : ∀ j < (sampleSizes s degree).v,
      checkSample s c start (sampleSizes s degree) (sampleWidth s (sampleSizes s degree) c) j =
        true) (x r t u v : ℝ) :
    s.removedFactor x r t u v * evalTerms x r t u v (c.tableTerms start) =
      s.value (affineEntries x r t u v) := by
  let sizes := sampleSizes s degree
  let width := sampleWidth s sizes c
  let A := reducedFactor s * tableExpansion (c.tableTerms start) degree
    (tableTerms_bounded c start degree hbound)
  let B := reducedSign s
  have hA : Fits sizes A.degree := fits_padded_left _ _
  have hB : Fits sizes B.degree := fits_padded_right _ _
  apply s.factor_mul_quotient_eq_of_reduced_identity
  have h : evalTerms x r t u v A.terms = evalTerms x r t u v B.terms := by
    apply evalTerms_eq_of_packedSamples sizes width A.terms B.terms x r t u v
      (by omega) (terms_fit A sizes hA) (terms_fit B sizes hB)
    · intro j hj
      have hj' : j ≤ sizes.v - 1 := by omega
      have hlim : 1 ≤ sizes.v - 1 := by omega
      have ha := specializeLast_mass_le j (sizes.v - 1) (sizes.v - 1) A.terms hj' hlim
        (fun z hz => Nat.le_sub_one_of_lt ((terms_fit A sizes hA z hz).2.2.2.2))
      have hb := specializeLast_mass_le j (sizes.v - 1) (sizes.v - 1) B.terms hj' hlim
        (fun z hz => Nat.le_sub_one_of_lt ((terms_fit B sizes hB z hz).2.2.2.2))
      refine (add_le_add ha hb).trans_lt ?_
      rw [← mul_add]
      have hm := add_le_add A.mass_bound B.mass_bound
      have hs : sampleMass s sizes (tableMass c) < (2 : ℤ) ^ width := by
        have hn : (sampleMass s sizes (tableMass c)).toNat < 2 ^ width := Nat.lt_log2_self
        exact (Int.self_le_toNat _).trans_lt (by exact_mod_cast hn)
      refine (mul_le_mul_of_nonneg_left hm (by positivity)).trans_lt ?_
      simpa only [A, B, sampleMass, tableMass_eq c start] using hs
    · intro j hj
      have hc := hcheck j hj
      simp only [packedEval, evalTerms_specializeLast]
      change A.eval _ _ _ _ (j : ℤ) = B.eval _ _ _ _ (j : ℤ)
      unfold A B
      rw [eval_bounded_mul, eval_reducedFactor, eval_reducedSign]
      simp only [checkSample, decide_eq_true_eq, Int.shiftLeft_eq, one_mul, pow_mul,
        Certificate.groupedPackedEval_eq, Certificate.sampleTable_terms, packedEval,
        evalTerms_specializeLast] at hc
      simpa only [width, sizes, radix, pow_mul] using hc
  change A.eval x r t u v = B.eval x r t u v at h
  unfold A B at h
  rw [eval_bounded_mul, eval_reducedFactor, eval_reducedSign] at h
  exact h

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity
