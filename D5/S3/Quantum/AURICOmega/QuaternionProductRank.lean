/- GID: D5/S3/Quantum/AURICOmega/QuaternionProductRank
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/QuaternionProductRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The squared quaternion model meets the rank-five hypotheses without feature rank five. -/

import D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive

/-! The product of two quaternion comparison models.

The product of the quaternion comparison model with itself is noncommutative, chain connected
and has readings arbitrarily close to zero, yet its reading is not the Gram kernel of a map into
Euclidean five-space. A rank-five realization would give an injective map `u` into the unit
quaternions carrying the transfer to `u x * (u y)⁻¹ * u z`. Normalized at the base point
`o = (1, 1)`, the map `v p = (u o)⁻¹ * u p` is multiplicative for the componentwise product.
The two distinct elements `(-1, 1)` and `(1, -1)` square to `o` and differ from `o`, so their
images are unit quaternions of square one different from one. The only such quaternion is `-1`,
so both images are `-1`, contradicting injectivity. -/

open scoped Quaternion

namespace D5.S3.Quantum.AURICOmega.QuaternionProductRank

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.TernaryComparisonProduct
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive

/-- The unit quaternions `-1` and `1` are different. -/
private lemma neg_one_ne_one : (-1 : unitary ℍ[ℝ]) ≠ 1 := fun h => by
  have h' := congrArg (fun z : unitary ℍ[ℝ] => (z : ℍ[ℝ]).re) h
  simp only [Unitary.coe_neg, OneMemClass.coe_one, Quaternion.re_neg, Quaternion.re_one] at h'
  norm_num at h'

/-- The unit quaternion `-1` squares to one under the transfer: `-1 * 1⁻¹ * -1 = 1`. -/
private lemma tri_neg_one : quaternionModel.tri (-1) 1 (-1) = 1 := by
  change (-1 : unitary ℍ[ℝ]) * 1⁻¹ * -1 = 1
  rw [inv_one, mul_one, neg_one_mul, neg_neg]

/-- The unit quaternion `1` squares to one under the transfer: `1 * 1⁻¹ * 1 = 1`. -/
private lemma tri_one : quaternionModel.tri 1 1 1 = 1 := by
  change (1 : unitary ℍ[ℝ]) * 1⁻¹ * 1 = 1
  rw [inv_one, mul_one, mul_one]

/-- A unit quaternion of square one different from one equals `-1`: in the division ring of
quaternions, `q * q = 1` forces `q = 1` or `q = -1`. -/
private lemma coe_eq_neg_one (q : unitary ℍ[ℝ]) (hq : q * q = 1) (hq1 : q ≠ 1) :
    (q : ℍ[ℝ]) = -1 := by
  have h : (q : ℍ[ℝ]) * q = 1 := by
    rw [← Submonoid.coe_mul, hq, OneMemClass.coe_one]
  refine (mul_self_eq_one_iff.mp h).resolve_left fun h1 => hq1 (Subtype.ext ?_)
  rw [h1, OneMemClass.coe_one]

/-- **The product of two quaternion models.** The product of the quaternion comparison model
with itself is noncommutative, chain connected and has readings arbitrarily close to zero, but
its reading is not the Gram kernel of any map into Euclidean five-space. -/
theorem prod_quaternionModel_not_hasFeatureRank_five :
    (prod quaternionModel quaternionModel).Noncommutative ∧
    (prod quaternionModel quaternionModel).ChainConnected ∧
    (prod quaternionModel quaternionModel).TouchesZero ∧
    ¬ (prod quaternionModel quaternionModel).HasFeatureRank 5 := by
  have hnc := prod_noncommutative_left quaternionModel quaternionModel
    quaternionModel_noncommutative
  have hconn := prod_chainConnected quaternionModel quaternionModel
    quaternionModel_chainConnected quaternionModel_chainConnected
  have hzero := prod_touchesZero_left quaternionModel quaternionModel
    quaternionModel_touchesZero
  refine ⟨hnc, hconn, hzero, fun h5 => ?_⟩
  obtain ⟨u, hinj, htri, -⟩ := exists_unitQuaternion_embedding _ hnc hconn hzero h5
  let o : unitary ℍ[ℝ] × unitary ℍ[ℝ] := (1, 1)
  -- an element of square `o` other than `o` is sent by `v p = (u o)⁻¹ * u p` to `-1`
  have hsq : ∀ p, (prod quaternionModel quaternionModel).tri p o p = o → p ≠ o →
      (((u o)⁻¹ * u p : unitary ℍ[ℝ]) : ℍ[ℝ]) = -1 := by
    intro p hp hpo
    have h := htri p o p
    rw [hp] at h
    refine coe_eq_neg_one _ ?_ fun h1 => hpo (hinj (inv_mul_eq_one.mp h1).symm)
    calc (u o)⁻¹ * u p * ((u o)⁻¹ * u p) = (u o)⁻¹ * (u p * (u o)⁻¹ * u p) := by group
      _ = (u o)⁻¹ * u o := by rw [← h]
      _ = 1 := inv_mul_cancel (u o)
  have ha := hsq (-1, 1) (Prod.ext tri_neg_one tri_one)
    fun h => neg_one_ne_one (congrArg Prod.fst h)
  have hb := hsq (1, -1) (Prod.ext tri_one tri_neg_one)
    fun h => neg_one_ne_one (congrArg Prod.snd h)
  have hab : u (-1, 1) = u (1, -1) := mul_left_cancel (Subtype.ext (ha.trans hb.symm))
  exact neg_one_ne_one (congrArg Prod.fst (hinj hab))

end D5.S3.Quantum.AURICOmega.QuaternionProductRank
