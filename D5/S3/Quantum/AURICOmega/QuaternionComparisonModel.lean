/- GID: D5/S3/Quantum/AURICOmega/QuaternionComparisonModel
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/QuaternionComparisonModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The unit quaternions with the half-shifted inner product form a ternary comparison. -/

import D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen

/-! The unit quaternions as a ternary comparison structure.

The carrier is the group of unit quaternions. The transfer is `x * y⁻¹ * z` and the reading is
`(1 + ⟪x, y⟫) / 2` for the real inner product on the quaternions. The reading is the Gram
kernel of a map into Euclidean five-space, it vanishes on the antipodal pair `1, -1`, and any
two unit quaternions are joined by chains of arbitrarily close readings because the unit
three-sphere is connected. -/

open scoped InnerProductSpace Quaternion

noncomputable section

namespace D5.S3.Quantum.AURICOmega.QuaternionComparisonModel

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup

/-- The real inner product of two quaternions is the sum of the products of components. -/
theorem inner_eq_components (p q : ℍ[ℝ]) :
    ⟪p, q⟫_ℝ = p.re * q.re + p.imI * q.imI + p.imJ * q.imJ + p.imK * q.imK := by
  rw [Quaternion.inner_def, Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- Left multiplication by a unit quaternion preserves the real inner product. -/
private lemma inner_unit_mul (a : unitary ℍ[ℝ]) (p q : ℍ[ℝ]) :
    ⟪(a : ℍ[ℝ]) * p, (a : ℍ[ℝ]) * q⟫_ℝ = ⟪p, q⟫_ℝ :=
  LinearIsometry.inner_map_map
    { toLinearMap := LinearMap.mulLeft ℝ (a : ℍ[ℝ])
      norm_map' := fun r => by
        rw [LinearMap.mulLeft_apply, norm_mul, CStarRing.norm_coe_unitary, one_mul] } p q

/-- Right multiplication by a unit quaternion preserves the real inner product. -/
private lemma inner_mul_unit (a : unitary ℍ[ℝ]) (p q : ℍ[ℝ]) :
    ⟪p * (a : ℍ[ℝ]), q * (a : ℍ[ℝ])⟫_ℝ = ⟪p, q⟫_ℝ :=
  LinearIsometry.inner_map_map
    { toLinearMap := LinearMap.mulRight ℝ (a : ℍ[ℝ])
      norm_map' := fun r => by
        rw [LinearMap.mulRight_apply, norm_mul, CStarRing.norm_coe_unitary, mul_one] } p q

/-- The feature map `q ↦ (1 / √2) • (1, re q, imI q, imJ q, imK q)`. -/
def feature (q : ℍ[ℝ]) : EuclideanSpace ℝ (Fin 5) :=
  (1 / Real.sqrt 2) • WithLp.toLp 2 ![1, q.re, q.imI, q.imJ, q.imK]

/-- The feature map turns the reading `(1 + ⟪p, q⟫) / 2` into a Euclidean inner product. -/
lemma inner_feature (p q : ℍ[ℝ]) :
    ⟪feature p, feature q⟫_ℝ = (1 + ⟪p, q⟫_ℝ) / 2 := by
  have h2 : 1 / Real.sqrt 2 * (1 / Real.sqrt 2) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  rw [feature, feature, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, h2,
    EuclideanSpace.inner_toLp_toLp, inner_eq_components]
  simp only [dotProduct, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.cons_val_succ, star_trivial]
  ring

/-- The unit quaternions with transfer `x * y⁻¹ * z` and reading `(1 + ⟪x, y⟫) / 2`. -/
def quaternionModel : TernaryComparison (unitary ℍ[ℝ]) where
  tri x y z := x * y⁻¹ * z
  kappa x y := (1 + ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ) / 2
  tri_self_left x z := by rw [mul_inv_cancel, one_mul]
  tri_self_right x z := inv_mul_cancel_right x z
  tri_assoc x y z u v := by simp only [mul_assoc]
  kappa_symm x y := by rw [real_inner_comm]
  kappa_eq_one_iff x y := by
    rw [Subtype.ext_iff,
      ← inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) (CStarRing.norm_coe_unitary x)
        (CStarRing.norm_coe_unitary y)]
    constructor <;> intro h <;> linarith
  kappa_nonneg x y := by
    have h := neg_one_le_real_inner_of_norm_eq_one (CStarRing.norm_coe_unitary x)
      (CStarRing.norm_coe_unitary y)
    linarith
  kappa_tri_right x y u v := by
    rw [mul_assoc x, mul_assoc y]
    change (1 + ⟪(x : ℍ[ℝ]) * ↑(u⁻¹ * v), (y : ℍ[ℝ]) * ↑(u⁻¹ * v)⟫_ℝ) / 2 = _
    rw [inner_mul_unit]
  kappa_tri_left u v x y := by
    change (1 + ⟪(↑(u * v⁻¹) : ℍ[ℝ]) * x, (↑(u * v⁻¹) : ℍ[ℝ]) * y⟫_ℝ) / 2 = _
    rw [inner_unit_mul]
  kappa_gram_nonneg n x c := by
    have h := real_inner_self_nonneg (x := ∑ i, c i • feature (x i : ℍ[ℝ]))
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      inner_feature] at h
    refine h.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [real_inner_comm (x i : ℍ[ℝ])]
    ring

/-- The unit quaternion `i`. -/
def unitI : unitary ℍ[ℝ] :=
  ⟨⟨0, 1, 0, 0⟩, Unitary.mem_iff.mpr ⟨by ext <;> simp, by ext <;> simp⟩⟩

/-- The unit quaternion `j`. -/
def unitJ : unitary ℍ[ℝ] :=
  ⟨⟨0, 0, 1, 0⟩, Unitary.mem_iff.mpr ⟨by ext <;> simp, by ext <;> simp⟩⟩

/-- The transfer is order sensitive: `i * 1⁻¹ * j = k` while `j * 1⁻¹ * i = -k`. -/
theorem quaternionModel_noncommutative : quaternionModel.Noncommutative := by
  refine ⟨unitI, 1, unitJ, fun h => ?_⟩
  have h' := congrArg (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).imK) h
  change ((unitI : ℍ[ℝ]) * ↑(1⁻¹ : unitary ℍ[ℝ]) * unitJ).imK =
    ((unitJ : ℍ[ℝ]) * ↑(1⁻¹ : unitary ℍ[ℝ]) * unitI).imK at h'
  simp [unitI, unitJ] at h'
  norm_num at h'

/-- The antipodal pair `1, -1` has reading zero. -/
theorem quaternionModel_touchesZero : quaternionModel.TouchesZero := by
  intro ε hε
  refine ⟨1, -1, ?_⟩
  change (1 + ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]), ((-1 : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ) / 2 < ε
  rw [Unitary.coe_neg, OneMemClass.coe_one, inner_neg_right, real_inner_self_eq_norm_sq, norm_one]
  norm_num [hε]

/-- The unit quaternions are exactly the quaternions of norm one. -/
lemma coe_unitary_eq_sphere : (unitary ℍ[ℝ] : Set ℍ[ℝ]) = Metric.sphere 0 1 := by
  ext q
  rw [SetLike.mem_coe, mem_sphere_zero_iff_norm]
  refine ⟨CStarRing.norm_of_mem_unitary, fun hq => ?_⟩
  have h : ((Quaternion.normSq q : ℝ) : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hq, mul_one, Quaternion.coe_one]
  exact Unitary.mem_iff.mpr ⟨(Quaternion.star_mul_self q).trans h,
    (Quaternion.self_mul_star q).trans h⟩

/-- Any two unit quaternions are joined by chains of readings within `ε` of one: the unit
three-sphere is connected and the reading is continuous with value one on the diagonal. -/
theorem quaternionModel_chainConnected : quaternionModel.ChainConnected := by
  intro ε hε x y
  have : PreconnectedSpace (unitary ℍ[ℝ]) := Subtype.preconnectedSpace (by
    rw [coe_unitary_eq_sphere]
    exact isPreconnected_sphere (by rw [Quaternion.rank_eq_four]; norm_num) 0 1)
  refine PreconnectedSpace.induction₂' _ (fun a => ?_)
    ⟨fun _ _ _ => Relation.ReflTransGen.trans⟩ x y
  have hcont : Continuous fun b : unitary ℍ[ℝ] => quaternionModel.kappa a b := by
    change Continuous fun b : unitary ℍ[ℝ] => (1 + ⟪(a : ℍ[ℝ]), (b : ℍ[ℝ])⟫_ℝ) / 2
    fun_prop
  have hlt : 1 - ε < quaternionModel.kappa a a := by
    rw [quaternionModel.kappa_self]
    linarith
  filter_upwards [(hcont.tendsto a).eventually (lt_mem_nhds hlt)] with b hb
  exact ⟨Relation.ReflTransGen.single hb,
    Relation.ReflTransGen.single (by rwa [quaternionModel.kappa_symm])⟩

/-- The reading is the Gram kernel of `q ↦ (1 / √2) • (1, re q, imI q, imJ q, imK q)`. -/
theorem quaternionModel_hasFeatureRank_five : quaternionModel.HasFeatureRank 5 :=
  ⟨fun x => feature x, fun x y => (inner_feature x y).symm⟩

end D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
