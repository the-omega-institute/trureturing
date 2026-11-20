/- GID: D5/S3/Quantum/AURICOmega/ProjectiveQuaternionModel
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/ProjectiveQuaternionModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unit quaternions modulo sign with the squared inner product have feature rank ten. -/

import D5.S3.Quantum.AURICOmega.GramRankFeatureMap
import D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism

/-! Unit quaternions modulo sign as a ternary comparison structure.

The carrier is the quotient of the unit quaternions by the central subgroup `{1, -1}`. The
transfer is `x * y⁻¹ * z` in the quotient group and the reading is `⟪x, y⟫ ^ 2`, which does not
depend on the signs of the representatives. The reading is the Gram kernel of the map
`q ↦ (q_a ^ 2, √2 q_a q_b)` over the ten index pairs `a ≤ b`, so it has feature rank ten. It has
no feature rank nine, so, feature rank being monotone in the dimension, its feature ranks are
exactly the `r ≥ 10`: for the ten points `1, i, j, k` and `(3 e_a + 4 e_b) / 5`, `a < b`, a
vanishing linear combination of the corresponding feature vectors gives a quadratic form vanishing
at the ten points; its values at `e_a` kill the diagonal and its values at `(3 e_a + 4 e_b) / 5`
then kill the off-diagonal entries, so all coefficients are zero, while ten independent vectors do
not fit in nine dimensions. Transfer invariance and chain connectedness come from the
unit-quaternion model, whose reading is `(1 + ⟪x, y⟫) / 2`. Reading completeness follows from
compactness of the unit sphere: a subsequence of representatives converges, and the readings of
the sequence with the class of the limit are limits of readings within the sequence. Every point
`x` has the two distinct points `x i` and `x j` of reading zero, since `1, i, j` are pairwise
orthogonal. -/

open scoped InnerProductSpace Quaternion
open Filter Topology

noncomputable section

namespace D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open D5.S3.Quantum.AURICOmega.GramRankFeatureMap
open D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
open D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup

/-- The central subgroup `{1, -1}` of the unit quaternions. -/
def signSubgroup : Subgroup (unitary ℍ[ℝ]) where
  carrier := {x | x = 1 ∨ x = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro _ _ (rfl | rfl) (rfl | rfl) <;> simp
  inv_mem' := by
    rintro _ (rfl | rfl) <;> simp

/-- Membership in `{1, -1}`. -/
private lemma mem_signSubgroup {x : unitary ℍ[ℝ]} : x ∈ signSubgroup ↔ x = 1 ∨ x = -1 :=
  Iff.rfl

/-- The subgroup `{1, -1}` is normal, since `-1` is central. -/
instance signSubgroup_normal : signSubgroup.Normal :=
  ⟨fun n hn g => by rcases mem_signSubgroup.mp hn with rfl | rfl <;> simp [mem_signSubgroup]⟩

/-- Unit quaternions modulo sign: the quotient group of the unit quaternions by `{1, -1}`. -/
abbrev ProjectiveQuaternion : Type := unitary ℍ[ℝ] ⧸ signSubgroup

/-- Two unit quaternions in the same class modulo `{1, -1}` agree up to sign. -/
private lemma coe_eq_or_eq_neg {x y : unitary ℍ[ℝ]} (h : x⁻¹ * y ∈ signSubgroup) :
    (y : ℍ[ℝ]) = x ∨ (y : ℍ[ℝ]) = -x := by
  rcases mem_signSubgroup.mp h with h | h
  · exact Or.inl (congrArg Subtype.val (inv_mul_eq_one.mp h).symm)
  · rw [inv_mul_eq_iff_eq_mul, mul_neg_one] at h
    exact Or.inr (by rw [h, Unitary.coe_neg])

/-- The squared inner product of unit quaternions does not depend on their signs. -/
private lemma inner_sq_eq {x x' y y' : unitary ℍ[ℝ]} (hx : x⁻¹ * x' ∈ signSubgroup)
    (hy : y⁻¹ * y' ∈ signSubgroup) :
    ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ ^ 2 = ⟪(x' : ℍ[ℝ]), (y' : ℍ[ℝ])⟫_ℝ ^ 2 := by
  rcases coe_eq_or_eq_neg hx with h | h <;> rcases coe_eq_or_eq_neg hy with h' | h' <;>
    simp only [h, h', inner_neg_left, inner_neg_right, neg_sq, neg_neg]

/-- The reading `⟪x, y⟫ ^ 2`, well defined on classes modulo sign. -/
private def reading : ProjectiveQuaternion → ProjectiveQuaternion → ℝ :=
  Quotient.lift₂ (fun x y : unitary ℍ[ℝ] => ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ ^ 2)
    fun _ _ _ _ hx hy => inner_sq_eq (QuotientGroup.leftRel_apply.mp hx)
      (QuotientGroup.leftRel_apply.mp hy)

/-- The reading of two classes is the squared inner product of representatives. -/
private lemma reading_mk (x y : unitary ℍ[ℝ]) :
    reading (QuotientGroup.mk x) (QuotientGroup.mk y) = ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ ^ 2 :=
  rfl

/-- The reading in terms of the chosen representatives. -/
private lemma reading_eq_out (p q : ProjectiveQuaternion) :
    reading p q = ⟪(p.out : ℍ[ℝ]), (q.out : ℍ[ℝ])⟫_ℝ ^ 2 := by
  conv_lhs => rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
  rfl

/-- The feature map `q ↦ (q_a ^ 2, √2 q_a q_b)` over the ten index pairs `a ≤ b`. -/
private def feature (q : ℍ[ℝ]) : EuclideanSpace ℝ (Fin 10) :=
  WithLp.toLp 2 ![q.re ^ 2, q.imI ^ 2, q.imJ ^ 2, q.imK ^ 2,
    Real.sqrt 2 * (q.re * q.imI), Real.sqrt 2 * (q.re * q.imJ), Real.sqrt 2 * (q.re * q.imK),
    Real.sqrt 2 * (q.imI * q.imJ), Real.sqrt 2 * (q.imI * q.imK), Real.sqrt 2 * (q.imJ * q.imK)]

/-- The feature map turns the squared inner product into a Euclidean inner product. -/
private lemma inner_feature (p q : ℍ[ℝ]) : ⟪feature p, feature q⟫_ℝ = ⟪p, q⟫_ℝ ^ 2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [feature, feature, EuclideanSpace.inner_toLp_toLp, inner_eq_components]
  simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, star_trivial]
  linear_combination (p.re * p.imI * q.re * q.imI + p.re * p.imJ * q.re * q.imJ +
    p.re * p.imK * q.re * q.imK + p.imI * p.imJ * q.imI * q.imJ +
    p.imI * p.imK * q.imI * q.imK + p.imJ * p.imK * q.imJ * q.imK) * hs

/-- Right multiplication by `u⁻¹ * v` preserves the inner product of unit quaternions. -/
private lemma inner_tri_right (x y u v : unitary ℍ[ℝ]) :
    ⟪((x * u⁻¹ * v : unitary ℍ[ℝ]) : ℍ[ℝ]), ((y * u⁻¹ * v : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ =
      ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ := by
  have h := quaternionModel.kappa_tri_right x y u v
  change (1 + ⟪((x * u⁻¹ * v : unitary ℍ[ℝ]) : ℍ[ℝ]), ((y * u⁻¹ * v : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ)
    / 2 = (1 + ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ) / 2 at h
  linarith

/-- Left multiplication by `u * v⁻¹` preserves the inner product of unit quaternions. -/
private lemma inner_tri_left (u v x y : unitary ℍ[ℝ]) :
    ⟪((u * v⁻¹ * x : unitary ℍ[ℝ]) : ℍ[ℝ]), ((u * v⁻¹ * y : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ =
      ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ := by
  have h := quaternionModel.kappa_tri_left u v x y
  change (1 + ⟪((u * v⁻¹ * x : unitary ℍ[ℝ]) : ℍ[ℝ]), ((u * v⁻¹ * y : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ)
    / 2 = (1 + ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ) / 2 at h
  linarith

/-- The squared inner product of two unit quaternions is one exactly when they agree up to
sign. -/
private lemma inner_sq_eq_one_iff (x y : unitary ℍ[ℝ]) :
    ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ ^ 2 = 1 ↔ x⁻¹ * y ∈ signSubgroup := by
  have h1 : ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ = 1 ↔ x = y := by
    rw [← quaternionModel.kappa_eq_one_iff]
    change _ ↔ (1 + ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ) / 2 = 1
    constructor <;> intro h <;> linarith
  have h2 : ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ = -1 ↔ x = -y := by
    rw [← quaternionModel.kappa_eq_one_iff]
    change _ ↔ (1 + ⟪(x : ℍ[ℝ]), ((-y : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ) / 2 = 1
    rw [Unitary.coe_neg, inner_neg_right]
    constructor <;> intro h <;> linarith
  rw [sq, mul_self_eq_one_iff, h1, h2, mem_signSubgroup, inv_mul_eq_one, inv_mul_eq_iff_eq_mul,
    mul_neg_one, eq_comm (a := x) (b := -y), neg_eq_iff_eq_neg]

/-- Unit quaternions modulo sign with transfer `x * y⁻¹ * z` and reading `⟪x, y⟫ ^ 2`. -/
def projectiveModel : TernaryComparison ProjectiveQuaternion where
  tri x y z := x * y⁻¹ * z
  kappa := reading
  tri_self_left x z := by rw [mul_inv_cancel, one_mul]
  tri_self_right x z := inv_mul_cancel_right x z
  tri_assoc x y z u v := by simp only [mul_assoc]
  kappa_symm p q := by rw [reading_eq_out, reading_eq_out, real_inner_comm]
  kappa_eq_one_iff p q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [reading_mk, QuotientGroup.eq, inner_sq_eq_one_iff]
  kappa_nonneg p q := by
    rw [reading_eq_out]
    exact sq_nonneg _
  kappa_tri_right p q u v := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    simp only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, reading_mk, inner_tri_right]
  kappa_tri_left u v p q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    simp only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, reading_mk, inner_tri_left]
  kappa_gram_nonneg n x c := by
    have h := real_inner_self_nonneg (x := ∑ i, c i • feature ((x i).out : ℍ[ℝ]))
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      inner_feature] at h
    refine h.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [reading_eq_out, real_inner_comm ((x i).out : ℍ[ℝ])]
    ring

/-- The reading of the classes of `x` and `y` is `⟪x, y⟫ ^ 2`. -/
private lemma kappa_mk (x y : unitary ℍ[ℝ]) :
    projectiveModel.kappa (QuotientGroup.mk x) (QuotientGroup.mk y) =
      ⟪(x : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ ^ 2 :=
  rfl

/-- The unit quaternion `a + b i + c j + d k` for `a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1`. -/
private def unitOf (a b c d : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) : unitary ℍ[ℝ] :=
  ⟨⟨a, b, c, d⟩, mem_unitary_of_normSq (by rw [Quaternion.normSq_def']; exact h)⟩

/-- The transfer is order sensitive modulo sign: with `r = (3 + 4 j) / 5`, the products `i r`
and `r i` have inner product `-7 / 25`, so they are not equal up to sign. -/
private lemma projectiveModel_noncommutative : projectiveModel.Noncommutative := by
  let r := unitOf (3 / 5) 0 (4 / 5) 0 (by norm_num)
  refine ⟨QuotientGroup.mk unitI, QuotientGroup.mk 1, QuotientGroup.mk r, fun h => ?_⟩
  have h1 : projectiveModel.kappa
      (projectiveModel.tri (QuotientGroup.mk unitI) (QuotientGroup.mk 1) (QuotientGroup.mk r))
      (projectiveModel.tri (QuotientGroup.mk r) (QuotientGroup.mk 1) (QuotientGroup.mk unitI)) =
        1 := by
    rw [h]
    exact projectiveModel.kappa_self _
  change reading (QuotientGroup.mk unitI * (QuotientGroup.mk 1)⁻¹ * QuotientGroup.mk r)
    (QuotientGroup.mk r * (QuotientGroup.mk 1)⁻¹ * QuotientGroup.mk unitI) = 1 at h1
  simp only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, reading_mk] at h1
  simp [unitI, r, unitOf, inner_eq_components] at h1
  norm_num at h1

/-- Every class `x` has reading zero with the two distinct classes `x i` and `x j`. -/
private lemma exists_two_zeros (p : ProjectiveQuaternion) :
    ∃ a b : ProjectiveQuaternion, a ≠ b ∧ projectiveModel.kappa p a = 0 ∧
      projectiveModel.kappa p b = 0 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
  have hmul : ∀ u v : unitary ℍ[ℝ],
      ⟪((x * u : unitary ℍ[ℝ]) : ℍ[ℝ]), ((x * v : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ =
        ⟪(u : ℍ[ℝ]), (v : ℍ[ℝ])⟫_ℝ := fun u v => by
    simpa only [inv_one, mul_one] using inner_tri_left x 1 u v
  have h1i : ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]), (unitI : ℍ[ℝ])⟫_ℝ = 0 := by
    simp [unitI, inner_eq_components]
  have h1j : ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]), (unitJ : ℍ[ℝ])⟫_ℝ = 0 := by
    simp [unitJ, inner_eq_components]
  have hij : ⟪(unitI : ℍ[ℝ]), (unitJ : ℍ[ℝ])⟫_ℝ = 0 := by
    simp [unitI, unitJ, inner_eq_components]
  have hx : ∀ u : unitary ℍ[ℝ], projectiveModel.kappa (QuotientGroup.mk x)
      (QuotientGroup.mk (x * u)) = ⟪((1 : unitary ℍ[ℝ]) : ℍ[ℝ]), (u : ℍ[ℝ])⟫_ℝ ^ 2 := by
    intro u
    rw [kappa_mk, ← hmul 1 u, mul_one]
  refine ⟨QuotientGroup.mk (x * unitI), QuotientGroup.mk (x * unitJ), fun h => ?_, ?_, ?_⟩
  · have h' := kappa_mk (x * unitI) (x * unitJ)
    rw [h, projectiveModel.kappa_self, hmul, hij] at h'
    norm_num at h'
  · rw [hx, h1i]
    norm_num
  · rw [hx, h1j]
    norm_num

/-- The reading takes the value zero. -/
private lemma projectiveModel_touchesZero : projectiveModel.TouchesZero := by
  intro ε hε
  obtain ⟨a, -, -, ha, -⟩ := exists_two_zeros 1
  exact ⟨1, a, ha.trans_lt hε⟩

/-- Chains of unit quaternions with readings `(1 + ⟪a, b⟫) / 2 > 1 - ε / 4` give chains of
classes with readings `⟪a, b⟫ ^ 2 > 1 - ε`. -/
private lemma projectiveModel_chainConnected : projectiveModel.ChainConnected := by
  intro ε hε p q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  refine (quaternionModel_chainConnected (ε / 4) (by positivity) x y).lift QuotientGroup.mk
    fun a b hab => ?_
  change 1 - ε / 4 < (1 + ⟪(a : ℍ[ℝ]), (b : ℍ[ℝ])⟫_ℝ) / 2 at hab
  change 1 - ε < projectiveModel.kappa (QuotientGroup.mk a) (QuotientGroup.mk b)
  rw [kappa_mk]
  nlinarith [sq_nonneg (⟪(a : ℍ[ℝ]), (b : ℍ[ℝ])⟫_ℝ - 1)]

/-- The reading is complete: representatives of a reading-Cauchy sequence have a subsequence
converging on the unit sphere, and the class of the limit is a reading limit. -/
private lemma projectiveModel_readingComplete : ReadingComplete projectiveModel := by
  intro x hx
  let y : ℕ → ℍ[ℝ] := fun n => ((x n).out : ℍ[ℝ])
  have hy : ∀ n, y n ∈ Metric.sphere (0 : ℍ[ℝ]) 1 := fun n => by
    rw [← coe_unitary_eq_sphere]
    exact ((x n).out).2
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (isCompact_sphere (0 : ℍ[ℝ]) 1).tendsto_subseq hy
  have ha' : a ∈ unitary ℍ[ℝ] := by
    rw [← SetLike.mem_coe, coe_unitary_eq_sphere]
    exact ha
  refine ⟨QuotientGroup.mk ⟨a, ha'⟩, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hx (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hf : Continuous fun q : ℍ[ℝ] => ⟪y n, q⟫_ℝ ^ 2 := by fun_prop
  have hge : 1 - ε / 2 ≤ ⟪y n, a⟫_ℝ ^ 2 := by
    refine ge_of_tendsto ((hf.tendsto a).comp hlim) (eventually_atTop.mpr ⟨N, fun k hk => ?_⟩)
    have h := hN n (φ k) hn (hk.trans (hφ.id_le k))
    change 1 - ε / 2 < reading (x n) (x (φ k)) at h
    rw [reading_eq_out] at h
    exact h.le
  have hk : projectiveModel.kappa (x n) (QuotientGroup.mk ⟨a, ha'⟩) = ⟪y n, a⟫_ℝ ^ 2 := by
    conv_lhs => rw [← QuotientGroup.out_eq' (x n)]
    rfl
  rw [hk]
  linarith

/-- The reading is the Gram kernel of the feature map applied to representatives. -/
private lemma projectiveModel_hasFeatureRank_ten : projectiveModel.HasFeatureRank 10 :=
  ⟨fun p => feature (p.out : ℍ[ℝ]), fun p q => by
    change reading p q = _
    rw [reading_eq_out, inner_feature]⟩

/-- The ten points `1, i, j, k` and `(3 e_a + 4 e_b) / 5` for `a < b`. -/
private def testPoint : Fin 10 → unitary ℍ[ℝ] :=
  ![unitOf 1 0 0 0 (by norm_num), unitI, unitJ, unitOf 0 0 0 1 (by norm_num),
    unitOf (3 / 5) (4 / 5) 0 0 (by norm_num),
    unitOf (3 / 5) 0 (4 / 5) 0 (by norm_num), unitOf (3 / 5) 0 0 (4 / 5) (by norm_num),
    unitOf 0 (3 / 5) (4 / 5) 0 (by norm_num), unitOf 0 (3 / 5) 0 (4 / 5) (by norm_num),
    unitOf 0 0 (3 / 5) (4 / 5) (by norm_num)]

/-- A linear combination of the squared inner products with the ten points, as an explicit
quadratic form. -/
private lemma sum_inner_testPoint (g : Fin 10 → ℝ) (y : ℍ[ℝ]) :
    ∑ a, g a * ⟪(testPoint a : ℍ[ℝ]), y⟫_ℝ ^ 2 =
      g 0 * y.re ^ 2 + g 1 * y.imI ^ 2 + g 2 * y.imJ ^ 2 + g 3 * y.imK ^ 2 +
      g 4 * ((3 * y.re + 4 * y.imI) / 5) ^ 2 + g 5 * ((3 * y.re + 4 * y.imJ) / 5) ^ 2 +
      g 6 * ((3 * y.re + 4 * y.imK) / 5) ^ 2 + g 7 * ((3 * y.imI + 4 * y.imJ) / 5) ^ 2 +
      g 8 * ((3 * y.imI + 4 * y.imK) / 5) ^ 2 + g 9 * ((3 * y.imJ + 4 * y.imK) / 5) ^ 2 := by
  simp [Fin.sum_univ_succ, testPoint, unitOf, unitI, unitJ, inner_eq_components]
  ring

/-- The feature vectors of the ten points are linearly independent, so they do not fit in
Euclidean nine-space. -/
private lemma projectiveModel_not_hasFeatureRank_nine : ¬ projectiveModel.HasFeatureRank 9 := by
  rintro ⟨φ, hφ⟩
  have hli : LinearIndependent ℝ fun a => φ (QuotientGroup.mk (testPoint a)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e : ∀ b, ∑ a, g a * ⟪(testPoint a : ℍ[ℝ]), (testPoint b : ℍ[ℝ])⟫_ℝ ^ 2 = 0 := by
      intro b
      have h := congrArg (fun w => ⟪w, φ (QuotientGroup.mk (testPoint b))⟫_ℝ) hg
      simp only [sum_inner, real_inner_smul_left, inner_zero_left, ← hφ, kappa_mk] at h
      exact h
    have e0 := e 0
    have e1 := e 1
    have e2 := e 2
    have e3 := e 3
    have e4 := e 4
    have e5 := e 5
    have e6 := e 6
    have e7 := e 7
    have e8 := e 8
    have e9 := e 9
    simp only [sum_inner_testPoint] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
    norm_num [testPoint, unitOf, unitI, unitJ] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
    intro i
    fin_cases i <;> simp <;> linarith
  have h := hli.fintype_card_le_finrank
  simp at h

/-- Feature rank is monotone: a Gram rank bound `r` is a Gram rank bound `s ≥ r`. -/
private lemma hasFeatureRank_mono {M : Type*} {C : TernaryComparison M} {r s : ℕ} (hrs : r ≤ s)
    (h : C.HasFeatureRank r) : C.HasFeatureRank s := by
  rw [← gramRankLE_iff_hasFeatureRank] at h ⊢
  exact fun n x => (h n x).trans hrs

/-- **Unit quaternions modulo sign.** With transfer `x * y⁻¹ * z` and reading `⟪x, y⟫ ^ 2`,
the unit quaternions modulo sign form a noncommutative, chain-connected, reading-complete ternary
comparison structure touching zero, whose reading has feature rank `r` exactly when `10 ≤ r`, and in
which every point has two distinct points of reading zero. -/
theorem projectiveModel_featureRank_ten :
    projectiveModel.Noncommutative ∧ projectiveModel.ChainConnected ∧
      projectiveModel.TouchesZero ∧ ReadingComplete projectiveModel ∧
      (∀ r : ℕ, projectiveModel.HasFeatureRank r ↔ 10 ≤ r) ∧
      ∀ p : ProjectiveQuaternion, ∃ a b : ProjectiveQuaternion, a ≠ b ∧
        projectiveModel.kappa p a = 0 ∧ projectiveModel.kappa p b = 0 :=
  ⟨projectiveModel_noncommutative, projectiveModel_chainConnected, projectiveModel_touchesZero,
    projectiveModel_readingComplete,
    fun _ => ⟨fun h => Nat.lt_of_not_le fun hr => projectiveModel_not_hasFeatureRank_nine
      (hasFeatureRank_mono hr h),
      fun hr => hasFeatureRank_mono hr projectiveModel_hasFeatureRank_ten⟩, exists_two_zeros⟩

end D5.S3.Quantum.AURICOmega.ProjectiveQuaternionModel
