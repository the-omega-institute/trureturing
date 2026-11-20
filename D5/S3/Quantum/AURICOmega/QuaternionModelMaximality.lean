/- GID: D5/S3/Quantum/AURICOmega/QuaternionModelMaximality
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/QuaternionModelMaximality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A transfer- and reading-preserving quaternion copy in feature rank ≤ 8 is everything. -/

import D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
import D5.S3.Quantum.AURICOmega.GramRankFeatureMap

/-! Maximality of the unit-quaternion comparison model in small feature rank.

A transfer- and reading-preserving copy of the unit-quaternion model inside a ternary comparison
structure of feature rank at most eight is everything; eight is optimal; and in feature rank five
a reading-preserving copy is everything.

Let `C` be a ternary comparison structure whose reading is the Gram kernel of a map `φ` into
Euclidean `r`-space, and let `j` be a map from the unit quaternions to `C` preserving the reading.
A preserved reading makes `j` injective. For a point `m`, the readings `κ (j y) m` form a one-point
extension of the quaternion reading with self-reading one, so they are `(a + ⟪b, y⟫) / √2` with
`a ^ 2 + ‖b‖ ^ 2 ≤ 1`.

If `j` also preserves the transfer, the right translate `x ↦ tri m (j 1) (j x)` of the copy has
readings `κ (j y) (tri m (j 1) (j x)) = (a + ⟪b * x, y⟫) / √2` against the copy. For the four unit
quaternions `e = 1, i, j, k`, the differences `D e` of the feature vectors of the translate at `e`
and `-e` read `⟪2 • (b * e), y⟫ / √2` against `φ (j y)` and satisfy `⟪D e, D e'⟫ = 2 * ⟪e, e'⟫`.
Their components orthogonal to all `φ (j y)` have inner products `(2 - 4 * ‖b‖ ^ 2) * ⟪e, e'⟫`.
Together with the five orthogonal vectors `φ (j 1) + φ (j (-1))` and `φ (j e) - φ (j (-e))`, they
would be nine nonzero orthogonal vectors if `‖b‖ ^ 2 < 1 / 2`, which is impossible for `r ≤ 8`.
So `‖b‖ ^ 2 = 1 / 2`; nonnegativity of the readings then gives `a = ‖b‖ = 1 / √2`, and `m` has
reading one with `j (√2 • b)`, so `m` lies in the image of `j`.

The bound eight is optimal: two copies of the unit quaternions, with transfer adding the layers
modulo two and reading one half between layers, form a structure of feature rank nine in which the
first layer is a proper transfer- and reading-preserving copy.

In feature rank five, the transfer need not be preserved. Every translate point
`tri m (j 1) (j x)` reads `(a + ⟪b, y⟫) / √2` against `j y` with `a ^ 2 + ‖b‖ ^ 2 = 1`, and
nonnegativity gives `‖b‖ ≤ a`, so its readings against `j 1` and `j (-1)` sum to `√2 * a ≥ 1`.
These sums, as functions of `x`, form a one-point extension of feature rank five of the translated
copy, by the unit vector `(φ (j 1) + φ (j (-1))) / √2`; hence the sums at `x` and `-x` add up to at
most two, and the sum at `x = 1`, which is that of `m`, equals one. For the readings of `m` this
means `2 * a = √2` and `‖b‖ ^ 2 = 1 / 2`, so `m` has reading one with `j (√2 • b)`. -/

open scoped InnerProductSpace Quaternion

noncomputable section

namespace D5.S3.Quantum.AURICOmega.QuaternionModelMaximality

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
open D5.S3.Quantum.AURICOmega.GramRankFeatureMap

section Quaternion

/-- The four unit quaternions `1, i, j, k`. -/
private def basis4 : Fin 4 → unitary ℍ[ℝ] := ![1, unitI, unitJ, unitI * unitJ]

/-- The unit quaternions `1, i, j, k` are orthonormal. -/
private lemma inner_basis4 (k l : Fin 4) :
    ⟪(basis4 k : ℍ[ℝ]), (basis4 l : ℍ[ℝ])⟫_ℝ = if k = l then 1 else 0 := by
  fin_cases k <;> fin_cases l <;> simp only [inner_eq_components] <;> simp [basis4, unitI, unitJ]

/-- Parseval's identity in the basis `1, i, j, k`. -/
private lemma sum_inner_basis4 (p q : ℍ[ℝ]) :
    ∑ k, ⟪p, (basis4 k : ℍ[ℝ])⟫_ℝ * ⟪q, (basis4 k : ℍ[ℝ])⟫_ℝ = ⟪p, q⟫_ℝ := by
  simp [Fin.sum_univ_four, basis4, unitI, unitJ, inner_eq_components]

/-- Right multiplication by `e` is adjoint to right multiplication by `star e`. -/
private lemma inner_mul_right_eq (b e y : ℍ[ℝ]) : ⟪b * e, y⟫_ℝ = ⟪b, y * star e⟫_ℝ := by
  rw [Quaternion.inner_def, Quaternion.inner_def, star_mul, star_star, mul_assoc]

/-- Left multiplication by `b` scales the inner product by `‖b‖ ^ 2`. -/
private lemma inner_mul_left_mul_left (b x y : ℍ[ℝ]) :
    ⟪b * x, b * y⟫_ℝ = ‖b‖ ^ 2 * ⟪x, y⟫_ℝ := by
  rw [inner_eq_components, inner_eq_components, sq, ← Quaternion.normSq_eq_norm_mul_self,
    Quaternion.normSq_def']
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

/-- The readings of `y` against an antipodal pair add up to one. -/
private lemma kappa_add_kappa_neg (y q : unitary ℍ[ℝ]) :
    quaternionModel.kappa y q + quaternionModel.kappa y (-q) = 1 := by
  change (1 + ⟪(y : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ) / 2 +
    (1 + ⟪(y : ℍ[ℝ]), ((-q : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ) / 2 = 1
  rw [Unitary.coe_neg, inner_neg_right]
  ring

/-- The readings of `y` against an antipodal pair differ by `⟪y, q⟫`. -/
private lemma kappa_sub_kappa_neg (y q : unitary ℍ[ℝ]) :
    quaternionModel.kappa y q - quaternionModel.kappa y (-q) = ⟪(y : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ := by
  change (1 + ⟪(y : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ) / 2 -
    (1 + ⟪(y : ℍ[ℝ]), ((-q : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ) / 2 = _
  rw [Unitary.coe_neg, inner_neg_right]
  ring

/-- The unit quaternion `y * x⁻¹ * 1` is `y * star x`. -/
private lemma coe_tri_one (y x : unitary ℍ[ℝ]) :
    ((quaternionModel.tri y x 1 : unitary ℍ[ℝ]) : ℍ[ℝ]) = (y : ℍ[ℝ]) * star (x : ℍ[ℝ]) := by
  change ((y * x⁻¹ * 1 : unitary ℍ[ℝ]) : ℍ[ℝ]) = _
  rw [mul_one, ← Unitary.star_eq_inv, Submonoid.coe_mul, Unitary.coe_star]

end Quaternion

section Residual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let `P` realize the unit-quaternion reading and let `z` read `(α + ⟪β, y⟫) / √2` against every
`P y`. Removing from `z` the combination `(α / √2) • (P 1 + P (-1))` plus
`(⟪β, e⟫ / √2) • (P e - P (-e))` over `e = 1, i, j, k` leaves a vector orthogonal to every `P y`,
whose inner product with any `z'` reading `(α' + ⟪β', y⟫) / √2` against every `P y` is
`⟪z, z'⟫ - α * α' - ⟪β, β'⟫`. -/
private lemma exists_residual (P : unitary ℍ[ℝ] → E)
    (hP : ∀ x y, ⟪P x, P y⟫_ℝ = quaternionModel.kappa x y) (z : E) (α : ℝ) (β : ℍ[ℝ])
    (hz : ∀ y, ⟪P y, z⟫_ℝ = (α + ⟪β, (y : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) :
    ∃ ρ : E, (∀ y, ⟪P y, ρ⟫_ℝ = 0) ∧
      ∀ (z' : E) (α' : ℝ) (β' : ℍ[ℝ]),
        (∀ y, ⟪P y, z'⟫_ℝ = (α' + ⟪β', (y : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) →
          ⟪ρ, z'⟫_ℝ = ⟪z, z'⟫_ℝ - α * α' - ⟪β, β'⟫_ℝ := by
  have hσσ : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨z - (α / Real.sqrt 2) • (P 1 + P (-1)) -
      ∑ k, (⟪β, (basis4 k : ℍ[ℝ])⟫_ℝ / Real.sqrt 2) • (P (basis4 k) - P (-basis4 k)), ?_, ?_⟩
  · intro y
    have hs : ∑ k, ⟪β, (basis4 k : ℍ[ℝ])⟫_ℝ / Real.sqrt 2 *
        ⟪(y : ℍ[ℝ]), (basis4 k : ℍ[ℝ])⟫_ℝ = ⟪β, (y : ℍ[ℝ])⟫_ℝ / Real.sqrt 2 := by
      rw [← sum_inner_basis4 β (y : ℍ[ℝ]), Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right, inner_sum, hP, hz,
      kappa_add_kappa_neg, kappa_sub_kappa_neg]
    rw [hs]
    ring
  · intro z' α' β' hz'
    have k1 : ∀ u v : ℝ,
        u / Real.sqrt 2 * ((α' + v) / Real.sqrt 2 + (α' + -v) / Real.sqrt 2) = u * α' := by
      intro u v
      calc _ = u * (2 * α') / (Real.sqrt 2 * Real.sqrt 2) := by ring
        _ = u * α' := by rw [hσσ]; ring
    have k2 : ∀ u v : ℝ,
        u / Real.sqrt 2 * ((α' + v) / Real.sqrt 2 - (α' + -v) / Real.sqrt 2) = u * v := by
      intro u v
      calc _ = u * (2 * v) / (Real.sqrt 2 * Real.sqrt 2) := by ring
        _ = u * v := by rw [hσσ]; ring
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, sum_inner, hz',
      Unitary.coe_neg, inner_neg_right, k1, k2]
    rw [sum_inner_basis4]

end Residual

/-- A reading-preserving map from the unit quaternions is injective. -/
private lemma injective_of_kappa {M : Type*} (C : TernaryComparison M) (j : unitary ℍ[ℝ] → M)
    (hjk : ∀ x y, C.kappa (j x) (j y) = quaternionModel.kappa x y) : Function.Injective j :=
  fun x y h => (quaternionModel.kappa_eq_one_iff x y).mp (by rw [← hjk, h, C.kappa_self])

/-- The readings of a point `m` against a reading-preserving copy of the model have nonnegative
extended Gram forms with self-reading one. -/
private lemma form_nonneg_of_copy {M : Type*} (C : TernaryComparison M) (j : unitary ℍ[ℝ] → M)
    (hjk : ∀ x y, C.kappa (j x) (j y) = quaternionModel.kappa x y) (m : M) (n : ℕ)
    (x : Fin n → unitary ℍ[ℝ]) (c : Fin n → ℝ) (t : ℝ) :
    0 ≤ 1 * t ^ 2 + 2 * t * ∑ i, c i * C.kappa (j (x i)) m +
      ∑ i, ∑ k, c i * c k * quaternionModel.kappa (x i) (x k) := by
  have h := C.kappa_gram_nonneg (n + 1) (Fin.cons m fun i => j (x i)) (Fin.cons t c)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, C.kappa_self, hjk] at h
  rw [Finset.sum_add_distrib] at h
  have e1 : ∑ k, t * c k * C.kappa m (j (x k)) = t * ∑ i, c i * C.kappa (j (x i)) m := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [C.kappa_symm]; ring
  have e2 : ∑ i, c i * t * C.kappa (j (x i)) m = t * ∑ i, c i * C.kappa (j (x i)) m := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e2] at h
  linarith

/-- Reading against the right translate `tri m (j 1) (j x)` of a transfer-preserving copy is
reading the copy at `y * x⁻¹` against `m`. -/
private lemma kappa_translate {M : Type*} (C : TernaryComparison M) (j : unitary ℍ[ℝ] → M)
    (hjt : ∀ x y z, j (quaternionModel.tri x y z) = C.tri (j x) (j y) (j z)) (m : M)
    (x y : unitary ℍ[ℝ]) :
    C.kappa (j y) (C.tri m (j 1) (j x)) = C.kappa (j (quaternionModel.tri y x 1)) m := by
  rw [← C.kappa_tri_right (j y) (C.tri m (j 1) (j x)) (j x) (j 1), C.tri_assoc, C.tri_self_left,
    C.tri_self_right, hjt]

/-- A copy of the unit-quaternion model inside a ternary comparison structure of feature rank at
most eight, preserving transfer and reading, is the whole structure. -/
theorem bijective_of_hasFeatureRank_le_eight {M : Type*} (C : TernaryComparison M) {r : ℕ}
    (hr : C.HasFeatureRank r) (hr8 : r ≤ 8) (j : unitary ℍ[ℝ] → M)
    (hjt : ∀ x y z, j (quaternionModel.tri x y z) = C.tri (j x) (j y) (j z))
    (hjk : ∀ x y, C.kappa (j x) (j y) = quaternionModel.kappa x y) :
    Function.Bijective j := by
  refine ⟨injective_of_kappa C j hjk, fun m => ?_⟩
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  obtain ⟨φ, hφ⟩ := hr
  -- the readings of `m` against the copy
  obtain ⟨a, b, hab, hf⟩ := ((tfae_onePointExtension (fun z => C.kappa (j z) m) 1).out 1 3).mp
    (form_nonneg_of_copy C j hjk m)
  have hf' : ∀ y, C.kappa (j y) m = (a + ⟪b, (y : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 := hf
  obtain ⟨P, hPdef⟩ : ∃ P : unitary ℍ[ℝ] → EuclideanSpace ℝ (Fin r), ∀ y, P y = φ (j y) :=
    ⟨_, fun _ => rfl⟩
  have hP : ∀ x y, ⟪P x, P y⟫_ℝ = quaternionModel.kappa x y := fun x y => by
    rw [hPdef, hPdef, ← hφ, hjk]
  -- the right translate of the copy through `m`
  obtain ⟨w, hw⟩ : ∃ w : unitary ℍ[ℝ] → EuclideanSpace ℝ (Fin r),
      ∀ x, w x = φ (C.tri m (j 1) (j x)) := ⟨_, fun _ => rfl⟩
  have hPw : ∀ y x, ⟪P y, w x⟫_ℝ = (a + ⟪b, (y : ℍ[ℝ]) * star (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 := by
    intro y x
    rw [hPdef, hw, ← hφ, kappa_translate C j hjt, hf', coe_tri_one]
  have hww : ∀ x y, ⟪w x, w y⟫_ℝ = quaternionModel.kappa x y := fun x y => by
    rw [hw, hw, ← hφ, C.kappa_tri_left, hjk]
  -- differences of the translate at `e` and `-e`
  obtain ⟨D, hD⟩ : ∃ D : unitary ℍ[ℝ] → EuclideanSpace ℝ (Fin r), ∀ e, D e = w e - w (-e) :=
    ⟨_, fun _ => rfl⟩
  have hPD : ∀ e y, ⟪P y, D e⟫_ℝ =
      (0 + ⟪(2 : ℝ) • (b * (e : ℍ[ℝ])), (y : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 := by
    intro e y
    rw [hD, inner_sub_right, hPw, hPw, Unitary.coe_neg, star_neg, mul_neg, inner_neg_right,
      real_inner_smul_left, inner_mul_right_eq]
    ring
  have hDD : ∀ e e', ⟪D e, D e'⟫_ℝ = 2 * ⟪(e : ℍ[ℝ]), (e' : ℍ[ℝ])⟫_ℝ := by
    intro e e'
    rw [hD, hD, inner_sub_left, inner_sub_right, inner_sub_right, hww, hww, hww, hww]
    have h1 := kappa_sub_kappa_neg e e'
    have h2 := kappa_sub_kappa_neg (-e) e'
    rw [Unitary.coe_neg, inner_neg_left] at h2
    linarith
  -- their components orthogonal to the copy
  choose η hη using fun e : unitary ℍ[ℝ] =>
    exists_residual P hP (D e) 0 ((2 : ℝ) • (b * (e : ℍ[ℝ]))) (hPD e)
  have hη0 : ∀ e y, ⟪P y, η e⟫_ℝ = (0 + ⟪(0 : ℍ[ℝ]), (y : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 :=
    fun e y => by rw [(hη e).1 y, inner_zero_left, zero_add, zero_div]
  have hηη : ∀ e e', ⟪η e, η e'⟫_ℝ = (2 - 4 * ‖b‖ ^ 2) * ⟪(e : ℍ[ℝ]), (e' : ℍ[ℝ])⟫_ℝ := by
    intro e e'
    rw [(hη e).2 (η e') 0 0 (hη0 e'), inner_zero_right, real_inner_comm (η e') (D e),
      (hη e').2 (D e) 0 _ (hPD e), hDD, real_inner_smul_left, real_inner_smul_right,
      inner_mul_left_mul_left, real_inner_comm (e : ℍ[ℝ]) (e' : ℍ[ℝ])]
    ring
  -- nine orthogonal vectors do not fit in feature rank at most eight
  have hc : 2 - 4 * ‖b‖ ^ 2 ≤ 0 := by
    by_contra hpos
    replace hpos := not_le.mp hpos
    have hPR : ∀ y, ⟪P y, P 1 + P (-1)⟫_ℝ = 1 := fun y => by
      rw [inner_add_right, hP, hP, kappa_add_kappa_neg]
    have hPQ : ∀ y q, ⟪P y, P q - P (-q)⟫_ℝ = ⟪(y : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ := fun y q => by
      rw [inner_sub_right, hP, hP, kappa_sub_kappa_neg]
    have hRη : ∀ e, ⟪P 1 + P (-1), η e⟫_ℝ = 0 := fun e => by
      rw [inner_add_left, (hη e).1, (hη e).1, add_zero]
    have hQη : ∀ q e, ⟪P q - P (-q), η e⟫_ℝ = 0 := fun q e => by
      rw [inner_sub_left, (hη e).1, (hη e).1, sub_zero]
    have hRR : ⟪P 1 + P (-1), P 1 + P (-1)⟫_ℝ = 2 := by
      rw [inner_add_left, hPR, hPR]
      norm_num
    have hRQ : ∀ q, ⟪P 1 + P (-1), P q - P (-q)⟫_ℝ = 0 := fun q => by
      rw [inner_add_left, hPQ, hPQ, Unitary.coe_neg, inner_neg_left, add_neg_cancel]
    have hQQ : ∀ q q', ⟪P q - P (-q), P q' - P (-q')⟫_ℝ = 2 * ⟪(q : ℍ[ℝ]), (q' : ℍ[ℝ])⟫_ℝ :=
      fun q q' => by
        rw [inner_sub_left, hPQ, hPQ, Unitary.coe_neg, inner_neg_left]
        ring
    let v : Option (Fin 4 ⊕ Fin 4) → EuclideanSpace ℝ (Fin r) := fun i =>
      match i with
      | none => P 1 + P (-1)
      | some (Sum.inl k) => P (basis4 k) - P (-basis4 k)
      | some (Sum.inr k) => η (basis4 k)
    have hli : LinearIndependent ℝ v := by
      refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun i h0 => ?_) (fun i i' hii' => ?_)
      · have h00 : ⟪v i, v i⟫_ℝ = 0 := by rw [h0, inner_zero_left]
        rcases i with _ | (k | k)
        · change ⟪P 1 + P (-1), P 1 + P (-1)⟫_ℝ = 0 at h00
          rw [hRR] at h00
          norm_num at h00
        · change ⟪P (basis4 k) - P (-basis4 k), P (basis4 k) - P (-basis4 k)⟫_ℝ = 0 at h00
          rw [hQQ, inner_basis4, ite_eq_left rfl] at h00
          norm_num at h00
        · change ⟪η (basis4 k), η (basis4 k)⟫_ℝ = 0 at h00
          rw [hηη, inner_basis4, ite_eq_left rfl, mul_one] at h00
          linarith
      · rcases i with _ | (k | k) <;> rcases i' with _ | (l | l)
        · exact absurd rfl hii'
        · exact hRQ _
        · exact hRη _
        · change ⟪P (basis4 k) - P (-basis4 k), P 1 + P (-1)⟫_ℝ = 0
          rw [real_inner_comm]
          exact hRQ _
        · change ⟪P (basis4 k) - P (-basis4 k), P (basis4 l) - P (-basis4 l)⟫_ℝ = 0
          have hkl : k ≠ l := fun h => hii' (by rw [h])
          rw [hQQ, inner_basis4, ite_eq_right hkl, mul_zero]
        · exact hQη _ _
        · change ⟪η (basis4 k), P 1 + P (-1)⟫_ℝ = 0
          rw [real_inner_comm]
          exact hRη _
        · change ⟪η (basis4 k), P (basis4 l) - P (-basis4 l)⟫_ℝ = 0
          rw [real_inner_comm]
          exact hQη _ _
        · change ⟪η (basis4 k), η (basis4 l)⟫_ℝ = 0
          have hkl : k ≠ l := fun h => hii' (by rw [h])
          rw [hηη, inner_basis4, ite_eq_right hkl, mul_zero]
    have h9 := hli.fintype_card_le_finrank
    rw [finrank_euclideanSpace_fin] at h9
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin] at h9
    omega
  have hc' : 0 ≤ 2 - 4 * ‖b‖ ^ 2 := by
    have h := real_inner_self_nonneg (x := η 1)
    rw [hηη, real_inner_self_eq_norm_sq, CStarRing.norm_coe_unitary, one_pow, mul_one] at h
    exact h
  have hb2 : ‖b‖ ^ 2 = 1 / 2 := by linarith
  -- the point `√2 • b` of the copy has reading one with `m`
  have hu : ‖Real.sqrt 2 • b‖ = 1 := by
    have h2 : ‖Real.sqrt 2 • b‖ ^ 2 = 1 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hσ, hb2]
      norm_num
    rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]
  set x₀ : unitary ℍ[ℝ] := ⟨Real.sqrt 2 • b, by
    rw [← SetLike.mem_coe, coe_unitary_eq_sphere, mem_sphere_zero_iff_norm]
    exact hu⟩
  have hbx : ⟪b, (x₀ : ℍ[ℝ])⟫_ℝ = Real.sqrt 2 / 2 := by
    change ⟪b, Real.sqrt 2 • b⟫_ℝ = _
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hb2]
    ring
  have hneg := C.kappa_nonneg (j (-x₀)) m
  rw [hf', Unitary.coe_neg, inner_neg_right, hbx, le_div_iff₀ hσ0, zero_mul] at hneg
  have ha : a = Real.sqrt 2 / 2 := by
    have ha2 : a ^ 2 ≤ (Real.sqrt 2 / 2) ^ 2 := by
      rw [div_pow, hσ]
      linarith
    have := (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).mp ha2
    linarith
  refine ⟨x₀, (C.kappa_eq_one_iff _ _).mp ?_⟩
  rw [hf', hbx, ha, add_halves, div_self hσ0.ne']

/-- A unit vector read against a realization of the unit-quaternion reading in Euclidean
five-space is a one-point extension of feature rank five. -/
private lemma hasOnePointFeatureRank_of_inner (P : unitary ℍ[ℝ] → EuclideanSpace ℝ (Fin 5))
    (hP : ∀ x y, ⟪P x, P y⟫_ℝ = quaternionModel.kappa x y) (v : EuclideanSpace ℝ (Fin 5))
    (hv : ‖v‖ = 1) : HasOnePointFeatureRank (fun x => ⟪P x, v⟫_ℝ) 5 :=
  ⟨fun o => o.elim v P, fun x y => (hP x y).symm, fun _ => rfl, hv⟩

/-- In a ternary comparison structure of feature rank five, a reading-preserving copy of the
unit-quaternion model is the whole structure; the transfer need not be preserved. -/
theorem bijective_of_hasFeatureRank_five_of_kappa {M : Type*} (C : TernaryComparison M)
    (hr : C.HasFeatureRank 5) (j : unitary ℍ[ℝ] → M)
    (hjk : ∀ x y, C.kappa (j x) (j y) = quaternionModel.kappa x y) :
    Function.Bijective j := by
  refine ⟨injective_of_kappa C j hjk, fun m => ?_⟩
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  obtain ⟨φ, hφ⟩ := hr
  have hnorm : ∀ p, ‖φ p‖ = 1 := fun p => by
    have h := hφ p p
    rw [C.kappa_self, real_inner_self_eq_norm_sq] at h
    rw [← Real.sqrt_sq (norm_nonneg _), ← h, Real.sqrt_one]
  have hP : ∀ x y, ⟪φ (j x), φ (j y)⟫_ℝ = quaternionModel.kappa x y := fun x y => by
    rw [← hφ, hjk]
  -- the translate `x ↦ tri m (j 1) (j x)` also preserves the reading and sends `1` to `m`
  obtain ⟨k, hkdef⟩ : ∃ k : unitary ℍ[ℝ] → M, ∀ x, k x = C.tri m (j 1) (j x) :=
    ⟨_, fun _ => rfl⟩
  have hk : ∀ x y, ⟪φ (k x), φ (k y)⟫_ℝ = quaternionModel.kappa x y := fun x y => by
    rw [← hφ, hkdef, hkdef, C.kappa_tri_left, hjk]
  have hk1 : k 1 = m := by rw [hkdef, C.tri_self_right]
  -- every translate point reads at least one against `j 1` and `j (-1)` together
  have hge : ∀ x, 1 ≤ C.kappa (j 1) (k x) + C.kappa (j (-1)) (k x) := by
    intro x
    obtain ⟨a, b, hab, hf⟩ := (hasOnePointFeatureRank_five_iff _).mp
      (hasOnePointFeatureRank_of_inner (fun y => φ (j y)) hP (φ (k x)) (hnorm _))
    have hf' : ∀ y, ⟪φ (j y), φ (k x)⟫_ℝ = (a + ⟪b, (y : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 := hf
    have hba : ‖b‖ ≤ a := (forall_nonneg_iff_norm_le a b).mp fun y => by
      rw [← hf', ← hφ]
      exact C.kappa_nonneg _ _
    rw [hφ, hφ, hf', hf', Unitary.coe_neg, inner_neg_right, ← add_div,
      le_div_iff₀ hσ0, one_mul]
    have ha0 : 0 ≤ a := (norm_nonneg b).trans hba
    have h4 : Real.sqrt 2 ^ 2 ≤ (2 * a) ^ 2 := by
      rw [hσ]
      nlinarith [mul_le_mul hba hba (norm_nonneg b) ha0]
    have := (pow_le_pow_iff_left₀ hσ0.le (by linarith) two_ne_zero).mp h4
    linarith
  -- these sums form a one-point extension of the translated copy by a unit vector
  set v : EuclideanSpace ℝ (Fin 5) := (Real.sqrt 2)⁻¹ • (φ (j 1) + φ (j (-1))) with hvdef
  have hu2 : ‖φ (j 1) + φ (j (-1))‖ ^ 2 = 2 := by
    have h0 := kappa_add_kappa_neg 1 1
    rw [quaternionModel.kappa_self] at h0
    rw [norm_add_sq_real, hnorm, hnorm, hP]
    linarith
  have hv : ‖v‖ = 1 := by
    rw [hvdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hσ0,
      ← Real.sqrt_sq (norm_nonneg (φ (j 1) + φ (j (-1)))), hu2, inv_mul_cancel₀ hσ0.ne']
  obtain ⟨A, B, hAB, hg⟩ := (hasOnePointFeatureRank_five_iff _).mp
    (hasOnePointFeatureRank_of_inner (fun x => φ (k x)) hk v hv)
  have hgx : ∀ x, C.kappa (j 1) (k x) + C.kappa (j (-1)) (k x) = A + ⟪B, (x : ℍ[ℝ])⟫_ℝ := by
    intro x
    have h : ⟪φ (k x), v⟫_ℝ = (A + ⟪B, (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 := hg x
    rw [hvdef, real_inner_smul_right, inner_add_right, ← hφ, ← hφ, C.kappa_symm (k x),
      C.kappa_symm (k x), inv_mul_eq_div, div_left_inj' hσ0.ne'] at h
    exact h
  -- the sum for `m` is exactly one
  have h1 : C.kappa (j 1) m + C.kappa (j (-1)) m = 1 := by
    have e1 := hgx 1
    have e2 := hgx (-1)
    rw [Unitary.coe_neg, inner_neg_right] at e2
    have hA : A ≤ 1 := by nlinarith [sq_nonneg ‖B‖]
    have g1 := hge 1
    have g2 := hge (-1)
    rw [hk1] at e1 g1
    linarith
  -- the readings of `m` then give `2 * a = √2` and `‖b‖ ^ 2 = 1 / 2`
  obtain ⟨a, b, hab, hf⟩ := (hasOnePointFeatureRank_five_iff _).mp
    (hasOnePointFeatureRank_of_inner (fun y => φ (j y)) hP (φ m) (hnorm m))
  have hf' : ∀ y, ⟪φ (j y), φ m⟫_ℝ = (a + ⟪b, (y : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 := hf
  rw [hφ, hφ, hf', hf', Unitary.coe_neg, inner_neg_right, ← add_div,
    div_eq_one_iff_eq hσ0.ne'] at h1
  have h2a : 2 * a = Real.sqrt 2 := by linarith
  have hb2 : ‖b‖ ^ 2 = 1 / 2 := by
    have h4 : (2 * a) ^ 2 = 2 := by rw [h2a, hσ]
    linarith
  have hu : ‖Real.sqrt 2 • b‖ = 1 := by
    have h2 : ‖Real.sqrt 2 • b‖ ^ 2 = 1 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hσ, hb2]
      norm_num
    rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]
  set x₀ : unitary ℍ[ℝ] := ⟨Real.sqrt 2 • b, by
    rw [← SetLike.mem_coe, coe_unitary_eq_sphere, mem_sphere_zero_iff_norm]
    exact hu⟩
  have hbx : ⟪b, (x₀ : ℍ[ℝ])⟫_ℝ = Real.sqrt 2 / 2 := by
    change ⟪b, Real.sqrt 2 • b⟫_ℝ = _
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hb2]
    ring
  -- so `m` has reading one with the point `√2 • b` of the copy
  refine ⟨x₀, (C.kappa_eq_one_iff _ _).mp ?_⟩
  rw [hφ, hf', hbx, show a = Real.sqrt 2 / 2 by linarith, add_halves, div_self hσ0.ne']

section Doubled

/-- `xor (xor a b) c = xor (xor a' b) c` exactly when `a = a'`. -/
private lemma xor_xor_left_iff (a a' b c : Bool) :
    xor (xor a b) c = xor (xor a' b) c ↔ a = a' := by
  revert a a' b c
  decide

/-- `xor (xor b c) a = xor (xor b c) a'` exactly when `a = a'`. -/
private lemma xor_xor_right_iff (a a' b c : Bool) :
    xor (xor b c) a = xor (xor b c) a' ↔ a = a' := by
  revert a a' b c
  decide

/-- Features of two copies of the unit quaternions in Euclidean nine-space: a common coordinate
`1 / √2` and the quaternion coordinates divided by `√2` in the block of the layer. -/
private def dfeature (x : unitary ℍ[ℝ] × Bool) : EuclideanSpace ℝ (Fin 9) :=
  (1 / Real.sqrt 2) • WithLp.toLp 2 (if x.2 then
    ![1, 0, 0, 0, 0, (x.1 : ℍ[ℝ]).re, (x.1 : ℍ[ℝ]).imI, (x.1 : ℍ[ℝ]).imJ, (x.1 : ℍ[ℝ]).imK]
  else
    ![1, (x.1 : ℍ[ℝ]).re, (x.1 : ℍ[ℝ]).imI, (x.1 : ℍ[ℝ]).imJ, (x.1 : ℍ[ℝ]).imK, 0, 0, 0, 0])

/-- The features of two copies realize the model reading within a layer and one half between
layers. -/
private lemma inner_dfeature (x y : unitary ℍ[ℝ] × Bool) :
    ⟪dfeature x, dfeature y⟫_ℝ =
      if x.2 = y.2 then quaternionModel.kappa x.1 y.1 else 1 / 2 := by
  obtain ⟨p, a⟩ := x
  obtain ⟨q, c⟩ := y
  have h2 : 1 / Real.sqrt 2 * (1 / Real.sqrt 2) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  rw [dfeature, dfeature, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, h2,
    EuclideanSpace.inner_toLp_toLp]
  change _ = if a = c then (1 + ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ) / 2 else 1 / 2
  cases a <;> cases c <;> simp [dotProduct, Fin.sum_univ_succ, inner_eq_components] <;> ring

/-- Two copies of the unit quaternions: the transfer is `x * y⁻¹ * z` on the quaternion parts and
adds the layers modulo two; the reading is that of the model within a layer and one half between
layers. -/
private def doubledModel : TernaryComparison (unitary ℍ[ℝ] × Bool) where
  tri x y z := (x.1 * y.1⁻¹ * z.1, xor (xor x.2 y.2) z.2)
  kappa x y := if x.2 = y.2 then quaternionModel.kappa x.1 y.1 else 1 / 2
  tri_self_left x z := Prod.ext (by simp) (by simp)
  tri_self_right x z := Prod.ext (by simp) (by simp)
  tri_assoc x y z u v := Prod.ext (by simp [mul_assoc]) (by simp)
  kappa_symm x y := by
    by_cases h : x.2 = y.2
    · rw [ite_eq_left h, ite_eq_left h.symm, quaternionModel.kappa_symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  kappa_eq_one_iff x y := by
    by_cases h : x.2 = y.2
    · rw [ite_eq_left h, quaternionModel.kappa_eq_one_iff, Prod.ext_iff]
      exact ⟨fun h1 => ⟨h1, h⟩, fun h1 => h1.1⟩
    · rw [ite_eq_right h]
      exact ⟨fun h1 => by norm_num at h1, fun h1 => absurd (congrArg Prod.snd h1) h⟩
  kappa_nonneg x y := by
    split_ifs
    · exact quaternionModel.kappa_nonneg _ _
    · norm_num
  kappa_tri_right x y u v := by
    dsimp only
    by_cases h : x.2 = y.2
    · rw [ite_eq_left ((xor_xor_left_iff _ _ _ _).mpr h), ite_eq_left h]
      exact quaternionModel.kappa_tri_right x.1 y.1 u.1 v.1
    · rw [ite_eq_right (fun h' => h ((xor_xor_left_iff _ _ _ _).mp h')), ite_eq_right h]
  kappa_tri_left u v x y := by
    dsimp only
    by_cases h : x.2 = y.2
    · rw [ite_eq_left ((xor_xor_right_iff _ _ _ _).mpr h), ite_eq_left h]
      exact quaternionModel.kappa_tri_left u.1 v.1 x.1 y.1
    · rw [ite_eq_right (fun h' => h ((xor_xor_right_iff _ _ _ _).mp h')), ite_eq_right h]
  kappa_gram_nonneg n x c := by
    have h := real_inner_self_nonneg (x := ∑ i, c i • dfeature (x i))
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      inner_dfeature] at h
    refine h.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_)
    rw [← inner_dfeature, ← inner_dfeature, real_inner_comm (dfeature (x i))]
    ring

/-- The doubled model has feature rank at most nine. -/
private lemma doubledModel_hasFeatureRank {r : ℕ} (hr : 9 ≤ r) : doubledModel.HasFeatureRank r := by
  have h9 : doubledModel.HasFeatureRank 9 := ⟨dfeature, fun x y => (inner_dfeature x y).symm⟩
  rw [← gramRankLE_iff_hasFeatureRank] at h9 ⊢
  exact fun n x => (h9 n x).trans hr

end Doubled

/-- Eight is the largest feature rank in which every transfer- and reading-preserving copy of the
unit-quaternion model exhausts the structure: in feature rank nine, two copies of the unit
quaternions with reading one half between them contain a proper copy. -/
theorem forall_bijective_iff_le_eight (r : ℕ) :
    (∀ (M : Type) (C : TernaryComparison M) (j : unitary ℍ[ℝ] → M), C.HasFeatureRank r →
        (∀ x y z, j (quaternionModel.tri x y z) = C.tri (j x) (j y) (j z)) →
        (∀ x y, C.kappa (j x) (j y) = quaternionModel.kappa x y) → Function.Bijective j) ↔
      r ≤ 8 := by
  constructor
  · intro H
    by_contra hr
    have h := H (unitary ℍ[ℝ] × Bool) doubledModel (fun x => (x, false))
      (doubledModel_hasFeatureRank (by omega)) (fun _ _ _ => rfl) (fun _ _ => rfl)
    obtain ⟨x, hx⟩ := h.2 (1, true)
    exact Bool.false_ne_true (congrArg Prod.snd hx)
  · intro hr M C j hC hjt hjk
    exact bijective_of_hasFeatureRank_le_eight C hC hr j hjt hjk

end D5.S3.Quantum.AURICOmega.QuaternionModelMaximality
