/- GID: D5/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/TernaryComparisonIsomorphism
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unit-quaternion isomorphism for reading-complete rank-five ternary comparisons. -/

import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup
import Mathlib.Topology.Sequences

/-! Ternary comparison structures isomorphic to the unit quaternions.

Let `C` be a noncommutative, chain-connected ternary comparison structure of feature rank five
whose reading touches zero, and fix a point `o`. Its embedding into the unit quaternions,
multiplied on the left by the inverse of the image of `o`, sends `o` to one, the transfer to
`x * y⁻¹ * z` and preserves the reading, since left multiplication by a unit quaternion preserves
the real inner product. Its image `H` is a subgroup. The reading between unit quaternions is
`1 - ‖x - y‖ ^ 2 / 4`, so a sequence in `H` converging in the quaternions has readings tending to
one; if the reading is complete, the sequence has a reading limit in `C`, whose image is the limit
of the sequence, so `H` is closed. Chains of `C` map to chains in `H`, and two noncommuting points
of the group at `o` map to noncommuting unit quaternions. A closed, chain-connected,
noncommutative subgroup of the unit quaternions is everything, so the embedding is a bijection. -/

open scoped InnerProductSpace Quaternion

namespace D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
open D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup

/-- The reading is complete: every sequence whose readings tend to one uniformly in both
indices has a point whose readings with the sequence tend to one. -/
def ReadingComplete {M : Type*} (C : TernaryComparison M) : Prop :=
  ∀ x : ℕ → M,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → 1 - ε < C.kappa (x m) (x n)) →
    ∃ a : M, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 - ε < C.kappa (x n) a

/-- The quaternion reading is one minus a quarter of the squared distance. -/
lemma kappa_eq_one_sub_dist_sq (a b : unitary ℍ[ℝ]) :
    quaternionModel.kappa a b = 1 - dist a b ^ 2 / 4 := by
  change (1 + ⟪(a : ℍ[ℝ]), (b : ℍ[ℝ])⟫_ℝ) / 2 = _
  rw [Subtype.dist_eq, dist_eq_norm, norm_sub_sq_real, CStarRing.norm_coe_unitary,
    CStarRing.norm_coe_unitary]
  ring

/-- A noncommutative, chain-connected ternary comparison structure of feature rank five whose
reading touches zero embeds into the unit quaternions with a prescribed point `o` sent to one,
the transfer sent to `x * y⁻¹ * z` and the reading preserved. -/
lemma exists_normalized_embedding {M : Type*} (C : TernaryComparison M)
    (hnc : C.Noncommutative) (hconn : C.ChainConnected) (hzero : C.TouchesZero)
    (hr : C.HasFeatureRank 5) (o : M) :
    ∃ v : M → unitary ℍ[ℝ], Function.Injective v ∧ v o = 1 ∧
      (∀ x y z : M, v (C.tri x y z) = v x * (v y)⁻¹ * v z) ∧
      (∀ x y : M, C.kappa x y = quaternionModel.kappa (v x) (v y)) := by
  obtain ⟨u, hinj, htri, hk⟩ := exists_unitQuaternion_embedding C hnc hconn hzero hr
  refine ⟨fun x => (u o)⁻¹ * u x, fun x y h => hinj (mul_left_cancel h), inv_mul_cancel _,
    fun x y z => ?_, fun x y => ?_⟩
  · simp only [htri, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  · have h := quaternionModel.kappa_tri_left 1 (u o) (u x) (u y)
    change quaternionModel.kappa (1 * (u o)⁻¹ * u x) (1 * (u o)⁻¹ * u y) = _ at h
    rw [one_mul] at h
    rw [h, hk]
    rfl

/-- The image of a map that sends `o` to one and the transfer to `x * y⁻¹ * z` is a subgroup:
products and inverses of images are images of `tri x o y` and `tri o x o`. -/
private def rangeSubgroup {M : Type*} (C : TernaryComparison M) (v : M → unitary ℍ[ℝ])
    (o : M) (hvo : v o = 1) (htri : ∀ x y z : M, v (C.tri x y z) = v x * (v y)⁻¹ * v z) :
    Subgroup (unitary ℍ[ℝ]) where
  carrier := Set.range v
  one_mem' := ⟨o, hvo⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨C.tri x o y, by rw [htri, hvo, inv_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨C.tri o x o, by rw [htri, hvo, one_mul, mul_one]⟩

/-- Under a complete reading, the image of a reading-preserving map is closed. -/
lemma isClosed_range {M : Type*} (C : TernaryComparison M) (v : M → unitary ℍ[ℝ])
    (hk : ∀ x y : M, C.kappa x y = quaternionModel.kappa (v x) (v y))
    (hcomplete : ReadingComplete C) : IsClosed (Set.range v) := by
  refine IsSeqClosed.isClosed fun w p hw hwp => ?_
  choose x hx using hw
  obtain ⟨a, ha⟩ := hcomplete x fun ε hε => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hwp.cauchySeq (min 1 ε) (lt_min one_pos hε)
    refine ⟨N, fun m n hm hn => ?_⟩
    have hd := hN m hm n hn
    have hd0 := dist_nonneg (x := w m) (y := w n)
    rw [hk, hx, hx, kappa_eq_one_sub_dist_sq]
    have h1 := hd.trans_le (min_le_left 1 ε)
    have h2 := hd.trans_le (min_le_right 1 ε)
    nlinarith
  refine ⟨a, tendsto_nhds_unique (Metric.tendsto_atTop.mpr fun ε hε => ?_) hwp⟩
  obtain ⟨N, hN⟩ := ha (ε ^ 2 / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [hk, hx, kappa_eq_one_sub_dist_sq] at h
  have h' : dist (w n) (v a) ^ 2 < ε ^ 2 := by linarith
  exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).mp h'

/-- A noncommutative, chain-connected ternary comparison structure of feature rank five whose
reading touches zero and is complete is isomorphic to the unit quaternions with transfer
`x * y⁻¹ * z` and reading `(1 + ⟪x, y⟫) / 2`, by a bijection sending a prescribed point `o` to
one. -/
theorem exists_unitQuaternion_equiv {M : Type*} (C : TernaryComparison M)
    (hnc : C.Noncommutative) (hconn : C.ChainConnected) (hzero : C.TouchesZero)
    (hr : C.HasFeatureRank 5) (hcomplete : ReadingComplete C) (o : M) :
    ∃ u : M ≃ unitary ℍ[ℝ], u o = 1 ∧
      (∀ x y z : M, u (C.tri x y z) = quaternionModel.tri (u x) (u y) (u z)) ∧
      (∀ x y : M, C.kappa x y = quaternionModel.kappa (u x) (u y)) := by
  obtain ⟨v, hinj, hvo, htri, hk⟩ := exists_normalized_embedding C hnc hconn hzero hr o
  have htop : rangeSubgroup C v o hvo htri = ⊤ := by
    refine eq_top_of_isClosed_of_chainConnected _ (isClosed_range C v hk hcomplete) ?_ ?_
    · rintro ε hε _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact (hconn ε hε x y).lift v fun a b h => ⟨⟨b, rfl⟩, by rwa [← hk]⟩
    · obtain ⟨x, y, hxy⟩ := (C.noncommutative_iff o).mp hnc
      refine ⟨v x, ⟨x, rfl⟩, v y, ⟨y, rfl⟩, fun h => hxy (hinj ?_)⟩
      rw [htri, htri, hvo, inv_one, mul_one, mul_one, h]
  have hsurj : Function.Surjective v := fun q => (Subgroup.eq_top_iff' _).mp htop q
  exact ⟨Equiv.ofBijective v ⟨hinj, hsurj⟩, hvo, htri, hk⟩

end D5.S3.Quantum.AURICOmega.TernaryComparisonIsomorphism
