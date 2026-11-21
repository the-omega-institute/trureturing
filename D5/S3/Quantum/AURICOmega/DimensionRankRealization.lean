/- GID: D5/S3/Quantum/AURICOmega/DimensionRankRealization
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/DimensionRankRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The bounds d >= 3, r >= 5 for ternary comparisons are attained by unit quaternions. -/

import D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound
import D5.S3.Quantum.AURICOmega.GramRankFeatureMap
import D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
import D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup

/-! The dimension and feature rank bounds are sharp.

A noncommutative ternary comparison structure of feature rank at most `r` on a preconnected,
locally compact space, with continuous transfer, a reading `kappa x` continuous at `x`, and a map
into `ℝ^d` continuous and injective on a neighbourhood of a point, has `3 ≤ d` and `5 ≤ r`. Every
pair with `3 ≤ d` and `5 ≤ r` occurs, already among compact, Hausdorff, connected spaces with
jointly continuous reading and a map continuous everywhere and injective on an open set: the unit
quaternions with transfer `x * y⁻¹ * z` and reading `(1 + ⟪x, y⟫) / 2` form such a structure of
feature rank five, and on the closed hemisphere of nonnegative real part the imaginary part,
followed by appending zero coordinates, is injective. -/

open Filter Set
open scoped Topology InnerProductSpace Quaternion

namespace D5.S3.Quantum.AURICOmega.DimensionRankRealization

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel

/-- On the unit quaternions of nonnegative real part the imaginary part is injective: the real
part is the nonnegative square root of `1 - ‖im q‖ ^ 2`. -/
theorem injOn_im_of_re_nonneg :
    Set.InjOn (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).im) {q | 0 ≤ (q : ℍ[ℝ]).re} := by
  intro p hp q hq h
  have hI : (p : ℍ[ℝ]).imI = (q : ℍ[ℝ]).imI := by
    simpa using congrArg QuaternionAlgebra.imI h
  have hJ : (p : ℍ[ℝ]).imJ = (q : ℍ[ℝ]).imJ := by
    simpa using congrArg QuaternionAlgebra.imJ h
  have hK : (p : ℍ[ℝ]).imK = (q : ℍ[ℝ]).imK := by
    simpa using congrArg QuaternionAlgebra.imK h
  have hsq : (p : ℍ[ℝ]).re ^ 2 = (q : ℍ[ℝ]).re ^ 2 := by
    have h1 := D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup.sq_add_sq_coe_unitary p
    have h2 := D5.S3.Quantum.AURICOmega.UnitQuaternionClosedSubgroup.sq_add_sq_coe_unitary q
    rw [hI, hJ, hK] at h1
    linarith
  have hre : (p : ℍ[ℝ]).re = (q : ℍ[ℝ]).re :=
    (pow_left_inj₀ hp hq two_ne_zero).1 hsq
  exact Subtype.ext (Quaternion.ext _ _ hre hI hJ hK)

/-- The transfer `x * y⁻¹ * z` of the unit quaternion model is continuous. -/
theorem continuous_tri_quaternionModel :
    Continuous fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] × unitary ℍ[ℝ] =>
      quaternionModel.tri p.1 p.2.1 p.2.2 := by
  change Continuous fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] × unitary ℍ[ℝ] => p.1 * p.2.1⁻¹ * p.2.2
  fun_prop

/-- The unit quaternions form a compact space: they are the unit sphere of `ℍ`. -/
private theorem compactSpace_unitary : CompactSpace (unitary ℍ[ℝ]) :=
  isCompact_iff_compactSpace.mp (by
    rw [coe_unitary_eq_sphere]
    exact isCompact_sphere 0 1)

/-- The imaginary coordinates of a unit quaternion followed by `m` zero coordinates. -/
private noncomputable def imPad (m : ℕ) (q : unitary ℍ[ℝ]) : EuclideanSpace ℝ (Fin (3 + m)) :=
  WithLp.toLp 2 (Fin.append ![(q : ℍ[ℝ]).imI, (q : ℍ[ℝ]).imJ, (q : ℍ[ℝ]).imK] 0)

private theorem continuous_imPad (m : ℕ) : Continuous (imPad m) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    fin_cases j
    · exact Quaternion.continuous_imI.comp continuous_subtype_val
    · exact Quaternion.continuous_imJ.comp continuous_subtype_val
    · exact Quaternion.continuous_imK.comp continuous_subtype_val
  · simp only [Fin.append_right, Pi.zero_apply]
    exact continuous_const

/-- The padded imaginary coordinates are injective on the unit quaternions of positive real
part, by `injOn_im_of_re_nonneg`. -/
private theorem injOn_imPad (m : ℕ) : Set.InjOn (imPad m) {q | 0 < (q : ℍ[ℝ]).re} := by
  intro p hp q hq h
  have hc : ∀ j : Fin 3, ![(p : ℍ[ℝ]).imI, (p : ℍ[ℝ]).imJ, (p : ℍ[ℝ]).imK] j =
      ![(q : ℍ[ℝ]).imI, (q : ℍ[ℝ]).imJ, (q : ℍ[ℝ]).imK] j := fun j => by
    have h' := congrArg (fun v : EuclideanSpace ℝ (Fin (3 + m)) => v (Fin.castAdd m j)) h
    simpa [imPad, Fin.append_left] using h'
  refine injOn_im_of_re_nonneg (show 0 ≤ (p : ℍ[ℝ]).re from le_of_lt hp)
    (show 0 ≤ (q : ℍ[ℝ]).re from le_of_lt hq) ?_
  exact Quaternion.ext _ _ (by simp) (by simpa using hc 0) (by simpa using hc 1)
    (by simpa using hc 2)

/-- Three equivalent conditions on natural numbers `d` and `r`: (1) a ternary comparison
structure with all the hypotheses of the dimension bound, feature rank at most `r` and a map into
`ℝ^d` continuous and injective on a neighbourhood of a point exists; (2) such a structure exists
on a compact, Hausdorff, connected space with jointly continuous reading and a map into `ℝ^d`
continuous everywhere and injective on an open set containing the point; (3) `3 ≤ d` and
`5 ≤ r`. -/
theorem exists_model_tfae (d r : ℕ) :
    List.TFAE [
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : LocallyCompactSpace M) (_ : PreconnectedSpace M)
        (C : TernaryComparison M) (o : M) (V : Set M) (f : M → EuclideanSpace ℝ (Fin d)),
        (Continuous fun p : M × M × M => C.tri p.1 p.2.1 p.2.2) ∧
        (∀ x, ContinuousAt (C.kappa x) x) ∧ C.Noncommutative ∧ C.HasFeatureRank r ∧
        V ∈ 𝓝 o ∧ ContinuousOn f V ∧ Set.InjOn f V,
      ∃ (M : Type) (_ : TopologicalSpace M) (_ : CompactSpace M) (_ : T2Space M)
        (_ : ConnectedSpace M) (C : TernaryComparison M) (o : M) (V : Set M)
        (f : M → EuclideanSpace ℝ (Fin d)),
        (Continuous fun p : M × M × M => C.tri p.1 p.2.1 p.2.2) ∧
        (Continuous fun p : M × M => C.kappa p.1 p.2) ∧ C.Noncommutative ∧ C.HasFeatureRank r ∧
        IsOpen V ∧ o ∈ V ∧ Continuous f ∧ Set.InjOn f V,
      3 ≤ d ∧ 5 ≤ r] := by
  tfae_have 2 → 1 := by
    rintro ⟨M, _, _, _, _, C, o, V, f, htri, hkappa, hnc, hr, hV, ho, hf, hfi⟩
    exact ⟨M, inferInstance, inferInstance, inferInstance, C, o, V, f, htri,
      fun x => (hkappa.comp (continuous_const.prodMk continuous_id)).continuousAt, hnc, hr,
      hV.mem_nhds ho, hf.continuousOn, hfi⟩
  tfae_have 1 → 3 := by
    rintro ⟨M, _, _, _, C, o, V, f, htri, hkappa, hnc, hr, hV, hf, hfi⟩
    exact D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound.three_le_dim_of_hasFeatureRank C
      htri hkappa hnc hr hV f hf hfi
  tfae_have 3 → 2 := by
    rintro ⟨hd, hr⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hd
    have : CompactSpace (unitary ℍ[ℝ]) := compactSpace_unitary
    have := pathConnectedSpace_unitary
    refine ⟨unitary ℍ[ℝ], inferInstance, inferInstance, inferInstance, inferInstance,
      quaternionModel, 1, {q | 0 < (q : ℍ[ℝ]).re}, imPad m, continuous_tri_quaternionModel,
      continuous_kappa_quaternionModel, quaternionModel_noncommutative,
      D5.S3.Quantum.AURICOmega.GramRankFeatureMap.hasFeatureRank_mono hr
        quaternionModel_hasFeatureRank_five,
      isOpen_lt continuous_const (Quaternion.continuous_re.comp continuous_subtype_val),
      by simp, continuous_imPad m, injOn_imPad m⟩
  tfae_finish

end D5.S3.Quantum.AURICOmega.DimensionRankRealization
