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

/-! The dimension and feature rank bounds are sharp.

A noncommutative ternary comparison structure of feature rank `r` on a preconnected, locally
compact space, with continuous transfer, a reading `kappa x` continuous at `x`, and a map into
`ℝ^d` continuous and injective on a neighbourhood of a point, has `3 ≤ d` and `5 ≤ r`. Every
pair with `3 ≤ d` and `5 ≤ r` occurs: the unit quaternions with transfer `x * y⁻¹ * z` and
reading `(1 + ⟪x, y⟫) / 2` form a compact, connected such structure of feature rank five, and on
the open hemisphere of positive real part the imaginary part, followed by appending zero
coordinates, is a continuous injection into `ℝ^d`. -/

open Filter Set
open scoped Topology InnerProductSpace Quaternion

namespace D5.S3.Quantum.AURICOmega.DimensionRankRealization

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel

/-- A unit quaternion satisfies `re ^ 2 + imI ^ 2 + imJ ^ 2 + imK ^ 2 = 1`. -/
private theorem normSq_components_unitary (q : unitary ℍ[ℝ]) :
    (q : ℍ[ℝ]).re ^ 2 + (q : ℍ[ℝ]).imI ^ 2 + (q : ℍ[ℝ]).imJ ^ 2 + (q : ℍ[ℝ]).imK ^ 2 = 1 := by
  rw [← Quaternion.normSq_def', Quaternion.normSq_eq_norm_mul_self,
    CStarRing.norm_coe_unitary, mul_one]

/-- On the unit quaternions of positive real part the imaginary part is injective: the real
part is the positive square root of `1 - ‖im q‖ ^ 2`. -/
theorem injOn_im_of_re_pos :
    Set.InjOn (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).im) {q | 0 < (q : ℍ[ℝ]).re} := by
  intro p hp q hq h
  have hI : (p : ℍ[ℝ]).imI = (q : ℍ[ℝ]).imI := by
    simpa using congrArg QuaternionAlgebra.imI h
  have hJ : (p : ℍ[ℝ]).imJ = (q : ℍ[ℝ]).imJ := by
    simpa using congrArg QuaternionAlgebra.imJ h
  have hK : (p : ℍ[ℝ]).imK = (q : ℍ[ℝ]).imK := by
    simpa using congrArg QuaternionAlgebra.imK h
  have hsq : (p : ℍ[ℝ]).re ^ 2 = (q : ℍ[ℝ]).re ^ 2 := by
    have h1 := normSq_components_unitary p
    have h2 := normSq_components_unitary q
    rw [hI, hJ, hK] at h1
    linarith
  have hre : (p : ℍ[ℝ]).re = (q : ℍ[ℝ]).re :=
    (pow_left_inj₀ (le_of_lt hp) (le_of_lt hq) two_ne_zero).1 hsq
  exact Subtype.ext (Quaternion.ext _ _ hre hI hJ hK)

/-- The transfer `x * y⁻¹ * z` of the unit quaternion model is continuous. -/
theorem continuous_tri_quaternionModel :
    Continuous fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] × unitary ℍ[ℝ] =>
      quaternionModel.tri p.1 p.2.1 p.2.2 := by
  change Continuous fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] × unitary ℍ[ℝ] => p.1 * p.2.1⁻¹ * p.2.2
  fun_prop

/-- The reading `(1 + ⟪x, y⟫) / 2` of the unit quaternion model is continuous. -/
theorem continuous_kappa_quaternionModel :
    Continuous fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] => quaternionModel.kappa p.1 p.2 := by
  change Continuous fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] =>
    (1 + ⟪(p.1 : ℍ[ℝ]), (p.2 : ℍ[ℝ])⟫_ℝ) / 2
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
part, by `injOn_im_of_re_pos`. -/
private theorem injOn_imPad (m : ℕ) : Set.InjOn (imPad m) {q | 0 < (q : ℍ[ℝ]).re} := by
  intro p hp q hq h
  have hc : ∀ j : Fin 3, ![(p : ℍ[ℝ]).imI, (p : ℍ[ℝ]).imJ, (p : ℍ[ℝ]).imK] j =
      ![(q : ℍ[ℝ]).imI, (q : ℍ[ℝ]).imJ, (q : ℍ[ℝ]).imK] j := fun j => by
    have h' := congrArg (fun v : EuclideanSpace ℝ (Fin (3 + m)) => v (Fin.castAdd m j)) h
    simpa [imPad, Fin.append_left] using h'
  refine injOn_im_of_re_pos hp hq ?_
  exact Quaternion.ext _ _ (by simp) (by simpa using hc 0) (by simpa using hc 1)
    (by simpa using hc 2)

/-- A ternary comparison structure with all the hypotheses of the dimension bound, on a space
with a continuous map into `ℝ^d` injective on a neighbourhood of a point and with feature rank
`r`, exists if and only if `3 ≤ d` and `5 ≤ r`. -/
theorem exists_model_iff (d r : ℕ) :
    (∃ (M : Type) (_ : TopologicalSpace M) (_ : LocallyCompactSpace M) (_ : PreconnectedSpace M)
        (C : TernaryComparison M) (o : M) (V : Set M) (f : M → EuclideanSpace ℝ (Fin d)),
        (Continuous fun p : M × M × M => C.tri p.1 p.2.1 p.2.2) ∧
        (∀ x, ContinuousAt (C.kappa x) x) ∧ C.Noncommutative ∧ C.HasFeatureRank r ∧
        V ∈ 𝓝 o ∧ ContinuousOn f V ∧ Set.InjOn f V) ↔ 3 ≤ d ∧ 5 ≤ r := by
  constructor
  · rintro ⟨M, _, _, _, C, o, V, f, htri, hkappa, hnc, hr, hV, hf, hfi⟩
    exact D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound.three_le_dim_of_hasFeatureRank C
      htri hkappa hnc hr hV f hf hfi
  · rintro ⟨hd, hr⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hd
    have : CompactSpace (unitary ℍ[ℝ]) := compactSpace_unitary
    refine ⟨unitary ℍ[ℝ], inferInstance, inferInstance, preconnectedSpace_unitary,
      quaternionModel, 1, {q | 0 < (q : ℍ[ℝ]).re}, imPad m, continuous_tri_quaternionModel,
      fun x => (continuous_kappa_quaternionModel.comp
        (continuous_const.prodMk continuous_id)).continuousAt,
      quaternionModel_noncommutative,
      D5.S3.Quantum.AURICOmega.GramRankFeatureMap.hasFeatureRank_mono hr
        quaternionModel_hasFeatureRank_five, ?_, (continuous_imPad m).continuousOn,
      injOn_imPad m⟩
    refine (isOpen_lt continuous_const
      (Quaternion.continuous_re.comp continuous_subtype_val)).mem_nhds ?_
    simp

end D5.S3.Quantum.AURICOmega.DimensionRankRealization
