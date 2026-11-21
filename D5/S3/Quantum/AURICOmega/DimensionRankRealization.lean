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

A noncommutative ternary comparison structure of feature rank at most `r` on a preconnected,
locally compact space, with continuous transfer, a reading `kappa x` continuous at `x`, and a map
into `ℝ^d` continuous and injective on a neighbourhood of a point, has `3 ≤ d` and `5 ≤ r`. The
unit quaternions realize every pair with `3 ≤ d` and `5 ≤ r`: with transfer `x * y⁻¹ * z` and
reading `(1 + ⟪x, y⟫) / 2` they form a structure of feature rank five on a compact, Hausdorff,
path-connected space with jointly continuous reading, and the imaginary part followed by zero
coordinates is continuous and injective on the open hemisphere of positive real part, an open
set containing `1`. Carried to `ULift`, the same structure realizes every such pair in every
universe. The imaginary part is injective on a set `S` of unit quaternions exactly when every
`q ∈ S` with `-star q ∈ S` has real part zero; hence the closed hemisphere of nonnegative real
part is the largest set that contains the open hemisphere and on which the imaginary part is
injective. -/

open scoped Topology Quaternion

namespace D5.S3.Quantum.AURICOmega.DimensionRankRealization

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel

universe u v

/-- The unit quaternion `-star q` has real part `-re q` and the imaginary part of `q`. -/
private theorem re_im_neg_star (q : unitary ℍ[ℝ]) :
    ((-star q : unitary ℍ[ℝ]) : ℍ[ℝ]).re = -(q : ℍ[ℝ]).re ∧
      ((-star q : unitary ℍ[ℝ]) : ℍ[ℝ]).im = (q : ℍ[ℝ]).im := by
  simp [Unitary.coe_neg, Unitary.coe_star]

/-- The imaginary part is injective on a set `S` of unit quaternions exactly when every `q ∈ S`
with `-star q ∈ S` has real part zero: two unit quaternions with the same imaginary part have
real parts of the same square, so they are equal or one of them is `-star` of the other. -/
theorem injOn_im_iff (S : Set (unitary ℍ[ℝ])) :
    Set.InjOn (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).im) S ↔
      ∀ q ∈ S, -star q ∈ S → (q : ℍ[ℝ]).re = 0 := by
  constructor
  · intro hinj q hq hq'
    have h := congrArg (fun x : unitary ℍ[ℝ] => (x : ℍ[ℝ]).re)
      (hinj hq' hq (re_im_neg_star q).2)
    have h' : -(q : ℍ[ℝ]).re = (q : ℍ[ℝ]).re := (re_im_neg_star q).1.symm.trans h
    linarith
  · intro hS p hp q hq h
    have hext : ∀ x y : unitary ℍ[ℝ], (x : ℍ[ℝ]).re = (y : ℍ[ℝ]).re →
        (x : ℍ[ℝ]).im = (y : ℍ[ℝ]).im → x = y := fun x y hre him =>
      Subtype.ext (by rw [← Quaternion.re_add_im (x : ℍ[ℝ]), hre, him, Quaternion.re_add_im])
    have hsq : (p : ℍ[ℝ]).re ^ 2 = (q : ℍ[ℝ]).re ^ 2 := by
      have hI : (p : ℍ[ℝ]).imI = (q : ℍ[ℝ]).imI := by
        simpa using congrArg QuaternionAlgebra.imI h
      have hJ : (p : ℍ[ℝ]).imJ = (q : ℍ[ℝ]).imJ := by
        simpa using congrArg QuaternionAlgebra.imJ h
      have hK : (p : ℍ[ℝ]).imK = (q : ℍ[ℝ]).imK := by
        simpa using congrArg QuaternionAlgebra.imK h
      have hn : Quaternion.normSq (p : ℍ[ℝ]) = Quaternion.normSq (q : ℍ[ℝ]) := by
        rw [Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_eq_norm_mul_self,
          CStarRing.norm_coe_unitary, CStarRing.norm_coe_unitary]
      rw [Quaternion.normSq_def', Quaternion.normSq_def', hI, hJ, hK] at hn
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hre | hre
    · exact hext p q hre h
    · have hpq : p = -star q := hext p (-star q) (hre.trans (re_im_neg_star q).1.symm)
        (h.trans (re_im_neg_star q).2.symm)
      have h0 := hS q hq (hpq ▸ hp)
      exact hext p q (by rw [hre, h0, neg_zero]) h

/-- The closed hemisphere of nonnegative real part is the largest set of unit quaternions that
contains the open hemisphere of positive real part and on which the imaginary part is
injective: a unit quaternion `q` with `re q < 0` has the imaginary part of `-star q`, which lies
in the open hemisphere. -/
theorem isGreatest_injOn_im :
    IsGreatest {S : Set (unitary ℍ[ℝ]) | {q : unitary ℍ[ℝ] | 0 < (q : ℍ[ℝ]).re} ⊆ S ∧
        Set.InjOn (fun q : unitary ℍ[ℝ] => (q : ℍ[ℝ]).im) S} {q | 0 ≤ (q : ℍ[ℝ]).re} := by
  refine ⟨⟨?_, (injOn_im_iff _).2 ?_⟩, ?_⟩
  · intro q hq
    have hq : 0 < (q : ℍ[ℝ]).re := hq
    exact le_of_lt hq
  · intro q hq hq'
    have hq : 0 ≤ (q : ℍ[ℝ]).re := hq
    have hq' : 0 ≤ ((-star q : unitary ℍ[ℝ]) : ℍ[ℝ]).re := hq'
    rw [(re_im_neg_star q).1] at hq'
    linarith
  · intro S hS q hq
    obtain ⟨hS, hinj⟩ := hS
    by_contra hneg
    have hlt : (q : ℍ[ℝ]).re < 0 := lt_of_not_ge hneg
    have hmem : -star q ∈ S := hS (show 0 < ((-star q : unitary ℍ[ℝ]) : ℍ[ℝ]).re by
      rw [(re_im_neg_star q).1]
      linarith)
    have h0 := (injOn_im_iff S).1 hinj q hq hmem
    linarith

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

/-- The padded imaginary coordinates are injective on the closed hemisphere of nonnegative real
part, by `isGreatest_injOn_im`. -/
private theorem injOn_imPad (m : ℕ) : Set.InjOn (imPad m) {q | 0 ≤ (q : ℍ[ℝ]).re} := by
  intro p hp q hq h
  have hc : ∀ j : Fin 3, ![(p : ℍ[ℝ]).imI, (p : ℍ[ℝ]).imJ, (p : ℍ[ℝ]).imK] j =
      ![(q : ℍ[ℝ]).imI, (q : ℍ[ℝ]).imJ, (q : ℍ[ℝ]).imK] j := fun j => by
    have h' := congrArg (fun v : EuclideanSpace ℝ (Fin (3 + m)) => v (Fin.castAdd m j)) h
    simpa [imPad, Fin.append_left] using h'
  refine isGreatest_injOn_im.1.2 hp hq ?_
  exact Quaternion.ext _ _ (by simp) (by simpa using hc 0) (by simpa using hc 1)
    (by simpa using hc 2)

/-- The comparison structure `C` carried to `ULift M`: transfer and reading are those of `C` on
the underlying points. -/
private def liftComparison {M : Type v} (C : TernaryComparison M) :
    TernaryComparison (ULift.{u} M) where
  tri x y z := ULift.up (C.tri x.down y.down z.down)
  kappa x y := C.kappa x.down y.down
  tri_self_left x z := congrArg ULift.up (C.tri_self_left x.down z.down)
  tri_self_right x z := congrArg ULift.up (C.tri_self_right x.down z.down)
  tri_assoc x y z p q := congrArg ULift.up (C.tri_assoc x.down y.down z.down p.down q.down)
  kappa_symm x y := C.kappa_symm x.down y.down
  kappa_eq_one_iff x y := (C.kappa_eq_one_iff x.down y.down).trans ⟨ULift.ext, congrArg ULift.down⟩
  kappa_nonneg x y := C.kappa_nonneg x.down y.down
  kappa_tri_right x y p q := C.kappa_tri_right x.down y.down p.down q.down
  kappa_tri_left p q x y := C.kappa_tri_left p.down q.down x.down y.down
  kappa_gram_nonneg n x c := C.kappa_gram_nonneg n (fun i => (x i).down) c

/-- Four equivalent conditions on natural numbers `d` and `r`, with the carriers of (1) and (2)
in an arbitrary universe: (1) a ternary comparison structure with all the hypotheses of the
dimension bound, feature rank at most `r` and a map into `ℝ^d` continuous and injective on a
neighbourhood of a point exists; (2) such a structure exists on a compact, Hausdorff,
path-connected space with jointly continuous reading and a map into `ℝ^d` continuous everywhere
and injective on an open set containing the point; (3) `3 ≤ d` and `5 ≤ r`; (4) the unit
quaternion model has feature rank at most `r` and some map into `ℝ^d` is continuous everywhere
and injective on an open set containing `1`. -/
theorem exists_model_tfae (d r : ℕ) :
    List.TFAE [
      ∃ (M : Type u) (_ : TopologicalSpace M) (_ : LocallyCompactSpace M)
        (_ : PreconnectedSpace M) (C : TernaryComparison M) (o : M) (V : Set M)
        (f : M → EuclideanSpace ℝ (Fin d)),
        (Continuous fun p : M × M × M => C.tri p.1 p.2.1 p.2.2) ∧
        (∀ x, ContinuousAt (C.kappa x) x) ∧ C.Noncommutative ∧ C.HasFeatureRank r ∧
        V ∈ 𝓝 o ∧ ContinuousOn f V ∧ Set.InjOn f V,
      ∃ (M : Type u) (_ : TopologicalSpace M) (_ : CompactSpace M) (_ : T2Space M)
        (_ : PathConnectedSpace M) (C : TernaryComparison M) (o : M) (V : Set M)
        (f : M → EuclideanSpace ℝ (Fin d)),
        (Continuous fun p : M × M × M => C.tri p.1 p.2.1 p.2.2) ∧
        (Continuous fun p : M × M => C.kappa p.1 p.2) ∧ C.Noncommutative ∧ C.HasFeatureRank r ∧
        IsOpen V ∧ o ∈ V ∧ Continuous f ∧ Set.InjOn f V,
      3 ≤ d ∧ 5 ≤ r,
      ∃ (V : Set (unitary ℍ[ℝ])) (f : unitary ℍ[ℝ] → EuclideanSpace ℝ (Fin d)),
        quaternionModel.HasFeatureRank r ∧ IsOpen V ∧ 1 ∈ V ∧ Continuous f ∧ Set.InjOn f V] := by
  tfae_have 2 → 1 := by
    rintro ⟨M, _, _, _, _, C, o, V, f, htri, hkappa, hnc, hr, hV, ho, hf, hfi⟩
    exact ⟨M, inferInstance, inferInstance, inferInstance, C, o, V, f, htri,
      fun x => (hkappa.comp (continuous_const.prodMk continuous_id)).continuousAt, hnc, hr,
      hV.mem_nhds ho, hf.continuousOn, hfi⟩
  tfae_have 1 → 3 := by
    rintro ⟨M, _, _, _, C, o, V, f, htri, hkappa, hnc, hr, hV, hf, hfi⟩
    exact D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound.three_le_dim_of_hasFeatureRank C
      htri hkappa hnc hr hV f hf hfi
  tfae_have 3 → 4 := by
    rintro ⟨hd, hr⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hd
    exact ⟨{q | 0 < (q : ℍ[ℝ]).re}, imPad m,
      D5.S3.Quantum.AURICOmega.GramRankFeatureMap.hasFeatureRank_mono hr
        quaternionModel_hasFeatureRank_five,
      isOpen_lt continuous_const (Quaternion.continuous_re.comp continuous_subtype_val),
      by simp, continuous_imPad m,
      Set.InjOn.mono (fun q (hq : 0 < (q : ℍ[ℝ]).re) => (le_of_lt hq : 0 ≤ (q : ℍ[ℝ]).re))
        (injOn_imPad m)⟩
  tfae_have 4 → 2 := by
    rintro ⟨V, f, ⟨φ, hφ⟩, hV, ho, hf, hfi⟩
    have : CompactSpace (unitary ℍ[ℝ]) := compactSpace_unitary
    have := pathConnectedSpace_unitary
    have htri := continuous_tri_quaternionModel
    have hkappa := continuous_kappa_quaternionModel
    have hnc := quaternionModel_noncommutative
    generalize quaternionModel = C at htri hkappa hnc hφ
    obtain ⟨a, b, c, hne⟩ := hnc
    have hd : Continuous (ULift.down : ULift.{u} (unitary ℍ[ℝ]) → unitary ℍ[ℝ]) :=
      continuous_uliftDown
    refine ⟨ULift.{u} (unitary ℍ[ℝ]), inferInstance, inferInstance, inferInstance,
      Homeomorph.ulift.symm.pathConnectedSpace, liftComparison C, ULift.up 1,
      ULift.down ⁻¹' V, f ∘ ULift.down, ?_, ?_,
      ⟨ULift.up a, ULift.up b, ULift.up c, fun h => hne (congrArg ULift.down h)⟩,
      ⟨φ ∘ ULift.down, fun x y => hφ x.down y.down⟩, hV.preimage hd, ho, hf.comp hd,
      fun x hx y hy hxy => ULift.ext (hfi hx hy hxy)⟩
    · exact continuous_uliftUp.comp (htri.comp (hd.prodMap (hd.prodMap hd)))
    · exact hkappa.comp (hd.prodMap hd)
  tfae_finish

end D5.S3.Quantum.AURICOmega.DimensionRankRealization
