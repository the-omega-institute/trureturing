/- GID: D5/S3/Quantum/Foundation/BinaryCenterSections
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/BinaryCenterSections
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Singleton center graphs give exact interior sections of the original normalized base. -/

import D5.S3.Quantum.Foundation.BinaryCenterGraph
import D5.S3.Quantum.Foundation.ExclusionIncidence
import D5.S3.Quantum.Foundation.UniqueConfirmationDensity

/-! The original singleton center-section theorem in XI §138.3. -/

noncomputable section
open Set Metric

namespace D5.S3.Quantum.Foundation.BinaryCenterSections

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalFacePolarity SingleLabelNormalBody ContinuousFrameSum BinaryCenterGeometry
open ReciprocalExclusionLimits

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

variable (hc : IsClosed (C : Set V))
  (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
  (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)

include hc hs hg hB in
private theorem center_graph_interior (p : pure C u) (b : ExclusionChart C u p)
    (g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V)
    (hb : ∀ x (hx : ‖x‖ = 1), g x = center hB (chartPure hc hs hg hB p b x hx))
    (hK : g '' Metric.closedBall 0 1 ⊆ base C u) (hi : Function.Injective g)
    {z : EuclideanSpace ℝ (Fin b.dim)} (hz : ‖z‖ < 1) :
    g z ∈ intrinsicInterior ℝ (base C u) := by
  by_contra hn
  have hfro : g z ∈ intrinsicFrontier ℝ (base C u) := by
    rw [← closure_sdiff_intrinsicInterior]
    exact ⟨subset_closure (hK ⟨z, by simpa using hz.le, rfl⟩), hn⟩
  obtain ⟨r, hr⟩ := MixedExclusionGeometry.frontier_covered hc hs hg hfro
  have all := (exclusion_ball_faces hc hs hg hB).1
  obtain ⟨f, hf, hzero⟩ := (all r).2.2.2.2.2.2
  have hvan := UniqueConfirmationDensity.affine_zero_inside_ball (f.toAffineMap.comp g)
    (fun w hw => (hf.1 (g w) (hK ⟨w, by simpa using hw, rfl⟩).1).1)
    hz (show f (g z) = 0 from (hzero ▸ hr).2)
  have hsame (x : EuclideanSpace ℝ (Fin b.dim)) (hx : ‖x‖ = 1) :
      g x = center hB r := by
    let q := chartPure hc hs hg hB p b x hx
    have hcq : center hB q ∈ intrinsicInterior ℝ (exclusion C u q) := by
      rw [MixedExclusionGeometry.chart_intrinsic q (hB q).some]
      exact ⟨0, by simp, rfl⟩
    have hfc : f (center hB q) = 0 := by rw [← hb x hx]; exact hvan x
    have hsub : exclusion C u q ⊆ exclusion C u r := by
      intro y hy
      rw [hzero]
      exact ⟨hy.1, UniqueConfirmationDensity.zero_on_exclusion_of_zero_interior hB q f
        (fun v hv => (hf.1 v hv).1) hcq hfc y hy⟩
    have he : exclusion C u q = exclusion C u r :=
      chart_face_eq (hB r).some (all q).2.2.1
        ((all q).2.2.2.2.1.mono (all r).2.2.2.2.1.subset hsub) (all q).1
    exact (hb x hx).trans (center_eq_of_exclusion_eq hB q r he)
  let e := EuclideanSpace.basisFun (Fin b.dim) ℝ ⟨0, b.dim_pos⟩
  have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin b.dim) ℝ).norm_eq_one _
  have heq : e = -e := hi ((hsame e he).trans (hsame (-e) (by simpa using he)).symm)
  have h2 : (2 : ℝ) • e = 0 := by
    calc
      (2 : ℝ) • e = e + e := two_smul ℝ e
      _ = e + (-e) := congrArg (fun v => e + v) heq
      _ = 0 := add_neg_cancel e
  have he0 : e = 0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [he0, norm_zero] at he
  norm_num at he

include hc hs hg hB in
private theorem center_graph_transverse (p : pure C u) (b : ExclusionChart C u p)
    (g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V)
    (hb : ∀ x (hx : ‖x‖ = 1), g x = center hB (chartPure hc hs hg hB p b x hx))
    (hi : Function.Injective g)
    (hsec : g '' Metric.closedBall 0 1 = base C u ∩ Set.range g)
    (x : EuclideanSpace ℝ (Fin b.dim)) (hx : ‖x‖ = 1) :
    Disjoint g.linear.range
      (hB (chartPure hc hs hg hB p b x hx)).some.param.linear.range := by
  let _ : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  let q := chartPure hc hs hg hB p b x hx
  let a := (hB q).some
  let E := g '' Metric.closedBall 0 1
  have hcq : center hB q = g x := (hb x hx).symm
  have hext : center hB q ∈ E.extremePoints ℝ := by
    rw [hcq]
    apply affine_extreme_image _ (convex_closedBall _ _) g hi.injOn
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    simpa using hx
  apply Submodule.disjoint_def.mpr
  rintro z ⟨w, hw⟩ ⟨v, hv⟩
  let ε : ℝ := (‖v‖ + 1)⁻¹
  have hε : 0 < ε := inv_pos.mpr (by positivity)
  have hsmall : ‖ε • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg hε.le]
    dsimp [ε]
    exact (inv_mul_le_one₀ (by positivity : 0 < ‖v‖+1)).mpr (by linarith)
  have hparam (t : ℝ) : a.param (t • v) = center hB q + t • z := by
    rw [show a.param (t • v) = a.param.linear (t • v) + a.param 0 from
      congrFun a.param.decomp (t • v), map_smul, hv]
    exact add_comm _ _
  have hinK (t : ℝ) (ht : ‖t • v‖ ≤ 1) : center hB q + t • z ∈ base C u :=
    (hparam t) ▸ (chart_mem a ht).1
  have hinRange (t : ℝ) : center hB q + t • z ∈ Set.range g := by
    refine ⟨t • w + x, ?_⟩
    rw [show g (t • w + x) = g.linear (t • w) + g x from g.map_vadd x (t • w),
      map_smul, hw, ← hcq, add_comm]
  have hp : center hB q + ε • z ∈ E := by
    dsimp only [E]
    rw [hsec]
    exact ⟨hinK ε hsmall, hinRange ε⟩
  have hm : center hB q + (-ε) • z ∈ E := by
    dsimp only [E]
    rw [hsec]
    exact ⟨hinK (-ε) (by simpa using hsmall), hinRange (-ε)⟩
  have hmid : center hB q ∈ openSegment ℝ
      (center hB q + ε • z) (center hB q + (-ε) • z) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have he := hext.2 hp hm hmid
  have hz : ε • z = 0 := by
    apply add_left_cancel (a := center hB q)
    simpa using he
  exact (smul_eq_zero.mp hz).resolve_left hε.ne'

include hc hs hg hB in
/-- A singleton-label original ball has an entire interior center image and
an exact section of the original base by its image affine carrier. -/
theorem whole_ball_center_section (hBC : binaryCompatible hB)
    (p : pure C u) (hp : SingleLabel C u p) (b : ExclusionChart C u p) :
    ∃ g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
      (∀ x (hx : ‖x‖ = 1), g x = center hB (chartPure hc hs hg hB p b x hx)) ∧
      Function.Injective g ∧ Module.finrank ℝ g.linear.range = b.dim ∧
      (∀ x, ‖x‖ < 1 → g x ∈ intrinsicInterior ℝ (base C u)) ∧
      g '' Metric.closedBall 0 1 = base C u ∩ Set.range g ∧
      (∀ x (hx : ‖x‖ = 1), Disjoint g.linear.range
        (hB (chartPure hc hs hg hB p b x hx)).some.param.linear.range) := by
  obtain ⟨g, hb, hK, hu, hi, hr⟩ := whole_ball_center_graph hc hs hg hB hBC p b
  have hgi := (hi hp).1
  have hint (x : EuclideanSpace ℝ (Fin b.dim)) (hx : ‖x‖ < 1) :=
    center_graph_interior hc hs hg hB p b g hb hK hgi hx
  have hsection : g '' Metric.closedBall 0 1 = base C u ∩ Set.range g := by
    apply Subset.antisymm
    · rintro y hy
      exact ⟨hK hy, by obtain ⟨x, hx, rfl⟩ := hy; exact ⟨x, rfl⟩⟩
    · rintro y ⟨hy, z, rfl⟩
      have hn : ‖z‖ ≤ 1 := by
        by_contra hn
        have hz : 1 < ‖z‖ := lt_of_not_ge hn
        have hz0 : 0 < ‖z‖ := lt_trans zero_lt_one hz
        let w := ‖z‖⁻¹ • z
        have hw : ‖w‖ = 1 := by simp [w, norm_smul, hz0.ne']
        have hseg : g w ∈ openSegment ℝ (g 0) (g z) := by
          refine ⟨1 - ‖z‖⁻¹, ‖z‖⁻¹, ?_, inv_pos.mpr hz0, by ring, ?_⟩
          · exact sub_pos.mpr ((inv_lt_one₀ hz0).mpr hz)
          · rw [← Convex.combo_affine_apply (by ring)]
            congr 1
            simp [w]
        have hri := (base_convex C u).openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
          (hint 0 (by simp : ‖(0 : EuclideanSpace ℝ (Fin b.dim))‖ < 1))
          (subset_intrinsicClosure hy) hseg
        have hbd : g w ∈ intrinsicFrontier ℝ (base C u) := by
          rw [hb w hw]
          exact MixedExclusionGeometry.exclusion_frontier hc hs hg hB _
            (chart_mem (hB _).some (by simp))
        rw [← closure_sdiff_intrinsicInterior] at hbd
        exact hbd.2 hri
      exact ⟨z, by simpa using hn, rfl⟩
  exact ⟨g, hb, hgi, (hi hp).2, hint, hsection,
    center_graph_transverse hc hs hg hB p b g hb hgi hsection⟩

include hc hs hg in
/-- The complete singleton center-section geometry in the original EB3 model.
The dimension bound and existence are on the same original normalized base. -/
theorem original_center_sections [Nontrivial V] (h3 : threeBallExclusions C u)
    (hBC : binaryCompatible (OriginalExclusionLimits.ballHyp h3)) :
    6 ≤ Module.finrank ℝ (affineSpan ℝ (base C u)).direction ∧
    (∃ p : pure C u, SingleLabel C u p) ∧
    ∀ p : pure C u, SingleLabel C u p →
      ∃ b : ExclusionChart C u p, b.dim = 3 ∧
      ∃ g : EuclideanSpace ℝ (Fin b.dim) →ᵃ[ℝ] V,
        (∀ x (hx : ‖x‖ = 1), g x = center
          (OriginalExclusionLimits.ballHyp h3)
          (chartPure hc hs hg (OriginalExclusionLimits.ballHyp h3) p b x hx)) ∧
        Function.Injective g ∧ Module.finrank ℝ g.linear.range = 3 ∧
        (∀ x, ‖x‖ < 1 → g x ∈ intrinsicInterior ℝ (base C u)) ∧
        g '' Metric.closedBall 0 1 =
          base C u ∩ (affineSpan ℝ (g '' Metric.closedBall 0 1) : Set V) ∧
        intrinsicFrontier ℝ (g '' Metric.closedBall 0 1) = g '' Metric.sphere 0 1 ∧
        g '' Metric.sphere 0 1 ⊆ intrinsicFrontier ℝ (base C u) ∧
        (∀ x (hx : ‖x‖ = 1), Disjoint g.linear.range
          ((OriginalExclusionLimits.ballHyp h3)
            (chartPure hc hs hg (OriginalExclusionLimits.ballHyp h3) p b x hx)).some.param.linear.range) := by
  let B := OriginalExclusionLimits.ballHyp h3
  let chart (p : pure C u) : ExclusionChart C u p :=
    ⟨3, by norm_num, CommonOldExclusionConfirmation.oldChart h3 p,
      (h3 p).choose_spec.1, (h3 p).choose_spec.2⟩
  obtain ⟨p₀, hp₀⟩ := ActualExclusionBoundary.original_singleton_label_exists hc hs hg B
  have hdim : 6 ≤ Module.finrank ℝ (affineSpan ℝ (base C u)).direction := by
    obtain ⟨q, r, hq, hr, hqr⟩ := pure_pair_in_ball hc hs hg B p₀
    have hnat := native_dimension hc hs hg B p₀ hp₀ (chart p₀) q hq (chart q)
    have hnonzero : (p₀ : V) ≠ 0 := by
      intro he
      have hunit := (pure_mem p₀).2
      rw [he, map_zero] at hunit
      norm_num at hunit
    have hbase := normalized_face_dimension C u hs ⟨p₀, (pure_mem p₀).1, hnonzero⟩
    rw [hg, finrank_top] at hbase
    dsimp [chart] at hnat
    omega
  refine ⟨hdim, ⟨p₀, hp₀⟩, ?_⟩
  intro p hp
  let b := chart p
  obtain ⟨g, hb, hi, hrank, hint, hsection, htrans⟩ :=
    whole_ball_center_section hc hs hg B hBC p hp b
  have hspan : (affineSpan ℝ (g '' Metric.closedBall 0 1) : Set V) = Set.range g := by
    have hs : affineSpan ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) 1) = ⊤ :=
      (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
        ⟨0, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
    rw [← AffineSubspace.map_span, hs]
    ext y
    simp
  refine ⟨b, rfl, g, hb, hi, hrank, hint, ?_, ?_, ?_, htrans⟩
  · rw [hspan]
    exact hsection
  · rw [ExclusionIncidence.intrinsic_image g hi, ExclusionIncidence.intrinsic_ball]
  · rintro _ ⟨x, hx, rfl⟩
    rw [hb x (by simpa using hx)]
    exact MixedExclusionGeometry.exclusion_frontier hc hs hg B _
      (chart_mem (B _).some (by simp))

end D5.S3.Quantum.Foundation.BinaryCenterSections
