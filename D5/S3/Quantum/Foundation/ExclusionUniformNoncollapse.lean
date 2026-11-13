/- GID: D5/S3/Quantum/Foundation/ExclusionUniformNoncollapse
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ExclusionUniformNoncollapse
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Closed pure loci prevent positive-rank collapse of whole exclusion ball charts. -/

import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import D5.S3.Quantum.Foundation.OriginalFacePolarity

/-! Uniform control of entire affine ball charts in the original normalized base. -/

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ExclusionWidthCompactness ContinuousFrameSum

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A nonzero kernel direction pads any point of a closed ball to its sphere
without changing its linear image. -/
private theorem kernel_padding (A : E →L[ℝ] V) {k : E} (hk : k ≠ 0)
    (hAk : A k = 0) {x : E} (hx : ‖x‖ ≤ 1) :
    ∃ y : E, ‖y‖ = 1 ∧ A y = A x := by
  let t : ℝ := (‖x‖ + 1) / ‖k‖
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htk : ‖t • k‖ = ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_of_nonneg ht]
    exact div_mul_cancel₀ _ hkpos.ne'
  have hlarge : 1 ≤ ‖x + t • k‖ := by
    have h := norm_sub_le (x + t • k) x
    rw [add_sub_cancel_left, htk] at h
    linarith
  have hc : Continuous (fun s : ℝ => ‖x + s • k‖) := by fun_prop
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc ht hc.continuousOn
    (show (1 : ℝ) ∈ Icc ‖x + (0 : ℝ) • k‖ ‖x + t • k‖ by simpa using And.intro hx hlarge)
  exact ⟨x + s • k, hs, by simp [hAk]⟩

/-- If an affine sphere lies entirely in the extreme locus, a noninjective
linear part must vanish: a flattened sphere cannot bound a nontrivial disk. -/
private theorem sphere_extreme_injective_or_zero (K : Set V) (c : V)
    (A : E →L[ℝ] V)
    (hsphere : ∀ x : E, ‖x‖ = 1 → c + A x ∈ K.extremePoints ℝ) :
    Function.Injective A ∨ A = 0 := by
  classical
  by_cases hi : Function.Injective A
  · exact Or.inl hi
  · right
    have hn : ¬ ∀ k, A k = 0 → k = 0 := fun h => hi ((injective_iff_map_eq_zero A).mpr h)
    push Not at hn
    obtain ⟨k, hAk, hk⟩ := hn
    have hball (x : E) (hx : ‖x‖ ≤ 1) : c + A x ∈ K.extremePoints ℝ := by
      obtain ⟨y, hy, he⟩ := kernel_padding A hk hAk hx
      simpa [he] using hsphere y hy
    have hc : c ∈ K.extremePoints ℝ := by simpa using hball 0 (by simp)
    have hz (x : E) (hx : ‖x‖ ≤ 1) : A x = 0 := by
      have hmid : c ∈ openSegment ℝ (c + A x) (c + A (-x)) := by
        convert midpoint_mem_openSegment (𝕜 := ℝ) (c + A x) (c + A (-x)) using 1
        simp only [midpoint_eq_smul_add, map_neg, add_add_add_comm, add_neg_cancel,
          add_zero, ← two_smul ℝ c, smul_smul, invOf_mul_self,
          one_smul]
      have he := hc.2 (hball x hx).1 (hball (-x) (by simpa using hx)).1 hmid
      exact add_left_cancel (he.trans (add_zero c).symm)
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · have hn : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      have he := hz (‖x‖⁻¹ • x) hn
      rw [map_smul, smul_eq_zero] at he
      exact he.resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hx))

/-- All affine ball maps whose sphere lies in a closed extreme locus and whose
operator norm stays positive share a positive lower bound on every direction. -/
private theorem compact_ball_maps_lower_bound
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
    (K : Set V) (hK : IsCompact K) (hP : IsClosed (K.extremePoints ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ (c : V) (A : E →L[ℝ] V),
      (∀ x, ‖x‖ ≤ 1 → c + A x ∈ K) →
      (∀ x, ‖x‖ = 1 → c + A x ∈ K.extremePoints ℝ) →
      δ ≤ ‖A‖ → ∀ x, η * ‖x‖ ≤ ‖A x‖ := by
  classical
  let F : Set (V × (E →L[ℝ] V)) := {t |
    (∀ x, ‖x‖ ≤ 1 → t.1 + t.2 x ∈ K) ∧
    (∀ x, ‖x‖ = 1 → t.1 + t.2 x ∈ K.extremePoints ℝ) ∧ δ ≤ ‖t.2‖}
  have hFc : IsClosed F := by
    have hb : IsClosed {t : V × (E →L[ℝ] V) | ∀ x, ‖x‖ ≤ 1 → t.1 + t.2 x ∈ K} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun _ =>
        hK.isClosed.preimage (by fun_prop)
    have hs : IsClosed {t : V × (E →L[ℝ] V) |
        ∀ x, ‖x‖ = 1 → t.1 + t.2 x ∈ K.extremePoints ℝ} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun _ => hP.preimage (by fun_prop)
    exact hb.inter (hs.inter (isClosed_le (f := fun _ : V × (E →L[ℝ] V) => δ)
      continuous_const (g := fun t => ‖t.2‖) (by fun_prop)))
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  let B := max R 0
  have hB : 0 ≤ B := le_max_right _ _
  have hFb : Bornology.IsBounded F := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨2 * B, ?_⟩
    intro t ht
    have hc : ‖t.1‖ ≤ B := by
      have hh := hR t.1 (by simpa using ht.1 0 (by simp))
      exact hh.trans (le_max_left _ _)
    have hA : ‖t.2‖ ≤ 2 * B := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
      intro x hx
      have hcx : ‖t.1 + t.2 x‖ ≤ B :=
        (hR _ (ht.1 x hx.le)).trans (le_max_left _ _)
      have hh := norm_sub_le (t.1 + t.2 x) t.1
      rw [add_sub_cancel_left] at hh
      linarith
    rw [Prod.norm_def]
    exact max_le (by linarith) hA
  have hF : IsCompact F := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hFc, hFb⟩
  let T := F ×ˢ sphere (0 : E) 1
  have hT : IsCompact T := hF.prod (isCompact_sphere _ _)
  have hpos (t : (V × (E →L[ℝ] V)) × E) (ht : t ∈ T) : 0 < ‖t.1.2 t.2‖ := by
    have hn : t.1.2 ≠ 0 := fun hz => by
      have hh := ht.1.2.2
      rw [hz, norm_zero] at hh
      exact (not_le_of_gt hδ) hh
    have hi := (sphere_extreme_injective_or_zero K t.1.1 t.1.2 ht.1.2.1).resolve_right hn
    apply norm_pos_iff.mpr
    intro hz
    have he : t.2 = 0 := hi (by simpa using hz)
    have hv : ‖t.2‖ = 1 := mem_sphere_zero_iff_norm.mp ht.2
    simp [he] at hv
  by_cases hne : T.Nonempty
  · obtain ⟨t, ht, hmin⟩ := hT.exists_isMinOn hne
      (show ContinuousOn (fun t : (V × (E →L[ℝ] V)) × E => ‖t.1.2 t.2‖) T by fun_prop)
    refine ⟨‖t.1.2 t.2‖, hpos t ht, ?_⟩
    intro c A hb hs hnorm x
    by_cases hx : x = 0
    · simp [hx]
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
        simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hxpos.le), hxpos.ne']
      have hh := hmin (show ((c, A), ‖x‖⁻¹ • x) ∈ T from
        ⟨⟨hb, hs, hnorm⟩, mem_sphere_zero_iff_norm.mpr hu⟩)
      change ‖t.1.2 t.2‖ ≤ ‖A (‖x‖⁻¹ • x)‖ at hh
      rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hxpos.le),
        ← div_eq_inv_mul] at hh
      exact (le_div_iff₀ hxpos).mp hh
  · refine ⟨1, zero_lt_one, ?_⟩
    intro c A hb hs hnorm x
    by_cases hx : x = 0
    · simp [hx]
    · exfalso
      apply hne
      refine ⟨((c, A), ‖x‖⁻¹ • x), ⟨hb, hs, hnorm⟩, ?_⟩
      simp [norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), norm_ne_zero_iff.mpr hx]


/-- One positive constant controls every axis of every three-ball chart at every
original pure label. Neither pure closedness nor a continuous chart choice is a premise. -/
theorem all_label_uniform_noncollapse
    [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hEB3 : ∀ p : pure C u, ∃ a : ExclusionChart C u p, a.dim = 3)
    (hW1 : ∀ p : pure C u, width C u (exclusion C u p) = 1) :
    ∃ η > 0, ∀ (p : pure C u) (a : ExclusionChart C u p), a.dim = 3 →
      ∀ v, η * ‖v‖ ≤ ‖a.param.linear v‖ := by
  classical
  have hB : exclusionBalls C u := fun p => by
    obtain ⟨a, _⟩ := hEB3 p
    exact ⟨a⟩
  have hPeq : {x | x ∈ pure C u ∧ width C u (exclusion C u x) = 1} = pure C u := by
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h, hW1 ⟨x, h⟩⟩⟩
  have hP : IsClosed (pure C u) := by
    rw [← hPeq]
    exact (saturated_labels_compact hc hs hg hB).isClosed
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp (effects_compact hs hg).isBounded
  let L := max M 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hLf (f : V →L[ℝ] ℝ) (hf : f ∈ effects C u) : ‖f‖ ≤ L :=
    (hM f hf).trans (le_max_left _ _)
  have hδ : 0 < (2 * L)⁻¹ := inv_pos.mpr (by positivity)
  obtain ⟨η, hη, hηall⟩ := compact_ball_maps_lower_bound
    (E := EuclideanSpace ℝ (Fin 3)) (base C u) (base_compact hc hs) hP hδ
  refine ⟨η, hη, ?_⟩
  intro p a hd
  rcases a with ⟨d, hdp, f, hfi, hfw⟩
  dsimp only at hd
  subst d
  let A : EuclideanSpace ℝ (Fin 3) →L[ℝ] V := f.linear.toContinuousLinearMap
  have hf (x : EuclideanSpace ℝ (Fin 3)) : f x = f 0 + A x := by
    have hh := congrFun f.decomp x
    simpa [A, add_comm] using hh
  have hb (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ 1) : f 0 + A x ∈ base C u := by
    rw [← hf]
    exact (hfw ▸ mem_image_of_mem f (mem_closedBall_zero_iff.mpr hx)).1
  have hbdry := OriginalFacePolarity.chart_boundary hc hs hg hB p
    (⟨3, hdp, f, hfi, hfw⟩ : ExclusionChart C u p)
  have hsp (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) :
      f 0 + A x ∈ (base C u).extremePoints ℝ := by
    rw [← hf]
    have hh : f x ∈ f '' sphere 0 1 := ⟨x, mem_sphere_zero_iff_norm.mpr hx, rfl⟩
    rw [← hbdry] at hh
    exact hh.2
  have hF : {x | x ∈ base C u ∧ comparison C u p x = 0} = exclusion C u p := by
    ext x
    exact ⟨fun h => (comparison_zero_iff hs hg p h.1).mp h.2,
      fun h => ⟨h.1, (comparison_zero_iff hs hg p h.1).mpr h⟩⟩
  have hat := (original_exclusion_width hc hs hg hB p).2
  rw [hF, hW1 p] at hat
  obtain ⟨g, hgE, y, hy, z, hz, hsat⟩ := hat
  rw [← hfw] at hy hz
  obtain ⟨s, hsball, rfl⟩ := hy
  obtain ⟨t, htball, rfl⟩ := hz
  have hst : ‖s - t‖ ≤ 2 := by
    have hsn : ‖s‖ ≤ 1 := mem_closedBall_zero_iff.mp hsball
    have htn : ‖t‖ ≤ 1 := mem_closedBall_zero_iff.mp htball
    exact (norm_sub_le s t).trans (by linarith)
  have hone : (1 : ℝ) ≤ 2 * L * ‖A‖ := by
    calc
      1 = ‖g (f s) - g (f t)‖ := by rw [← hsat]; norm_num
      _ = ‖g (A (s - t))‖ := by rw [hf s, hf t]; simp [map_sub]
      _ ≤ ‖g‖ * ‖A (s - t)‖ := g.le_opNorm _
      _ ≤ L * (‖A‖ * ‖s - t‖) :=
        mul_le_mul (hLf g hgE) (A.le_opNorm _) (norm_nonneg _) hL.le
      _ ≤ L * (‖A‖ * 2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hst (norm_nonneg _)) hL.le
      _ = 2 * L * ‖A‖ := by ring
  have hnorm : (2 * L)⁻¹ ≤ ‖A‖ := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (show 0 < 2 * L by positivity)).mpr
    simpa [mul_comm] using hone
  exact hηall (f 0) A hb hsp hnorm

end D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse

