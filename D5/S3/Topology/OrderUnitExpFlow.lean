/- GID: D5/S3/Topology/OrderUnitExpFlow
   generality: G
   mirror-B: D5/B/S3/Topology/OrderUnitExpFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Exponential]
   utility: none
   digest: Positive zero contacts imply original exponential cone invariance on Banach spaces. -/

module

public import D5.S3.Topology.OrderUnitNorm

/-! The exponential and every functional use the original norm topology.
Four-slot audit evidence: https://github.com/the-omega-institute/trureturing/issues/28368. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology

namespace D5.S3.Topology.OrderUnitExpFlow

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private lemma no_exit (A : OrderUnitNorm.Data E) (w v : ℝ → E)
    (hd : ∀ t, HasDerivAt w (v t) t)
    (hstart : w 0 ∈ interior (A.cone : Set E))
    (hstrict : ∀ t, 0 ≤ t → w t ∈ A.cone →
      ∀ β : E →L[ℝ] ℝ, (∀ z ∈ A.cone, 0 ≤ β z) →
        β (w t) = 0 → 0 < β A.unit → 0 < β (v t))
    (S : ℝ) (hS : 0 ≤ S) : w S ∈ interior (A.cone : Set E) := by
  have hw : Continuous w := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  by_contra hbad
  let B : Set ℝ := Icc 0 S ∩ w ⁻¹' (interior (A.cone : Set E))ᶜ
  have hBc : IsCompact B :=
    isCompact_Icc.inter_right (isClosed_compl_iff.mpr isOpen_interior |>.preimage hw)
  obtain ⟨T, hT⟩ := hBc.exists_isLeast ⟨S, ⟨⟨hS, le_rfl⟩, hbad⟩⟩
  have hTpos : 0 < T := by
    apply lt_of_le_of_ne hT.1.1.1
    intro hzero
    exact hT.1.2 (hzero ▸ hstart)
  have hbefore (s : ℝ) (hs : s ∈ Ico 0 T) : w s ∈ interior (A.cone : Set E) := by
    by_contra h
    have hb : s ∈ B := ⟨⟨hs.1, hs.2.le.trans hT.1.1.2⟩, h⟩
    exact (not_le_of_gt hs.2) (hT.2 hb)
  have hwT : w T ∈ A.cone := by
    have hc : IsClosed (w ⁻¹' (A.cone : Set E)) := A.closed.preimage hw
    have hs : Ico 0 T ⊆ w ⁻¹' (A.cone : Set E) :=
      fun s hs => @interior_subset E _ (A.cone : Set E) (w s) (hbefore s hs)
    apply closure_minimal hs hc
    rw [closure_Ico hTpos.ne]
    exact ⟨hTpos.le, le_rfl⟩
  obtain ⟨β, hβ, hβz, hβu⟩ := A.boundary_support (w T) hwT hT.1.2
  have hder := β.hasFDerivAt.comp_hasDerivAt T (hd T)
  have hnonpos : β (v T) ≤ 0 := by
    apply le_of_tendsto hder.tendsto_slope_zero_left
    filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr hTpos)] with h hh
    have hv : 0 ≤ β (w (T + h)) :=
      hβ _ (interior_subset (hbefore (T + h) ⟨by linarith [hh.1], by linarith [hh.2]⟩))
    simp only [Function.comp_apply, hβz, sub_zero, smul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hh.2.le) hv
  exact (not_le_of_gt (hstrict T hTpos.le hwT β hβ hβz hβu)) hnonpos

variable [CompleteSpace E]

private lemma forward (A : OrderUnitNorm.Data E) (H : E →L[ℝ] E)
    (hcp : ∀ β : E →L[ℝ] ℝ, (∀ z ∈ A.cone, 0 ≤ β z) →
      ∀ z ∈ A.cone, β z = 0 → 0 ≤ β (H z))
    (t : ℝ) (ht : 0 ≤ t) (y : E) (hy : y ∈ A.cone) :
    NormedSpace.exp (t • H) y ∈ A.cone := by
  let a := A.orderNorm (H A.unit) + 1
  let d := a • A.unit - H A.unit
  have ha : d - A.unit ∈ A.cone := by
    have h := (A.norm_attained (H A.unit)).2.1
    convert h using 1 <;> dsimp [d, a] <;> module
  have hpert (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
      (1 - ε) • (NormedSpace.exp (t • H) y) +
        (ε * Real.exp (a * t)) • A.unit ∈ interior (A.cone : Set E) := by
    let w : ℝ → E := fun s => (1 - ε) • (NormedSpace.exp (s • H) y) +
      (ε * Real.exp (a * s)) • A.unit
    have hd (s : ℝ) : HasDerivAt w
        (H (w s) + (ε * Real.exp (a * s)) • d) s := by
      have hflow := (hasDerivAt_exp_smul_const' H s).clm_apply (hasDerivAt_const s y)
      have hflow' : HasDerivAt (fun r : ℝ => NormedSpace.exp (r • H) y)
          (H (NormedSpace.exp (s • H) y)) s := by
        simpa only [mul_apply_eq_comp, map_zero, add_zero] using hflow
      have hpert := (((hasDerivAt_id s).const_mul a).exp.const_mul ε).smul_const A.unit
      have hpert' : HasDerivAt (fun r : ℝ => (ε * Real.exp (a * r)) • A.unit)
          ((ε * Real.exp (a * s) * a) • A.unit) s := by
        simpa only [id_eq, mul_one, mul_assoc] using hpert
      have he : H (w s) + (ε * Real.exp (a * s)) • d =
          (1 - ε) • H (NormedSpace.exp (s • H) y) +
            (ε * Real.exp (a * s) * a) • A.unit := by
        dsimp [w, d]
        simp only [map_add, map_smul, smul_sub, smul_smul]
        module
      rw [he]
      exact (hflow'.const_smul (1 - ε)).add hpert'
    have hw0 : w 0 ∈ interior (A.cone : Set E) := by
      simpa [w] using A.cone.convex.combo_self_interior_mem_interior
        hy A.interior_unit (sub_nonneg.mpr hε1.le) hε (by ring : (1 - ε) + ε = 1)
    apply no_exit A w _ hd hw0 ?_ t ht
    intro s hs hws β hβ hβz hβu
    have hcpz := hcp β hβ (w s) hws hβz
    have hdpos : 0 < β d := by
      have hh := hβ (d - A.unit) ha
      simp only [map_sub] at hh
      linarith
    simp only [map_add, map_smul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos hcpz (mul_pos (mul_pos hε (Real.exp_pos _)) hdpos)
  have hlim : Tendsto
      (fun ε : ℝ => (1 - ε) • (NormedSpace.exp (t • H) y) +
        (ε * Real.exp (a * t)) • A.unit)
      (𝓝[>] 0) (𝓝 (NormedSpace.exp (t • H) y)) := by
    have hc : Continuous (fun ε : ℝ => (1 - ε) • (NormedSpace.exp (t • H) y) +
        (ε * Real.exp (a * t)) • A.unit) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply A.closed.mem_of_tendsto hlim
  have hlt : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hlt] with ε hε hε1
  exact interior_subset (hpert ε hε hε1)

/-- All continuous positive zero contacts suffice for both time directions in
the original Banach space, without any condition on the unit's image. -/
theorem zero_contact_exp (A : OrderUnitNorm.Data E) (H : E →L[ℝ] E)
    (hzero : ∀ β : E →L[ℝ] ℝ, (∀ c ∈ A.cone, 0 ≤ β c) →
      ∀ c ∈ A.cone, β c = 0 → β (H c) = 0) :
    ∀ t : ℝ, ∀ c ∈ A.cone, NormedSpace.exp (t • H) c ∈ A.cone := by
  have hp : ∀ β : E →L[ℝ] ℝ, (∀ c ∈ A.cone, 0 ≤ β c) →
      ∀ c ∈ A.cone, β c = 0 → 0 ≤ β (H c) := by
    intro β hβ c hc hz
    exact le_of_eq (hzero β hβ c hc hz).symm
  have hm : ∀ β : E →L[ℝ] ℝ, (∀ c ∈ A.cone, 0 ≤ β c) →
      ∀ c ∈ A.cone, β c = 0 → 0 ≤ β ((-H) c) := by
    intro β hβ c hc hz
    simp only [neg_apply, map_neg, hzero β hβ c hc hz, neg_zero, le_refl]
  intro t c hc
  by_cases ht : 0 ≤ t
  · exact forward A H hp t ht c hc
  · simpa only [neg_smul, smul_neg, neg_neg] using
      forward A (-H) hm (-t) (by linarith) c hc

#print axioms zero_contact_exp

end D5.S3.Topology.OrderUnitExpFlow
