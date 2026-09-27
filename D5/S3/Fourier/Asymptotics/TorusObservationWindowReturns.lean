/- GID: D5/S3/Fourier/Asymptotics/TorusObservationWindowReturns
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/TorusObservationWindowReturns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Measure.Support]
   utility: none
   digest: Torus observations have full image support and robust positive-density returns. -/

import D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution
import Mathlib.MeasureTheory.Measure.Support

noncomputable section

namespace D5.S3.Fourier.Asymptotics.TorusObservationWindowReturns

open Filter MeasureTheory Set TopologicalSpace Topology
open scoped Topology

/-- Every open observation window meeting the image is visited with bounded gaps after any
vanishing perturbation. The last clause expresses the lower-density bound by its equivalent
eventual epsilon inequalities for initial-segment counting ratios. -/
theorem result {I : Type*} [Fintype I] (g : I → Circle) :
    let G := (Subgroup.zpowers g).topologicalClosure
    letI : CompactSpace G := isCompact_iff_compactSpace.mp
      (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers g)).isCompact
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    let μ := Measure.haarMeasure (⊤ : PositiveCompacts G)
    let a : G := ⟨g, subset_closure (Subgroup.mem_zpowers g)⟩
    ∀ (h : C(G, ℝ)) (e : ℕ → ℝ),
      Tendsto (fun n => e n - h (a ^ n)) atTop (𝓝 0) →
      (Measure.map h μ).support = range h ∧
      ∀ u v : ℝ, (Ioo u v ∩ range h).Nonempty →
        ∃ n₀ M : ℕ, 1 ≤ n₀ ∧
          (∀ n : ℕ, n₀ ≤ n → ∃ m : ℕ, n ≤ m ∧ m ≤ n + M ∧ e m ∈ Ioo u v) ∧
          (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
            1 / ((M : ℝ) + 1) - ε ≤
              (((Finset.range N).filter (fun m => e m ∈ Ioo u v)).card : ℝ) / (N : ℝ)) := by
  classical
  intro G
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers g)).isCompact
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  intro μ a h e he
  have hsupport : (Measure.map h μ).support = range h := by
    apply Subset.antisymm
    · apply Measure.support_subset_of_isClosed (isCompact_range h.continuous).isClosed
      rw [mem_ae_iff, Measure.map_apply h.continuous.measurable
        (isCompact_range h.continuous).isClosed.isOpen_compl.measurableSet]
      simp
    · rintro _ ⟨z, rfl⟩
      rw [Measure.support_eq_forall_isOpen]
      intro U hz hU
      rw [Measure.map_apply h.continuous.measurable hU.measurableSet]
      exact (hU.preimage h.continuous).measure_pos μ ⟨z, hz⟩
  refine ⟨hsupport, ?_⟩
  intro u v hwindow
  obtain ⟨y, hy, z, rfl⟩ := hwindow
  obtain ⟨δ, hδ, hδu, hδv⟩ : ∃ δ : ℝ, 0 < δ ∧ u < h z - 2 * δ ∧ h z + 2 * δ < v := by
    refine ⟨min (h z - u) (v - h z) / 4,
      div_pos (lt_min (sub_pos.mpr hy.1) (sub_pos.mpr hy.2)) (by norm_num), ?_, ?_⟩
    · have := min_le_left (h z - u) (v - h z)
      linarith [hy.1]
    · have := min_le_right (h z - u) (v - h z)
      linarith [hy.2]
  let U : Set G := h ⁻¹' Ioo (h z - δ) (h z + δ)
  have hU : IsOpen U := isOpen_Ioo.preimage h.continuous
  have hUne : U.Nonempty := ⟨z, by change h z - δ < h z ∧ h z < h z + δ; constructor <;> linarith⟩
  have hG : (G : Set (I → Circle)) = closure (range (fun n : ℕ => g ^ n)) :=
    (TorusOrbitEquidistribution.result g).1
  have hdense : DenseRange (fun n : ℕ => a ^ n) := by
    rw [DenseRange, Subtype.dense_iff, ← range_comp]
    simpa only [Function.comp_def, Subgroup.coe_pow, a] using hG.le
  let V : ℕ → Set G := fun k => (fun x => x * a ^ k) ⁻¹' U
  have hV : ∀ k, IsOpen (V k) := fun k => hU.preimage (by fun_prop)
  have hcover : (univ : Set G) ⊆ ⋃ k, V k := by
    intro x _
    have htranslated : DenseRange (fun k : ℕ => x * a ^ k) :=
      (Homeomorph.mulLeft x).surjective.denseRange.comp hdense (by fun_prop)
    obtain ⟨k, hk⟩ := htranslated.exists_mem_open hU hUne
    exact mem_iUnion.mpr ⟨k, hk⟩
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (univ : Set G)).elim_finite_subcover V hV hcover
  let M := t.sup id
  have hreturn (n : ℕ) : ∃ k : ℕ, k ≤ M ∧ h (a ^ (n + k)) ∈ Ioo (h z - δ) (h z + δ) := by
    obtain ⟨k, hkt, hk⟩ := mem_iUnion₂.mp (ht (mem_univ (a ^ n)))
    refine ⟨k, Finset.le_sup (f := id) hkt, ?_⟩
    simpa only [V, U, mem_preimage, ← pow_add] using hk
  have herr : ∀ᶠ n : ℕ in atTop, |e n - h (a ^ n)| < δ := by
    simpa only [Real.dist_eq, sub_zero] using (Metric.tendsto_nhds.mp he δ hδ)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 herr
  let n₀ := max n₁ 1
  have hreturns (n : ℕ) (hn : n₀ ≤ n) :
      ∃ m : ℕ, n ≤ m ∧ m ≤ n + M ∧ e m ∈ Ioo u v := by
    obtain ⟨k, hk, hobs⟩ := hreturn n
    have herror := abs_lt.mp (hn₁ (n + k) (by dsimp [n₀] at hn; omega))
    refine ⟨n + k, by omega, by omega, ?_⟩
    constructor <;> linarith [hobs.1, hobs.2]
  refine ⟨n₀, M, le_max_right _ _, hreturns, ?_⟩
  let L := M + 1
  have hL : 0 < L := by dsimp [L]; omega
  have hblocks (k : ℕ) : ∃ m : ℕ,
      n₀ + k * L ≤ m ∧ m < n₀ + (k + 1) * L ∧ e m ∈ Ioo u v := by
    obtain ⟨m, hm, hm', he'⟩ := hreturns (n₀ + k * L) (by omega)
    refine ⟨m, hm, ?_, he'⟩
    dsimp [L] at *
    nlinarith
  choose b hb using hblocks
  have hbinj : Function.Injective b := by
    apply StrictMono.injective
    intro i j hij
    have hij' : (i + 1) * L ≤ j * L := Nat.mul_le_mul_right L hij
    exact (hb i).2.1.trans_le ((Nat.add_le_add_left hij' n₀).trans (hb j).1)
  have hcount (N : ℕ) : (N - n₀) / L ≤
      ((Finset.range N).filter (fun m => e m ∈ Ioo u v)).card := by
    let K := (N - n₀) / L
    have hsub : (Finset.range K).image b ⊆
        (Finset.range N).filter (fun m => e m ∈ Ioo u v) := by
      intro m hm
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
      have hk' : k + 1 ≤ K := Finset.mem_range.mp hk
      have hmul : (k + 1) * L ≤ N - n₀ :=
        (Nat.mul_le_mul_right L hk').trans (Nat.div_mul_le_self _ _)
      have hn : n₀ ≤ N := by
        have : 0 < (k + 1) * L := Nat.mul_pos (by omega) hL
        omega
      have hbk := (hb k).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (hb k).2.2⟩
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_image_of_injective _ hbinj, Finset.card_range, K] using hc
  have hlinear (N : ℕ) : N ≤ n₀ + L *
      (((Finset.range N).filter (fun m => e m ∈ Ioo u v)).card + 1) := by
    by_cases hn : N < n₀
    · omega
    have hn' : n₀ ≤ N := by omega
    have hmod := Nat.mod_lt (N - n₀) hL
    have hdiv := Nat.mod_add_div (N - n₀) L
    have hmul := Nat.mul_le_mul_left L (hcount N)
    nlinarith [Nat.sub_add_cancel hn']
  intro ε hε
  have hLreal : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hsmall : ∀ᶠ N : ℕ in atTop, (((n₀ : ℝ) + L) / L) / N < ε :=
    (tendsto_const_div_atTop_nhds_zero_nat (((n₀ : ℝ) + L) / L)).eventually (gt_mem_nhds hε)
  filter_upwards [hsmall, eventually_gt_atTop 0] with N hsmall hN
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hc : (N : ℝ) ≤ n₀ + (L : ℝ) *
      ((((Finset.range N).filter (fun m => e m ∈ Ioo u v)).card : ℝ) + 1) := by
    exact_mod_cast hlinear N
  have hsmall' := (div_lt_iff₀ hNreal).mp hsmall
  have hsmall'' := (div_lt_iff₀ hLreal).mp hsmall'
  have hbound : 1 / (L : ℝ) - ε ≤
      (((Finset.range N).filter (fun m => e m ∈ Ioo u v)).card : ℝ) / N := by
    apply (le_div_iff₀ hNreal).mpr
    have hid : (1 / (L : ℝ)) * L = 1 := div_mul_cancel₀ 1 hLreal.ne'
    nlinarith
  simpa only [L, Nat.cast_add, Nat.cast_one] using hbound

#print axioms result

end D5.S3.Fourier.Asymptotics.TorusObservationWindowReturns
