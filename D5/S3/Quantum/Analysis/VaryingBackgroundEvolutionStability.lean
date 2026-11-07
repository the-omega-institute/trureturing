/- GID: D5/S3/Quantum/Analysis/VaryingBackgroundEvolutionStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/VaryingBackgroundEvolutionStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform strong stability under varying contraction backgrounds. -/

import D5.S3.Quantum.Analysis.SeparateMassEvolutionStability
import Mathlib.Topology.ContinuousMap.Compact

/-! # Uniform stability for varying contraction backgrounds -/

open scoped Nat Topology
open MeasureTheory Filter
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.NonautonomousEvolutionStability
open D5.S3.Quantum.Analysis.SeparateMassEvolutionStability

namespace D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private noncomputable def actionDifference (S₁ S : Contraction E) (T : ℝ) :
    E →L[ℂ] C(Set.Icc (0 : ℝ) T, E) :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        ⟨fun h => S₁.action h x - S.action h x,
          (S₁.action_continuous.comp (continuous_subtype_val.prodMk continuous_const)).sub
            (S.action_continuous.comp (continuous_subtype_val.prodMk continuous_const))⟩
      map_add' := by
        intro x y
        ext h
        change S₁.action h (x + y) - S.action h (x + y) =
          (S₁.action h x - S.action h x) + (S₁.action h y - S.action h y)
        simp only [map_add]
        abel
      map_smul' := by
        intro c x
        ext h
        change S₁.action h (c • x) - S.action h (c • x) =
          c • (S₁.action h x - S.action h x)
        simp only [map_smul, smul_sub] }
    2 (fun x => (ContinuousMap.norm_le _ (by positivity)).mpr fun h =>
      (norm_sub_le _ _).trans ((add_le_add (S₁.action_bound h x)
        (S.action_bound h x)).trans_eq (two_mul ‖x‖).symm))

private theorem actionDifference_bound (S₁ S : Contraction E) (T : ℝ) (x : E) :
    ‖actionDifference S₁ S T x‖ ≤ 2 * ‖x‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro h
  change ‖S₁.action h x - S.action h x‖ ≤ _
  exact (norm_sub_le _ _).trans ((add_le_add (S₁.action_bound h x)
    (S.action_bound h x)).trans_eq (two_mul ‖x‖).symm)

/-- Compact-time strong convergence of contraction backgrounds remains uniformly L1-small
after a vectorwise measurable integrably bounded coefficient, for every measurable vector
path in a fixed compact set and every measurable choice of a time in the compact interval. -/
theorem uniform_integral_background_action {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (Sseq : ℕ → Contraction E) (S : Contraction E) (T : ℝ)
    (hSlim : ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ h : ℝ, 0 ≤ h → h ≤ T → ‖(Sseq n).action h x - S.action h x‖ < ε)
    (B : α → E →L[ℂ] E)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x) μ)
    (g : α → ℝ) (hg : Integrable g μ) (hgn : 0 ≤ᵐ[μ] g)
    (hBg : ∀ᵐ s ∂μ, ‖B s‖ ≤ g s) {K : Set E} (hK : IsCompact K) :
    (∀ n (v : α → E) (h : α → ℝ), AEStronglyMeasurable v μ →
      (∀ᵐ s ∂μ, v s ∈ K) → AEStronglyMeasurable h μ →
      Integrable (fun s => (Sseq n).action (h s) (B s (v s)) -
        S.action (h s) (B s (v s))) μ) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (v : α → E) (h : α → ℝ),
      AEStronglyMeasurable v μ → (∀ᵐ s ∂μ, v s ∈ K) →
      AEStronglyMeasurable h μ → (∀ᵐ s ∂μ, h s ∈ Set.Icc 0 T) →
      (∫ s, ‖(Sseq n).action (h s) (B s (v s)) -
        S.action (h s) (B s (v s))‖ ∂μ) < ε := by
  classical
  let F := C(Set.Icc (0 : ℝ) T, E)
  let U : ℕ → E →L[ℂ] F := fun n => actionDifference (Sseq n) S T
  have hU : ∀ x, Tendsto (fun n => U n x) atTop (𝓝 0) := by
    intro x
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := hSlim x ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [dist_zero_right]
    apply (ContinuousMap.norm_lt_iff _ hε).mpr
    intro h
    exact hN n hn h h.2.1 h.2.2
  have hfixed_meas : ∀ n x, AEStronglyMeasurable (fun s => U n (B s x)) μ := by
    intro n x
    exact (U n).continuous.comp_aestronglyMeasurable (hB x)
  have hfixed_bound : ∀ n x, ∀ᵐ s ∂μ,
      ‖U n (B s x)‖ ≤ (g s * 2) * ‖x‖ := by
    intro n x
    filter_upwards [hBg] with s hs
    exact (actionDifference_bound (Sseq n) S T _).trans (by
      have hb := ((B s).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hs (norm_nonneg x))
      nlinarith)
  have hfixed : ∀ x, Tendsto (fun n => ∫ s, ‖U n (B s x)‖ ∂μ) atTop (𝓝 0) := by
    intro x
    have hd := tendsto_integral_of_dominated_convergence
      (fun s => (g s * 2) * ‖x‖) (fun n => (hfixed_meas n x).norm)
      ((hg.mul_const 2).mul_const ‖x‖)
      (fun n => by simpa only [Real.norm_eq_abs, abs_norm] using hfixed_bound n x)
      (Eventually.of_forall fun s => (hU (B s x)).norm)
    simpa only [norm_zero, integral_zero] using hd
  let D : ℕ → α → (E × F) →L[ℂ] (E × F) := fun n s =>
    (0 : (E × F) →L[ℂ] E).prod
      (((U n).comp (B s)).comp (ContinuousLinearMap.fst ℂ E F))
  have hDnorm : ∀ n s z, ‖D n s z‖ = ‖U n (B s z.1)‖ := by
    intro n s z
    change max ‖(0 : E)‖ ‖U n (B s z.1)‖ = _
    rw [norm_zero, max_eq_right (norm_nonneg _)]
  have hD : ∀ n z, AEStronglyMeasurable (fun s => D n s z) μ := by
    intro n z
    exact aestronglyMeasurable_const.prodMk (hfixed_meas n z.1)
  have hDb : ∀ n, ∀ᵐ s ∂μ, ‖D n s‖ ≤ g s * 2 := by
    intro n
    filter_upwards [hBg, hgn] with s hs hgs
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hgs (by positivity))
    intro z
    change ‖((0 : E), U n (B s z.1))‖ ≤ _
    rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    exact (actionDifference_bound (Sseq n) S T _).trans (by
      have hb := ((B s).le_opNorm z.1).trans
        (mul_le_mul hs (norm_fst_le z) (norm_nonneg _) hgs)
      nlinarith)
  have hDlim : ∀ z, Tendsto (fun n => ∫ s, ‖D n s z‖ ∂μ) atTop (𝓝 0) := by
    intro z
    simp_rw [hDnorm]
    exact hfixed z.1
  have hK' : IsCompact ((fun x : E => (x, (0 : F))) '' K) :=
    hK.image (continuous_id.prodMk continuous_const)
  have hu := uniform_integral_evaluation_of_mass D hD (fun _ => hg.mul_const 2)
    (fun _ => hgn.mono fun s hs => mul_nonneg hs (by positivity)) hDb
    (∫ s, g s * 2 ∂μ) (fun _ => le_rfl) hDlim hK'
  have hi : ∀ n (v : α → E) (h : α → ℝ), AEStronglyMeasurable v μ →
      (∀ᵐ s ∂μ, v s ∈ K) → AEStronglyMeasurable h μ →
      Integrable (fun s => (Sseq n).action (h s) (B s (v s)) -
        S.action (h s) (B s (v s))) μ := by
    intro n v h hv hvK hh
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun x : E => x) continuousOn_id
    have hiv := evaluation_integrable_of_bound B hB hg hgn hBg hv C
      (hvK.mono fun s hs => hC _ hs)
    apply (hiv.norm.mul_const 2).mono'
      (((Sseq n).action_continuous.comp_aestronglyMeasurable
        (hh.prodMk hiv.aestronglyMeasurable)).sub
        (S.action_continuous.comp_aestronglyMeasurable (hh.prodMk hiv.aestronglyMeasurable)))
    exact Eventually.of_forall fun s => (norm_sub_le _ _).trans (by
      linarith [(Sseq n).action_bound (h s) (B s (v s)),
        S.action_bound (h s) (B s (v s))])
  refine ⟨hi, ?_⟩
  intro ε hε
  filter_upwards [hu.2 ε hε] with n hn
  intro v h hv hvK hh hhT
  have hv' : AEStronglyMeasurable (fun s => (v s, (0 : F))) μ :=
    hv.prodMk aestronglyMeasurable_const
  have hvK' : ∀ᵐ s ∂μ, (v s, (0 : F)) ∈ (fun x : E => (x, (0 : F))) '' K :=
    hvK.mono fun s hs => ⟨v s, hs, rfl⟩
  have hsmall := hn (fun s => (v s, (0 : F))) hv' hvK'
  apply lt_of_le_of_lt (b := ∫ s, ‖D n s (v s, (0 : F))‖ ∂μ) _ hsmall
  apply integral_mono_ae (hi n v h hv hvK hh).norm (hu.1 n _ hv' hvK').norm
  filter_upwards [hhT] with s hs
  have hb := ContinuousMap.norm_coe_le_norm (U n (B s (v s))) ⟨h s, hs⟩
  change ‖(Sseq n).action (h s) (B s (v s)) - S.action (h s) (B s (v s))‖ ≤
    ‖U n (B s (v s))‖ at hb
  rw [hDnorm]
  exact hb

variable [CompleteSpace E]

private theorem background_term_path_error
    (Sseq : ℕ → Contraction E) (S : Contraction E) {T : ℝ} (hT : 0 ≤ T)
    (hSlim : ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ h : ℝ, 0 ≤ h → h ≤ T → ‖(Sseq n).action h x - S.action h x‖ < ε)
    (B : ℝ → E →L[ℂ] E)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x)
      (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgpos : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) (m : ℕ) (x : E) :
    (∀ n r t, r ∈ Set.Icc 0 T → IntegrableOn
      (fun s => (Sseq n).action (max (t-s) 0) (B s (term S B m (max s r) r x)) -
        S.action (max (t-s) 0) (B s (term S B m (max s r) r x))) (Set.Icc 0 T)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ r t : ℝ,
      r ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      (∫ s in Set.Icc 0 T,
        ‖(Sseq n).action (max (t-s) 0) (B s (term S B m (max s r) r x)) -
          S.action (max (t-s) 0) (B s (term S B m (max s r) r x))‖) < ε := by
  let f : ℝ × ℝ → E := fun p => term S B m (max p.1 p.2) p.2 x
  have hf : ContinuousOn f ((Set.Icc 0 T) ×ˢ (Set.Icc 0 T)) := by
    apply (term_joint_continuous S B hT hB g hg hgpos hBg m x).comp
      ((continuous_fst.max continuous_snd).prodMk continuous_snd).continuousOn
    intro p hp
    exact ⟨hp.2.1, le_max_right _ _, max_le hp.1.2 hp.2.2⟩
  have hK : IsCompact (f '' ((Set.Icc 0 T) ×ˢ (Set.Icc 0 T))) :=
    (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn hf
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc 0 T)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hgpos s hs
  have hbound : ∀ᵐ s ∂volume.restrict (Set.Icc 0 T), ‖B s‖ ≤ g s := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hBg s hs
  have hu := uniform_integral_background_action Sseq S T hSlim B hB g hg
    hnonneg hbound hK
  have hpath : ∀ r ∈ Set.Icc 0 T,
      AEStronglyMeasurable (fun s => f (s,r)) (volume.restrict (Set.Icc 0 T)) := by
    intro r hr
    exact (hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs,hr⟩)).aestronglyMeasurable measurableSet_Icc
  have hmem : ∀ r ∈ Set.Icc 0 T, ∀ᵐ s ∂volume.restrict (Set.Icc 0 T),
      f (s,r) ∈ f '' ((Set.Icc 0 T) ×ˢ (Set.Icc 0 T)) := by
    intro r hr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ⟨(s,r), ⟨hs,hr⟩, rfl⟩
  have htime : ∀ t : ℝ, AEStronglyMeasurable (fun s => max (t-s) 0)
      (volume.restrict (Set.Icc 0 T)) := fun t =>
    ((continuous_const.sub continuous_id).max continuous_const).aestronglyMeasurable
  constructor
  · intro n r t hr
    exact hu.1 n _ _ (hpath r hr) (hmem r hr) (htime t)
  · intro ε hε
    filter_upwards [hu.2 ε hε] with n hn r t hr ht
    apply hn _ _ (hpath r hr) (hmem r hr) (htime t)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ⟨le_max_right _ _, max_le (by linarith [ht.2, hs.1]) hT⟩

/-- Every original Dyson term converges strongly under varying contraction backgrounds,
uniformly over the full closed ordered time triangle. -/
theorem uniform_term_convergence_of_mass
    (Sseq : ℕ → Contraction E) (S : Contraction E) {T : ℝ} (hT : 0 ≤ T)
    (hSlim : ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ h : ℝ, 0 ≤ h → h ≤ T → ‖(Sseq n).action h x - S.action h x‖ < ε)
    (Bseq : ℕ → ℝ → E →L[ℂ] E) (B : ℝ → E →L[ℂ] E)
    (hseq : ∀ n x, AEStronglyMeasurable (fun s => Bseq n s x)
      (volume.restrict (Set.Icc 0 T)))
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x)
      (volume.restrict (Set.Icc 0 T)))
    (gn : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hgn : ∀ n, IntegrableOn (gn n) (Set.Icc 0 T))
    (hg : IntegrableOn g (Set.Icc 0 T))
    (hgnn : ∀ n, ∀ s ∈ Set.Icc 0 T, 0 ≤ gn n s)
    (hgpos : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hseqg : ∀ n, ∀ s ∈ Set.Icc 0 T, ‖Bseq n s‖ ≤ gn n s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s)
    (C : ℝ) (hC : 0 ≤ C)
    (hseqmass : ∀ n, (∫ s in (0 : ℝ)..T, gn n s) ≤ C)
    (hBmass : (∫ s in (0 : ℝ)..T, g s) ≤ C)
    (hlim : ∀ x, Tendsto (fun n => ∫ s in (0 : ℝ)..T, ‖(Bseq n s - B s) x‖)
      atTop (𝓝 0)) :
    ∀ (m : ℕ) (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ r t : ℝ,
      0 ≤ r → r ≤ t → t ≤ T →
      ‖term (Sseq n) (Bseq n) m t r x - term S B m t r x‖ < ε := by
  intro m x
  have hw : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ r t : ℝ,
      0 ≤ r → r ≤ t → t ≤ T →
      ‖term (Sseq n) (Bseq n) m t r x - term S B m t r x‖ < ε := by
    intro m
    induction m with
    | zero =>
      intro ε hε
      obtain ⟨N,hN⟩ := hSlim x ε hε
      filter_upwards [eventually_ge_atTop N] with n hn r t hr hrt ht
      simpa only [term_zero] using hN n hn (t-r) (sub_nonneg.mpr hrt) (by linarith)
    | succ m ih =>
      intro ε hε
      obtain ⟨η,hη,hηε⟩ := exists_pos_mul_lt (show 0 < ε / 3 by positivity) C
      have he := SeparateMassEvolutionStability.term_path_error S hT Bseq B hseq hB
        gn g hgn hg hgnn hgpos hseqg hBg C hseqmass hBmass hlim m x
      have ha := background_term_path_error Sseq S hT hSlim B hB g hg hgpos hBg m x
      filter_upwards [ih η hη, he.2 (ε/3) (by positivity), ha.2 (ε/3) (by positivity)]
        with n hn hen han
      intro r t hr hrt ht
      have hrT : r ∈ Set.Icc 0 T := ⟨hr,hrt.trans ht⟩
      have htT : t ∈ Set.Icc 0 T := ⟨hr.trans hrt,ht⟩
      let v : ℝ → E := fun s => term S B m (max s r) r x
      let a : ℝ → E := fun s => (Sseq n).action (max (t-s) 0) (B s (v s)) -
        S.action (max (t-s) 0) (B s (v s))
      let b : ℝ → ℝ := fun s =>
        (gn n s * η + ‖(Bseq n s - B s) (v s)‖) + ‖a s‖
      have hai : IntegrableOn a (Set.Icc 0 T) := ha.1 n r t hrT
      have hei : IntegrableOn (fun s => (Bseq n s - B s) (v s)) (Set.Icc 0 T) :=
        he.1 n r hrT
      have hbi : IntegrableOn b (Set.Icc 0 T) :=
        (((hgn n).mul_const η).add hei.norm).add hai.norm
      have hbn : 0 ≤ᵐ[volume.restrict (Set.Icc 0 T)] b := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact add_nonneg (add_nonneg (mul_nonneg (hgnn n s hs) hη.le)
          (norm_nonneg _)) (norm_nonneg _)
      have hbrt := hbi.mono_set (Set.Icc_subset_Icc hr ht)
      have hiseq := term_integrable (Sseq n) (Bseq n) (hrt.trans ht)
        (fun z => (hseq n z).mono_set (Set.Icc_subset_Icc hr le_rfl))
        (gn n) ((hgn n).mono_set (Set.Icc_subset_Icc hr le_rfl))
        (fun s hs => hgnn n s ⟨hr.trans hs.1,hs.2⟩)
        (fun s hs => hseqg n s ⟨hr.trans hs.1,hs.2⟩) m x ⟨hrt,ht⟩
      have hiB := term_integrable S B (hrt.trans ht)
        (fun z => (hB z).mono_set (Set.Icc_subset_Icc hr le_rfl))
        g (hg.mono_set (Set.Icc_subset_Icc hr le_rfl))
        (fun s hs => hgpos s ⟨hr.trans hs.1,hs.2⟩)
        (fun s hs => hBg s ⟨hr.trans hs.1,hs.2⟩) m x ⟨hrt,ht⟩
      rw [term_succ,term_succ, ← intervalIntegral.integral_sub hiseq hiB]
      calc
        _ ≤ ∫ s in r..t, b s := by
          apply intervalIntegral.norm_integral_le_of_norm_le hrt _
            ((intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr hbrt)
          apply Eventually.of_forall
          intro s hs
          have hsT : s ∈ Set.Icc 0 T := ⟨hr.trans hs.1.le,hs.2.trans ht⟩
          have hprev := (hn r s hr hs.1.le hsT.2).le
          have halg :
              (Sseq n).action (t-s) (Bseq n s (term (Sseq n) (Bseq n) m s r x)) -
                S.action (t-s) (B s (term S B m s r x)) =
              (Sseq n).action (t-s)
                (Bseq n s (term (Sseq n) (Bseq n) m s r x - term S B m s r x) +
                  (Bseq n s - B s) (term S B m s r x)) + a s := by
            dsimp [a,v]
            rw [max_eq_left hs.1.le, max_eq_left (sub_nonneg.mpr hs.2)]
            simp only [map_add,map_sub,sub_apply]
            abel
          rw [halg]
          apply (norm_add_le _ _).trans
          apply (add_le_add ((Sseq n).action_bound _ _) (le_refl ‖a s‖)).trans
          apply (add_le_add (norm_add_le _ _) (le_refl ‖a s‖)).trans
          dsimp [b,v]
          rw [max_eq_left hs.1.le]
          exact add_le_add (add_le_add (((Bseq n s).le_opNorm _).trans
            (mul_le_mul (hseqg n s hsT) hprev (norm_nonneg _) (hgnn n s hsT))) le_rfl) le_rfl
        _ ≤ ∫ s in Set.Icc 0 T, b s := by
          rw [intervalIntegral.integral_of_le hrt, ← integral_Icc_eq_integral_Ioc]
          exact setIntegral_mono_set hbi hbn (Eventually.of_forall
            (fun s hs => ⟨hr.trans hs.1,hs.2.trans ht⟩))
        _ = ((∫ s in Set.Icc 0 T, gn n s) * η +
            ∫ s in Set.Icc 0 T, ‖(Bseq n s - B s) (v s)‖) +
            ∫ s in Set.Icc 0 T, ‖a s‖ := by
          calc
            _ = (∫ s in Set.Icc 0 T, gn n s * η +
                ‖(Bseq n s - B s) (v s)‖) + ∫ s in Set.Icc 0 T, ‖a s‖ :=
              integral_add (((hgn n).mul_const η).add hei.norm) hai.norm
            _ = ((∫ s in Set.Icc 0 T, gn n s * η) +
                ∫ s in Set.Icc 0 T, ‖(Bseq n s - B s) (v s)‖) +
                ∫ s in Set.Icc 0 T, ‖a s‖ :=
              congrArg (fun z : ℝ => z + ∫ s in Set.Icc 0 T, ‖a s‖)
                (integral_add ((hgn n).mul_const η) hei.norm)
            _ = _ := by rw [integral_mul_const]
        _ ≤ (C * η + ∫ s in Set.Icc 0 T, ‖(Bseq n s - B s) (v s)‖) +
            ∫ s in Set.Icc 0 T, ‖a s‖ := by
          have hm := hseqmass n
          simp only [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at hm
          gcongr
        _ < ε := by
          have hsmall := hen r hrT
          have hasmall := han r t hrT htT
          change (∫ s in Set.Icc 0 T, ‖a s‖) < ε/3 at hasmall
          change (∫ s in Set.Icc 0 T, ‖(Bseq n s - B s) (v s)‖) < ε/3 at hsmall
          linarith
  intro ε hε
  exact eventually_atTop.mp (hw m ε hε)

/-- Separate coefficient mass bounds and compact-time strong convergence of the backgrounds
imply uniform strong convergence of the original measurable evolutions. -/
theorem measurable_evolution_stability_of_mass
    (Sseq : ℕ → Contraction E) (S : Contraction E) {T : ℝ} (hT : 0 ≤ T)
    (hSlim : ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ h : ℝ, 0 ≤ h → h ≤ T → ‖(Sseq n).action h x - S.action h x‖ < ε)
    (Bseq : ℕ → ℝ → E →L[ℂ] E) (B : ℝ → E →L[ℂ] E)
    (hseq : ∀ n x, AEStronglyMeasurable (fun s => Bseq n s x)
      (volume.restrict (Set.Icc 0 T)))
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x)
      (volume.restrict (Set.Icc 0 T)))
    (gn : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hgn : ∀ n, IntegrableOn (gn n) (Set.Icc 0 T))
    (hg : IntegrableOn g (Set.Icc 0 T))
    (hgnn : ∀ n, ∀ s ∈ Set.Icc 0 T, 0 ≤ gn n s)
    (hgpos : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hseqg : ∀ n, ∀ s ∈ Set.Icc 0 T, ‖Bseq n s‖ ≤ gn n s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s)
    (C : ℝ) (hC : 0 ≤ C)
    (hseqmass : ∀ n, (∫ s in (0 : ℝ)..T, gn n s) ≤ C)
    (hBmass : (∫ s in (0 : ℝ)..T, g s) ≤ C)
    (hlim : ∀ x, Tendsto (fun n => ∫ s in (0 : ℝ)..T, ‖(Bseq n s - B s) x‖)
      atTop (𝓝 0)) :
    ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ r t : ℝ,
      0 ≤ r → r ≤ t → t ≤ T →
      ‖measurableEvolution (Sseq n) (Bseq n) t r x - measurableEvolution S B t r x‖ < ε := by
  classical
  intro x ε hε
  let u : ℕ → ℝ := fun m => C^m / m ! * ‖x‖
  have hu : Summable u := (Real.summable_pow_div_factorial _).mul_right _
  let K : Set (Contraction E × (((ℝ → E →L[ℂ] E) × (ℝ → ℝ)) × (ℝ × ℝ))) := {q |
    (∀ z, AEStronglyMeasurable (fun s => q.2.1.1 s z) (volume.restrict (Set.Icc 0 T))) ∧
    IntegrableOn q.2.1.2 (Set.Icc 0 T) ∧
    (∀ s ∈ Set.Icc 0 T, 0 ≤ q.2.1.2 s) ∧
    (∀ s ∈ Set.Icc 0 T, ‖q.2.1.1 s‖ ≤ q.2.1.2 s) ∧
    (∫ s in (0 : ℝ)..T, q.2.1.2 s) ≤ C ∧ q.2.2 ∈ triangle T}
  have hb : ∀ m q, q ∈ K → ‖term q.1 q.2.1.1 m q.2.2.1 q.2.2.2 x‖ ≤ u m := by
    intro m q hq
    obtain ⟨hQ, hc, hcp, hQc, hmass, hr, hrt, ht⟩ := hq
    apply (term_bound q.1 q.2.1.1 (hrt.trans ht)
      (fun z => (hQ z).mono_set (Set.Icc_subset_Icc hr le_rfl))
      q.2.1.2 (hc.mono_set (Set.Icc_subset_Icc hr le_rfl))
      (fun s hs => hcp s ⟨hr.trans hs.1, hs.2⟩)
      (fun s hs => hQc s ⟨hr.trans hs.1, hs.2⟩) m ⟨hrt, ht⟩ x).trans
    have hn : 0 ≤ ∫ s in q.2.2.2..q.2.2.1, q.2.1.2 s :=
      intervalIntegral.integral_nonneg hrt (fun s hs => hcp s ⟨hr.trans hs.1, hs.2.trans ht⟩)
    have hl : (∫ s in q.2.2.2..q.2.2.1, q.2.1.2 s) ≤ C := by
      apply le_trans (b := ∫ s in (0 : ℝ)..T, q.2.1.2 s) _ hmass
      apply intervalIntegral.integral_mono_interval hr hrt ht _
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hc)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hcp s ⟨hs.1.le, hs.2⟩
    dsimp [u]
    exact mul_le_mul
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hn hl m) (by positivity)) le_rfl
      (norm_nonneg x) (div_nonneg (pow_nonneg hC m) (by positivity))
  have htail := tendstoUniformlyOn_tsum_nat hu hb
  obtain ⟨M, hM⟩ := (Metric.tendstoUniformlyOn_iff.mp htail (ε / 3) (by positivity)).exists
  have hterm : ∀ m, TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => term (Sseq n) (Bseq n) m p.1 p.2 x)
      (fun p => term S B m p.1 p.2 x) atTop (triangle T) := by
    intro m
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro δ hδ
    filter_upwards [eventually_atTop.mpr (uniform_term_convergence_of_mass Sseq S hT hSlim
      Bseq B hseq hB gn g hgn hg hgnn hgpos hseqg hBg C hC hseqmass hBmass hlim m x δ hδ)]
      with n hn p hp
    simpa only [dist_eq_norm, norm_sub_rev] using hn p.2 p.1 hp.1 hp.2.1 hp.2.2
  have hhead : ∀ M : ℕ, TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => ∑ m ∈ Finset.range M, term (Sseq n) (Bseq n) m p.1 p.2 x)
      (fun p => ∑ m ∈ Finset.range M, term S B m p.1 p.2 x) atTop (triangle T) := by
    intro M
    induction M with
    | zero => simpa using (tendsto_const_nhds (x := (0 : E))).tendstoUniformlyOn_const (triangle T)
    | succ M ih => simpa only [Finset.sum_range_succ, Pi.add_def] using ih.add (hterm M)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp (hhead M) (ε / 3) (by positivity))
  refine ⟨N, ?_⟩
  intro n hn r t hr hrt ht
  have hp : (t,r) ∈ triangle T := ⟨hr, hrt, ht⟩
  have hntail := hM (Sseq n, ((Bseq n, gn n), (t,r))) ⟨hseq n, hgn n, hgnn n, hseqg n, hseqmass n, hp⟩
  have hBtail := hM (S, ((B, g), (t,r))) ⟨hB, hg, hgpos, hBg, hBmass, hp⟩
  have hh := hN n hn (t,r) hp
  have happly : ∀ (U : Contraction E) (Q : ℝ → E →L[ℂ] E) (c : ℝ → ℝ),
      (∀ z, AEStronglyMeasurable (fun s => Q s z) (volume.restrict (Set.Icc 0 T))) →
      IntegrableOn c (Set.Icc 0 T) →
      (∀ s ∈ Set.Icc 0 T, 0 ≤ c s) →
      (∀ s ∈ Set.Icc 0 T, ‖Q s‖ ≤ c s) →
      measurableEvolution U Q t r x = sum U Q t r x := by
    intro U Q c hQ hc hcp hQc
    exact measurableEvolution_apply U Q (hrt.trans ht)
      (fun z => (hQ z).mono_set (Set.Icc_subset_Icc hr le_rfl))
      c (hc.mono_set (Set.Icc_subset_Icc hr le_rfl))
      (fun s hs => hcp s ⟨hr.trans hs.1, hs.2⟩)
      (fun s hs => hQc s ⟨hr.trans hs.1, hs.2⟩) ⟨hrt, ht⟩ x
  rw [happly (Sseq n) (Bseq n) (gn n) (hseq n) (hgn n) (hgnn n) (hseqg n),
    happly S B g hB hg hgpos hBg, ← dist_eq_norm]
  let a := ∑ m ∈ Finset.range M, term (Sseq n) (Bseq n) m t r x
  let b := ∑ m ∈ Finset.range M, term S B m t r x
  have han : dist (sum (Sseq n) (Bseq n) t r x) a < ε / 3 := hntail
  have hab : dist a b < ε / 3 := by rw [dist_comm]; exact hh
  have hbB : dist b (sum S B t r x) < ε / 3 := by rw [dist_comm]; exact hBtail
  calc
    _ ≤ dist (sum (Sseq n) (Bseq n) t r x) a + dist a (sum S B t r x) := dist_triangle _ _ _
    _ ≤ dist (sum (Sseq n) (Bseq n) t r x) a + (dist a b + dist b (sum S B t r x)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε := by linarith


end D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability
