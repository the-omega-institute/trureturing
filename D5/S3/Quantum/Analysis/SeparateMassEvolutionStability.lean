/- GID: D5/S3/Quantum/Analysis/SeparateMassEvolutionStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/SeparateMassEvolutionStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separate scalar mass bounds and strong L1 stability of measurable evolution. -/

import D5.S3.Quantum.Analysis.NonautonomousEvolutionStability

/-! # Strong L1 stability under separate scalar mass bounds -/

open scoped Nat Topology
open MeasureTheory Filter
open D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips

namespace D5.S3.Quantum.Analysis.SeparateMassEvolutionStability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open D5.S3.Quantum.Analysis.NonautonomousEvolutionStability

/-- Fixed-vector L1 convergence controls all measurable paths in a compact vector range,
uniformly over the paths. Each evaluated vector function is actually Bochner integrable. -/
theorem uniform_integral_evaluation_of_mass {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (D : ℕ → α → E →L[ℂ] E)
    (hD : ∀ n x, AEStronglyMeasurable (fun s => D n s x) μ)
    {c : ℕ → α → ℝ} (hc : ∀ n, Integrable (c n) μ)
    (hcn : ∀ n, 0 ≤ᵐ[μ] c n)
    (hDc : ∀ n, ∀ᵐ s ∂μ, ‖D n s‖ ≤ c n s)
    (M : ℝ) (hmass : ∀ n, (∫ s, c n s ∂μ) ≤ M)
    (hlim : ∀ x, Tendsto (fun n => ∫ s, ‖D n s x‖ ∂μ) atTop (𝓝 0))
    {K : Set E} (hK : IsCompact K) :
    (∀ n (v : α → E), AEStronglyMeasurable v μ →
      (∀ᵐ s ∂μ, v s ∈ K) → Integrable (fun s => D n s (v s)) μ) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (v : α → E),
      AEStronglyMeasurable v μ → (∀ᵐ s ∂μ, v s ∈ K) →
      (∫ s, ‖D n s (v s)‖ ∂μ) < ε := by
  classical
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun x : E => x) continuousOn_id
  have hi : ∀ n (v : α → E), AEStronglyMeasurable v μ →
      (∀ᵐ s ∂μ, v s ∈ K) → Integrable (fun s => D n s (v s)) μ := by
    intro n v hv hvK
    exact evaluation_integrable_of_bound (D n) (hD n) (hc n) (hcn n) (hDc n) hv C
      (hvK.mono fun s hs => hC _ hs)
  refine ⟨hi, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_mul_lt (half_pos hε) M
  obtain ⟨A, hAK, hAf, hcover⟩ := hK.finite_cover_balls hδ
  let F := hAf.toFinset
  have hfixed : ∀ n x, Integrable (fun s => D n s x) μ := by
    intro n x
    exact evaluation_integrable_of_bound (D n) (hD n) (hc n) (hcn n) (hDc n)
      aestronglyMeasurable_const ‖x‖ (Eventually.of_forall fun _ => le_rfl)
  have hsumlim : Tendsto (fun n => ∑ x ∈ F, ∫ s, ‖D n s x‖ ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum F (fun x _ => hlim x)
  filter_upwards [hsumlim.eventually (gt_mem_nhds (half_pos hε))] with n hn
  intro v hv hvK
  have hsum : Integrable (fun s => ∑ x ∈ F, ‖D n s x‖) μ :=
    integrable_finsetSum F (fun x _ => (hfixed n x).norm)
  have hpoint : ∀ᵐ s ∂μ,
      ‖D n s (v s)‖ ≤ (∑ x ∈ F, ‖D n s x‖) + c n s * δ := by
    filter_upwards [hvK, hcn n, hDc n] with s hvs hcs hDs
    obtain ⟨x, hxA, hx⟩ := Set.mem_iUnion₂.mp (hcover hvs)
    have hxF : x ∈ F := hAf.mem_toFinset.mpr hxA
    have hdist : ‖v s - x‖ ≤ δ := by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hx).le
    calc
      ‖D n s (v s)‖ = ‖D n s (v s - x) + D n s x‖ := by rw [map_sub, sub_add_cancel]
      _ ≤ ‖D n s (v s - x)‖ + ‖D n s x‖ := norm_add_le _ _
      _ ≤ c n s * δ + ‖D n s x‖ := by
        gcongr
        exact ((D n s).le_opNorm _).trans
          (mul_le_mul hDs hdist (norm_nonneg _) hcs)
      _ ≤ (∑ x ∈ F, ‖D n s x‖) + c n s * δ := by
        have hxsum := Finset.single_le_sum (fun y (_ : y ∈ F) => norm_nonneg (D n s y)) hxF
        linarith
  calc
    (∫ s, ‖D n s (v s)‖ ∂μ) ≤
        ∫ s, (∑ x ∈ F, ‖D n s x‖) + c n s * δ ∂μ :=
      integral_mono_ae (hi n v hv hvK).norm (hsum.add ((hc n).mul_const δ)) hpoint
    _ = (∑ x ∈ F, ∫ s, ‖D n s x‖ ∂μ) + (∫ s, c n s ∂μ) * δ := by
      rw [integral_add hsum ((hc n).mul_const δ), integral_finsetSum F
        (fun x _ => (hfixed n x).norm), integral_mul_const]
    _ ≤ (∑ x ∈ F, ∫ s, ‖D n s x‖ ∂μ) + M * δ := by
      gcongr
      exact hmass n
    _ < ε := by linarith

variable [CompleteSpace E]

theorem term_path_error (S : Contraction E) {T : ℝ} (hT : 0 ≤ T)
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
    (C : ℝ)
    (hseqmass : ∀ n, (∫ s in (0 : ℝ)..T, gn n s) ≤ C)
    (hBmass : (∫ s in (0 : ℝ)..T, g s) ≤ C)
    (hlim : ∀ x, Tendsto (fun n => ∫ s in (0 : ℝ)..T, ‖(Bseq n s - B s) x‖)
      atTop (𝓝 0)) (m : ℕ) (x : E) :
    (∀ n r, r ∈ Set.Icc 0 T → IntegrableOn
      (fun s => (Bseq n s - B s) (term S B m (max s r) r x)) (Set.Icc 0 T)) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      (∫ s in Set.Icc 0 T, ‖(Bseq n s - B s) (term S B m (max s r) r x)‖) < ε := by
  let f : ℝ × ℝ → E := fun p => term S B m (max p.1 p.2) p.2 x
  have hf : ContinuousOn f ((Set.Icc 0 T) ×ˢ (Set.Icc 0 T)) := by
    apply (term_joint_continuous S B hT hB g hg hgpos hBg m x).comp
      ((continuous_fst.max continuous_snd).prodMk continuous_snd).continuousOn
    intro p hp
    exact ⟨hp.2.1, le_max_right _ _, max_le hp.1.2 hp.2.2⟩
  have hK : IsCompact (f '' ((Set.Icc 0 T) ×ˢ (Set.Icc 0 T))) :=
    (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn hf
  have hmeas : ∀ n z, AEStronglyMeasurable (fun s => (Bseq n s - B s) z)
      (volume.restrict (Set.Icc 0 T)) := by
    intro n z
    simpa only [sub_apply, Pi.sub_def] using (hseq n z).sub (hB z)
  have hbound : ∀ n, ∀ᵐ s ∂volume.restrict (Set.Icc 0 T),
      ‖Bseq n s - B s‖ ≤ gn n s + g s := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (norm_sub_le _ _).trans (add_le_add (hseqg n s hs) (hBg s hs))
  have hconv : ∀ z, Tendsto (fun n => ∫ s in Set.Icc 0 T, ‖(Bseq n s - B s) z‖)
      atTop (𝓝 0) := by
    intro z
    simpa only [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc] using hlim z
  have hnonneg : ∀ n, 0 ≤ᵐ[volume.restrict (Set.Icc 0 T)] (fun s => gn n s + g s) := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact add_nonneg (hgnn n s hs) (hgpos s hs)
  have hmass : ∀ n, (∫ s in Set.Icc 0 T, gn n s + g s) ≤ C + C := by
    intro n
    rw [integral_add (hgn n) hg]
    have hn := hseqmass n
    have hb := hBmass
    simp only [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at hn hb
    exact add_le_add hn hb
  have hu := uniform_integral_evaluation_of_mass (fun n s => Bseq n s - B s) hmeas
    (fun n => (hgn n).add hg) hnonneg hbound (C+C) hmass hconv hK
  have hpath : ∀ r ∈ Set.Icc 0 T,
      ContinuousOn (fun s => f (s,r)) (Set.Icc 0 T) := by
    intro r hr
    exact hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, hr⟩)
  have hmem : ∀ r ∈ Set.Icc 0 T, ∀ᵐ s ∂volume.restrict (Set.Icc 0 T),
      f (s,r) ∈ f '' ((Set.Icc 0 T) ×ˢ (Set.Icc 0 T)) := by
    intro r hr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ⟨(s,r), ⟨hs,hr⟩, rfl⟩
  constructor
  · intro n r hr
    exact hu.1 n (fun s => f (s,r))
      ((hpath r hr).aestronglyMeasurable measurableSet_Icc) (hmem r hr)
  · intro ε hε
    filter_upwards [hu.2 ε hε] with n hn r hr
    exact hn (fun s => f (s,r))
      ((hpath r hr).aestronglyMeasurable measurableSet_Icc) (hmem r hr)

/-- Every fixed original Dyson term converges strongly, uniformly in both ordered endpoints. -/
theorem uniform_term_convergence_of_mass (S : Contraction E) {T : ℝ} (hT : 0 ≤ T)
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
    (C : ℝ)
    (hseqmass : ∀ n, (∫ s in (0 : ℝ)..T, gn n s) ≤ C)
    (hBmass : (∫ s in (0 : ℝ)..T, g s) ≤ C)
    (hlim : ∀ x, Tendsto (fun n => ∫ s in (0 : ℝ)..T, ‖(Bseq n s - B s) x‖)
      atTop (𝓝 0)) (m : ℕ) (x : E) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ r t : ℝ,
      0 ≤ r → r ≤ t → t ≤ T →
      ‖term S (Bseq n) m t r x - term S B m t r x‖ < ε := by
  induction m with
  | zero =>
    intro ε hε
    exact Eventually.of_forall (fun n r t _ _ _ => by simpa only [term_zero, sub_self, norm_zero])
  | succ m ih =>
    intro ε hε
    obtain ⟨η, hη, hηε⟩ := exists_pos_mul_lt (half_pos hε) C
    have he := term_path_error S hT Bseq B hseq hB gn g hgn hg hgnn hgpos hseqg hBg C
      hseqmass hBmass hlim m x
    filter_upwards [ih η hη, he.2 (ε / 2) (half_pos hε)] with n hn hen
    intro r t hr hrt ht
    have hrT : r ∈ Set.Icc 0 T := ⟨hr, hrt.trans ht⟩
    let v : ℝ → E := fun s => term S B m (max s r) r x
    let b : ℝ → ℝ := fun s => gn n s * η + ‖(Bseq n s - B s) (v s)‖
    have hbi : IntegrableOn b (Set.Icc 0 T) := ((hgn n).mul_const η).add (he.1 n r hrT).norm
    have hbn : 0 ≤ᵐ[volume.restrict (Set.Icc 0 T)] b := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact add_nonneg (mul_nonneg (hgnn n s hs) hη.le) (norm_nonneg _)
    have hbrt := hbi.mono_set (Set.Icc_subset_Icc hr ht)
    have hiseq := term_integrable S (Bseq n) (hrt.trans ht)
      (fun z => (hseq n z).mono_set (Set.Icc_subset_Icc hr le_rfl))
      (gn n) ((hgn n).mono_set (Set.Icc_subset_Icc hr le_rfl))
      (fun s hs => hgnn n s ⟨hr.trans hs.1, hs.2⟩)
      (fun s hs => hseqg n s ⟨hr.trans hs.1, hs.2⟩) m x ⟨hrt, ht⟩
    have hiB := term_integrable S B (hrt.trans ht)
      (fun z => (hB z).mono_set (Set.Icc_subset_Icc hr le_rfl))
      g (hg.mono_set (Set.Icc_subset_Icc hr le_rfl))
      (fun s hs => hgpos s ⟨hr.trans hs.1, hs.2⟩)
      (fun s hs => hBg s ⟨hr.trans hs.1, hs.2⟩) m x ⟨hrt, ht⟩
    rw [term_succ, term_succ, ← intervalIntegral.integral_sub hiseq hiB]
    calc
      _ ≤ ∫ s in r..t, b s := by
        apply intervalIntegral.norm_integral_le_of_norm_le hrt _
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr hbrt)
        apply Eventually.of_forall
        intro s hs
        have hsT : s ∈ Set.Icc 0 T := ⟨hr.trans hs.1.le, hs.2.trans ht⟩
        have hprev := (hn r s hr hs.1.le hsT.2).le
        have halg : Bseq n s (term S (Bseq n) m s r x) - B s (term S B m s r x) =
            Bseq n s (term S (Bseq n) m s r x - term S B m s r x) +
              (Bseq n s - B s) (term S B m s r x) := by
          simp only [map_sub, sub_apply]
          abel
        rw [← map_sub, halg]
        apply (S.action_bound _ _).trans
        apply (norm_add_le _ _).trans
        dsimp [b, v]
        rw [max_eq_left hs.1.le]
        exact add_le_add (((Bseq n s).le_opNorm _).trans
          (mul_le_mul (hseqg n s hsT) hprev (norm_nonneg _) (hgnn n s hsT))) le_rfl
      _ ≤ ∫ s in Set.Icc 0 T, b s := by
        rw [intervalIntegral.integral_of_le hrt, ← integral_Icc_eq_integral_Ioc]
        exact setIntegral_mono_set hbi hbn (Eventually.of_forall
          (fun s hs => ⟨hr.trans hs.1, hs.2.trans ht⟩))
      _ = (∫ s in Set.Icc 0 T, gn n s) * η +
          ∫ s in Set.Icc 0 T, ‖(Bseq n s - B s) (v s)‖ := by
        rw [integral_add ((hgn n).mul_const η) (he.1 n r hrT).norm, integral_mul_const]
      _ ≤ C * η + ∫ s in Set.Icc 0 T, ‖(Bseq n s - B s) (v s)‖ := by
        have hm := hseqmass n
        simp only [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at hm
        gcongr
      _ < ε := by have hsmall := hen r hrT; dsimp [v] at *; linarith

/-- Strong L1 convergence of vectorwise measurable coefficients under separate integrable controls
of uniformly bounded mass implies uniform strong convergence of the same coefficient-indexed
evolution. -/
theorem measurable_evolution_stability_of_mass (S : Contraction E) {T : ℝ} (hT : 0 ≤ T)
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
      ‖measurableEvolution S (Bseq n) t r x - measurableEvolution S B t r x‖ < ε := by
  classical
  intro x ε hε
  let u : ℕ → ℝ := fun m => C^m / m ! * ‖x‖
  have hu : Summable u := (Real.summable_pow_div_factorial _).mul_right _
  let K : Set (((ℝ → E →L[ℂ] E) × (ℝ → ℝ)) × (ℝ × ℝ)) := {q |
    (∀ z, AEStronglyMeasurable (fun s => q.1.1 s z) (volume.restrict (Set.Icc 0 T))) ∧
    IntegrableOn q.1.2 (Set.Icc 0 T) ∧
    (∀ s ∈ Set.Icc 0 T, 0 ≤ q.1.2 s) ∧
    (∀ s ∈ Set.Icc 0 T, ‖q.1.1 s‖ ≤ q.1.2 s) ∧
    (∫ s in (0 : ℝ)..T, q.1.2 s) ≤ C ∧ q.2 ∈ triangle T}
  have hb : ∀ m q, q ∈ K → ‖term S q.1.1 m q.2.1 q.2.2 x‖ ≤ u m := by
    intro m q hq
    obtain ⟨hQ, hc, hcp, hQc, hmass, hr, hrt, ht⟩ := hq
    apply (term_bound S q.1.1 (hrt.trans ht)
      (fun z => (hQ z).mono_set (Set.Icc_subset_Icc hr le_rfl))
      q.1.2 (hc.mono_set (Set.Icc_subset_Icc hr le_rfl))
      (fun s hs => hcp s ⟨hr.trans hs.1, hs.2⟩)
      (fun s hs => hQc s ⟨hr.trans hs.1, hs.2⟩) m ⟨hrt, ht⟩ x).trans
    have hn : 0 ≤ ∫ s in q.2.2..q.2.1, q.1.2 s :=
      intervalIntegral.integral_nonneg hrt (fun s hs => hcp s ⟨hr.trans hs.1, hs.2.trans ht⟩)
    have hl : (∫ s in q.2.2..q.2.1, q.1.2 s) ≤ C := by
      apply le_trans (b := ∫ s in (0 : ℝ)..T, q.1.2 s) _ hmass
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
      (fun n (p : ℝ × ℝ) => term S (Bseq n) m p.1 p.2 x)
      (fun p => term S B m p.1 p.2 x) atTop (triangle T) := by
    intro m
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro δ hδ
    filter_upwards [uniform_term_convergence_of_mass S hT Bseq B hseq hB gn g hgn hg
      hgnn hgpos hseqg hBg C hseqmass hBmass hlim m x δ hδ]
      with n hn p hp
    simpa only [dist_eq_norm, norm_sub_rev] using hn p.2 p.1 hp.1 hp.2.1 hp.2.2
  have hhead : ∀ M : ℕ, TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => ∑ m ∈ Finset.range M, term S (Bseq n) m p.1 p.2 x)
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
  have hntail := hM ((Bseq n, gn n), (t,r)) ⟨hseq n, hgn n, hgnn n, hseqg n, hseqmass n, hp⟩
  have hBtail := hM ((B, g), (t,r)) ⟨hB, hg, hgpos, hBg, hBmass, hp⟩
  have hh := hN n hn (t,r) hp
  have happly : ∀ (Q : ℝ → E →L[ℂ] E) (c : ℝ → ℝ),
      (∀ z, AEStronglyMeasurable (fun s => Q s z) (volume.restrict (Set.Icc 0 T))) →
      IntegrableOn c (Set.Icc 0 T) →
      (∀ s ∈ Set.Icc 0 T, 0 ≤ c s) →
      (∀ s ∈ Set.Icc 0 T, ‖Q s‖ ≤ c s) →
      measurableEvolution S Q t r x = sum S Q t r x := by
    intro Q c hQ hc hcp hQc
    exact measurableEvolution_apply S Q (hrt.trans ht)
      (fun z => (hQ z).mono_set (Set.Icc_subset_Icc hr le_rfl))
      c (hc.mono_set (Set.Icc_subset_Icc hr le_rfl))
      (fun s hs => hcp s ⟨hr.trans hs.1, hs.2⟩)
      (fun s hs => hQc s ⟨hr.trans hs.1, hs.2⟩) ⟨hrt, ht⟩ x
  rw [happly (Bseq n) (gn n) (hseq n) (hgn n) (hgnn n) (hseqg n),
    happly B g hB hg hgpos hBg, ← dist_eq_norm]
  let a := ∑ m ∈ Finset.range M, term S (Bseq n) m t r x
  let b := ∑ m ∈ Finset.range M, term S B m t r x
  have han : dist (sum S (Bseq n) t r x) a < ε / 3 := hntail
  have hab : dist a b < ε / 3 := by rw [dist_comm]; exact hh
  have hbB : dist b (sum S B t r x) < ε / 3 := by rw [dist_comm]; exact hBtail
  calc
    _ ≤ dist (sum S (Bseq n) t r x) a + dist a (sum S B t r x) := dist_triangle _ _ _
    _ ≤ dist (sum S (Bseq n) t r x) a + (dist a b + dist b (sum S B t r x)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε := by linarith

end D5.S3.Quantum.Analysis.SeparateMassEvolutionStability
