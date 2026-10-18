/- GID: D5/S3/Entropy/RenyiCombining/CachinConvexCertificate
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/CachinConvexCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive-parameter Riccati certificate for convex Renyi combining. -/

import D5.S3.Entropy.RenyiCombining.CachinConvexLocal
import D5.S3.Entropy.RenyiCombining.CachinConvexTransport

/-! This module proves global differential inequalities for a real parameter
interval; its declarations are not finite numerical verification. -/

open Set Filter
open scoped Topology

namespace D5.S3.Entropy.RenyiCombining.CachinConvexCertificate

open CachinConvexBranch CachinConvexTransport

theorem C_secondDeriv_neg (n : ℝ) (hn : 0 < n) (hn' : n ≤ 1 / 4) :
    ∀ z ∈ Ioo 0 1, deriv (deriv (C n)) z < 0 := by
  have hc : ContDiffOn ℝ 3 (C n) (Ioo 0 1) := fun z hz =>
    (C_contDiffAt n z hn hz).contDiffWithinAt
  have hc₁ : ContDiffOn ℝ 2 (deriv (C n)) (Ioo 0 1) :=
    hc.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hc₂ : ContDiffOn ℝ 1 (deriv (deriv (C n))) (Ioo 0 1) :=
    hc₁.deriv_of_isOpen isOpen_Ioo (by norm_num)
  apply riccati_curvature_neg_of_local (C n) (deriv (C n))
    (deriv (deriv (C n))) (deriv (deriv (deriv (C n)))) hc₁.continuousOn hc₂.continuousOn
  · intro z hz
    exact ((hc₁.differentiableOn (by norm_num)) z hz).differentiableAt
      (Ioo_mem_nhds hz.1 hz.2) |>.hasDerivAt
  · intro z hz
    exact ((hc₂.differentiableOn (by norm_num)) z hz).differentiableAt
      (Ioo_mem_nhds hz.1 hz.2) |>.hasDerivAt
  · obtain ⟨δ, hδ, hsign⟩ :=
      CachinConvexLocal.C_local_signs n hn hn'
    refine ⟨δ, hδ, ?_⟩
    intro z hz
    exact ⟨(hsign z hz).1.trans (by linarith), (hsign z hz).2⟩
  · exact C_curvature_equation n hn

theorem D_hasDerivAt (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) :
    HasDerivAt (D n) (D₁ n z) z := by
  have hd := ((C_hasDerivAt n z hn hz).differentiableAt.hasDerivAt).add
    ((hasDerivAt_id z).const_mul n)
  convert hd using 1 <;> (try ext w) <;> (try dsimp [D, D₁]) <;> ring

theorem D1_hasDerivAt (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) :
    HasDerivAt (D₁ n) (deriv (deriv (C n)) z) z := by
  have hc : ContDiffOn ℝ 2 (C n) (Ioo 0 1) := fun z hz =>
    (C_contDiffAt n z hn hz).contDiffWithinAt
  have hc₁ : ContDiffOn ℝ 1 (deriv (C n)) (Ioo 0 1) :=
    hc.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd : HasDerivAt (deriv (C n)) (deriv (deriv (C n)) z) z :=
    ((hc₁.differentiableOn (by norm_num)) z hz).differentiableAt
      (Ioo_mem_nhds hz.1 hz.2) |>.hasDerivAt
  convert! hd.add_const n using 1 <;> rfl

theorem D1_neg (n : ℝ) (hn : 0 < n) (hn' : n ≤ 1 / 4) :
    ∀ z ∈ Ioo 0 1, D₁ n z < 0 := by
  have hm : StrictAntiOn (D₁ n) (Ioo 0 1) :=
    strictAntiOn_of_deriv_neg (convex_Ioo _ _)
      (fun z hz => (D1_hasDerivAt n z hn hz).continuousAt.continuousWithinAt) (by
        intro z hz
        have hz' : z ∈ Ioo 0 1 := by simpa using hz
        rw [(D1_hasDerivAt n z hn hz').deriv]
        exact C_secondDeriv_neg n hn hn' z hz')
  obtain ⟨δ, hδ, hsign⟩ :=
    CachinConvexLocal.C_local_signs n hn hn'
  intro z hz
  let l := min (z / 2) (δ / 2)
  have hl : 0 < l := lt_min (by linarith [hz.1]) (by linarith)
  have hlz : l < z := (min_le_left _ _).trans_lt (by linarith [hz.1])
  have hlδ : l < δ := (min_le_right _ _).trans_lt (by linarith)
  have hlocal : D₁ n l < 0 := by
    unfold D₁
    linarith [(hsign l ⟨hl, hlδ⟩).1]
  exact (hm ⟨hl, hlz.trans hz.2⟩ hz hlz).trans hlocal

theorem elasticity_strictMonoOn (n : ℝ) (hn : 0 < n) (hn' : n ≤ 1 / 4) :
    StrictMonoOn (elasticity (D n) (D₁ n)) (Ioo 0 1) := by
  apply CachinConvexBranch.elasticity_strictMonoOn (D n) (D₁ n)
    (deriv (deriv (C n))) 0 1
  · intro z hz
    exact ⟨hz.1, D_pos n z hn hz⟩
  · exact fun z hz => D_hasDerivAt n z hn hz
  · exact fun z hz => D1_hasDerivAt n z hn hz
  · exact D1_neg n hn hn'
  · exact C_secondDeriv_neg n hn hn'

/-- The required elasticity monotonicity on the positive convex branch. -/
theorem antitoneOn_F (n : ℝ) (hn : 0 < n) (hn' : n ≤ 1 / 4) :
    AntitoneOn (CachinElasticityMonotone.F n) (Ioo 0 1) := by
  intro r hr s hs hrs
  rw [F_eq_denominator_elasticity n s hn hs, F_eq_denominator_elasticity n r hn hr]
  have htr := bias_mem r hr
  have hts := bias_mem s hs
  have htsr : (1 - s) / (1 + s) ≤ (1 - r) / (1 + r) := by
    apply (div_le_div_iff₀ (by linarith [hs.1]) (by linarith [hr.1])).mpr
    nlinarith
  apply (elasticity_strictMonoOn n hn hn').monotoneOn
    ⟨sq_pos_of_pos hts.1, by nlinarith [hts.1, hts.2]⟩
    ⟨sq_pos_of_pos htr.1, by nlinarith [htr.1, htr.2]⟩
  nlinarith [htr.1, hts.1]

end D5.S3.Entropy.RenyiCombining.CachinConvexCertificate
