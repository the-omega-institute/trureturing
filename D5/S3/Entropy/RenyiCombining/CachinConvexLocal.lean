/- GID: D5/S3/Entropy/RenyiCombining/CachinConvexLocal
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/CachinConvexLocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Analytic finite jets give local signs for the Renyi Riccati quotient. -/

import D5.S3.Entropy.RenyiCombining.CachinConvexInitial
import D5.S3.Entropy.RenyiCombining.CachinConvexLimits
import D5.S3.Entropy.RenyiCombining.CachinConvexBranch

open Set Filter
open scoped Topology

namespace D5.S3.Entropy.RenyiCombining.CachinConvexLocal

open CachinConvexInitial CachinConvexLimits

private theorem C_eq_Q_sqrt (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) :
    CachinConvexBranch.C n z = Q n (Real.sqrt z) := by
  have ht : Real.sqrt z ∈ Ioo 0 1 :=
    ⟨Real.sqrt_pos.mpr hz.1, (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hz.2)⟩
  have h := CachinConvexBranch.C_eq_power_quotient n (Real.sqrt z) hn ht
  rw [Real.sq_sqrt hz.1.le] at h
  exact h.trans (Q_eq ht.1.ne').symm

theorem C_local_signs (n : ℝ) (hn : 0 < n) (hn' : n ≤ 1 / 4) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Ioo 0 δ,
      deriv (CachinConvexBranch.C n) z < -n ∧
      deriv (deriv (CachinConvexBranch.C n)) z < 0 := by
  obtain ⟨a, ha, hd, hcont⟩ := Q_local_derivatives hn.ne'
  obtain ⟨h1, h2, h3, h4⟩ := Q_jets hn.ne'
  have hbound : iteratedDeriv 2 (Q n) 0 < 2 * (-n) := by
    rw [h2]
    have h := CachinConvexBranch.initial_slope_bound n (by linarith) hn'
    linarith
  have hfour : iteratedDeriv 4 (Q n) 0 < 0 := by
    rw [h4]
    have hs : n ^ (2 : ℕ) < 1 := by nlinarith
    have hp : 0 < (1 - n ^ (2 : ℕ)) * (4 - n ^ (2 : ℕ)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  obtain ⟨b, hb, hsign⟩ := exists_sqrt_jet_negative ha (-n)
    (fun t ht => by simpa using hd t ht 1)
    (fun t ht => by simpa using hd t ht 2)
    (fun t ht => by simpa using hd t ht 3) h1 h3 hbound hcont hfour
  let c := min (a ^ (2 : ℕ)) 1
  have hc : 0 < c := lt_min (sq_pos_of_pos ha) (by norm_num)
  have hroot : ∀ z ∈ Ioo 0 c, Real.sqrt z ∈ Icc 0 a := by
    intro z hz
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    exact ((Real.sqrt_lt' ha).mpr (hz.2.trans_le (min_le_left _ _))).le
  have hCE : EqOn (CachinConvexBranch.C n) (fun z => Q n (Real.sqrt z)) (Ioo 0 c) := by
    intro z hz
    exact C_eq_Q_sqrt n z hn ⟨hz.1, hz.2.trans_le (min_le_right _ _)⟩
  have hfirst : EqOn (deriv (CachinConvexBranch.C n))
      (sqrtSlope (iteratedDeriv 1 (Q n))) (Ioo 0 c) := by
    intro z hz
    have he : CachinConvexBranch.C n =ᶠ[𝓝 z] (fun w => Q n (Real.sqrt w)) :=
      hCE.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hz)
    have hQ : HasDerivAt (Q n) (iteratedDeriv 1 (Q n) (Real.sqrt z)) (Real.sqrt z) := by
      simpa using hd (Real.sqrt z) (hroot z hz) 0
    exact ((sqrt_comp_hasDerivAt hz.1 hQ).congr_of_eventuallyEq he).deriv
  have hsecond : ∀ z ∈ Ioo 0 c,
      deriv (deriv (CachinConvexBranch.C n)) z =
        sqrtCurvature (iteratedDeriv 1 (Q n)) (iteratedDeriv 2 (Q n)) z := by
    intro z hz
    have he : deriv (CachinConvexBranch.C n) =ᶠ[𝓝 z]
        sqrtSlope (iteratedDeriv 1 (Q n)) :=
      hfirst.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hz)
    have hQ := hd (Real.sqrt z) (hroot z hz) 1
    exact ((sqrtSlope_hasDerivAt hz.1 hQ).congr_of_eventuallyEq he).deriv
  refine ⟨min b c, lt_min hb hc, ?_⟩
  intro z hz
  have hzb : z ∈ Ioo 0 b := ⟨hz.1, hz.2.trans_le (min_le_left _ _)⟩
  have hzc : z ∈ Ioo 0 c := ⟨hz.1, hz.2.trans_le (min_le_right _ _)⟩
  rw [hfirst hzc, hsecond z hzc]
  exact hsign z hzb

end D5.S3.Entropy.RenyiCombining.CachinConvexLocal
