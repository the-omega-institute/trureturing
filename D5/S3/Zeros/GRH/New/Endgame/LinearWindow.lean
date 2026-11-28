/- GID: D5/S3/Zeros/GRH/New/Endgame/LinearWindow
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Endgame/LinearWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polar errors have a uniformly good second scale in a fixed linear window. -/

import D5.S3.Zeros.GRH.New.Endgame.OneSidedCriterion
import OmegaMath.Analysis.LinearMomentWindow

set_option autoImplicit false

open Filter Real Set Topology

/-- The signed moment bounds for polar errors yield a linear second-scale window,
uniformly over coefficients between zero and the exponential of the initial scale. -/
lemma IsPolar.exists_linear_window_sub_mul_le {E r E' r'} (h : IsPolar E r)
    (h' : IsPolar E' r') :
    ∃ C : ℝ, 1 < C ∧ ∀ᶠ t in atTop,
      ∀ X ∈ Icc 0 t.exp, ∃ u ∈ Icc t (C * t), E u - X * E' u ≤ (-t).exp := by
  obtain ⟨R, c, d, p, q⟩ := (h.eventually_moment_le.and
    (h'.eventually_moment_le.and (Ioo_mem_nhdsGT (by norm_num : (3 : ℝ) < 4)))).exists
  exact Omega.Analysis.exists_linear_window_of_signed_moments ⟨R, ⟨p, q⟩, c, d⟩
