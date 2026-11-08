/- GID: D5/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/RationalIntervalPhaseMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One fixed phase-memory map on the full closed interval pseudo-orbit domain. -/

import D5.S1.Dynamics.Shadowing.RationalIntervalRetraction

/-! The memory is the actual error at time minus one, on the unchanged closed domain. -/

open Set Filter
open scoped Topology

namespace D5.S1.Dynamics.Shadowing.RationalInterval

/-- The rational action commutes with every positive and negative iterate of `f`. -/
theorem action_commutes (c : ℝ) (hc : 0 < c) (k : ℤ) (u : I) :
    (f ^ k) (action c hc u) = action c hc ((f ^ k) u) := by
  rw [f_zpow]
  change action ((2 : ℝ) ^ k) (by positivity) (action c hc u) =
    action c hc (action ((2 : ℝ) ^ k) (by positivity) u)
  rw [action_mul, action_mul]
  congr 1
  exact mul_comm _ _

/-- Exact displacement for a nonnegative phase-memory error. -/
theorem action_displacement (e : ℝ) (he : 0 ≤ e) (u : I) :
    (action (1 + e) (by linarith) u : ℝ) - u =
      e * (u : ℝ) * (1 - u) / (1 + e * u) := by
  have hu := u.property.1
  have hd : 0 < 1 + e * (u : ℝ) := by positivity
  rw [action_coe]
  have hden : 1 - (u : ℝ) + (1 + e) * u = 1 + e * u := by ring
  rw [hden]
  field_simp
  ring

/-- The uniform quarter-error estimate includes both interval endpoints. -/
theorem action_displacement_le (e : ℝ) (he : 0 ≤ e) (u : I) :
    dist (action (1 + e) (by linarith) u) u ≤ e / 4 := by
  rw [Subtype.dist_eq, Real.dist_eq, action_displacement e he]
  have hn : 0 ≤ e * (u : ℝ) * (1 - u) :=
    mul_nonneg (mul_nonneg he u.property.1) (sub_nonneg.mpr u.property.2)
  have hu := u.property.1
  have hd : 0 < 1 + e * (u : ℝ) := by positivity
  rw [abs_of_nonneg (div_nonneg hn hd.le)]
  apply (div_le_iff₀ hd).mpr
  have hquad : (u : ℝ) * (1 - u) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * (u : ℝ) - 1)]
  have hb := mul_le_mul_of_nonneg_left hquad he
  have hp := mul_nonneg he (mul_nonneg he u.property.1)
  nlinarith

/-- The single origin memory used by `T`, independent of all requested accuracies. -/
noncomputable def memory (x : P) : ℝ := CompactSelector.linkError f x.1 (-1)

private theorem memory_nonneg (x : P) : 0 ≤ memory x := dist_nonneg

private theorem continuous_memory : Continuous memory := by
  unfold memory CompactSelector.linkError
  exact ((continuous_apply _).comp continuous_subtype_val).dist
    (f.continuous.comp ((continuous_apply _).comp continuous_subtype_val))

/-- One fixed map, with the completed explicit finite-marker `R` as its consumer. -/
noncomputable def T (x : P) : I := action (1 + memory x) (by linarith [memory_nonneg x]) (R x)

/-- Joint action continuity and continuity of the actual memory and retraction. -/
theorem continuous_T : Continuous T :=
  continuous_action.comp (((continuous_const.add continuous_memory).subtype_mk
    (fun x => by dsimp; linarith [memory_nonneg x])).prodMk continuous_R)

/-- Every true orbit, including both endpoints, is fixed by this same `T`. -/
theorem T_trueOrbit (p : I) :
    T (CompactSelector.trueOrbit f (by norm_num : (0 : ℝ) ≤ 1 / 256) p) = p := by
  have hm : memory (CompactSelector.trueOrbit f (by norm_num) p) = 0 := by
    change dist (CompactSelector.orbit f p 0) (f (CompactSelector.orbit f p (-1))) = 0
    have hs := CompactSelector.orbit_step f p (-1)
    norm_num only [neg_add_cancel] at hs
    rw [← hs, dist_self]
  simp [T, hm, R_trueOrbit]

/-- All integer iterates preserve the original, fixed memory parameter. -/
theorem T_iterate (x : P) (k : ℤ) :
    (f ^ k) (T x) = action (1 + memory x) (by linarith [memory_nonneg x]) ((f ^ k) (R x)) :=
  action_commutes _ _ _ _

private theorem memory_inclusion_le {γ : ℝ} (hγ : γ ≤ (1 / 256 : ℝ))
    (x : CompactSelector.Space f γ) : memory (CompactSelector.inclusion f hγ x) ≤ γ :=
  x.2 (-1)

/-- The actual all-integer shadowing-map defect on every smaller closed domain. -/
theorem T_shadowing_defect {γ : ℝ} (hγ : γ ≤ (1 / 256 : ℝ))
    (x : CompactSelector.Space f γ) (k : ℤ) :
    dist ((f ^ k) (T (CompactSelector.inclusion f hγ x)))
      (T (CompactSelector.shift f k (CompactSelector.inclusion f hγ x))) ≤ γ / 2 := by
  let y := CompactSelector.inclusion f hγ x
  have hm := memory_inclusion_le hγ x
  have hs : memory (CompactSelector.shift f k y) ≤ γ := by
    simpa only [y, CompactSelector.inclusion, ContinuousMap.coe_mk, memory,
      CompactSelector.linkError, CompactSelector.shift_apply,
      add_assoc] using x.2 (k + -1)
  calc
    dist ((f ^ k) (T y)) (T (CompactSelector.shift f k y)) ≤
        dist ((f ^ k) (T y)) ((f ^ k) (R y)) +
          dist ((f ^ k) (R y)) (T (CompactSelector.shift f k y)) := dist_triangle _ _ _
    _ ≤ memory y / 4 + memory (CompactSelector.shift f k y) / 4 := by
      apply add_le_add
      · rw [T_iterate]
        exact action_displacement_le _ (memory_nonneg y) _
      · rw [← R_shift, dist_comm]
        exact action_displacement_le _ (memory_nonneg _) _
    _ ≤ γ / 2 := by linarith

/-- Literal Definition 3.1, with one fixed map and every integer time. -/
theorem T_shadowing_map :
    Continuous T ∧
    (∀ p : I, T (CompactSelector.trueOrbit f (by norm_num) p) = p) ∧
    (∀ ε > 0, ∃ γ > 0, ∃ hγδ : γ ≤ (1 / 256 : ℝ),
      ∀ (x : CompactSelector.Space f γ) (k : ℤ),
        dist ((f ^ k) (T (CompactSelector.inclusion f hγδ x)))
          (T (CompactSelector.shift f k (CompactSelector.inclusion f hγδ x))) ≤ ε) := by
  refine ⟨continuous_T, T_trueOrbit, ?_⟩
  intro ε hε
  refine ⟨min (1 / 256) (2 * ε), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro x k
  exact (T_shadowing_defect _ x k).trans (by have := min_le_right (1 / 256 : ℝ) (2 * ε); linarith)

/-- Uniform global tracing uses the existing `R` estimate and the quarter-error bound. -/
theorem T_global_shadowing :
    ∀ ε > 0, ∃ γ > 0, ∃ hγδ : γ ≤ (1 / 256 : ℝ),
      ∀ (x : CompactSelector.Space f γ) (k : ℤ),
        dist ((f ^ k) (T (CompactSelector.inclusion f hγδ x))) (x.1 k) < ε := by
  intro ε hε
  obtain ⟨g, hg, hgd, hR⟩ := R_global_and_limit_shadowing.1 (ε / 2) (by positivity)
  let γ := min g (2 * ε)
  have hγg : γ ≤ g := min_le_left _ _
  have hγd : γ ≤ (1 / 256 : ℝ) := hγg.trans hgd
  refine ⟨γ, lt_min hg (by positivity), hγd, fun x k => ?_⟩
  have hr := hR (CompactSelector.inclusion f hγg x) k
  have hm := memory_inclusion_le hγd x
  have hp := action_displacement_le _ (memory_nonneg (CompactSelector.inclusion f hγd x))
    ((f ^ k) (R (CompactSelector.inclusion f hγd x)))
  rw [← T_iterate] at hp
  have heq : CompactSelector.inclusion f hgd (CompactSelector.inclusion f hγg x) =
      CompactSelector.inclusion f hγd x := rfl
  rw [heq] at hr
  change dist ((f ^ k) (R (CompactSelector.inclusion f hγd x))) (x.1 k) < ε / 2 at hr
  have htri := dist_triangle ((f ^ k) (T (CompactSelector.inclusion f hγd x)))
    ((f ^ k) (R (CompactSelector.inclusion f hγd x))) (x.1 k)
  have hγε : γ ≤ 2 * ε := min_le_right _ _
  linarith

private theorem cofinite_limit_of_signed_naturals {a : ℤ → ℝ} {l : ℝ}
    (hp : Tendsto (fun n : ℕ => a n) atTop (𝓝 l))
    (hn : Tendsto (fun n : ℕ => a (-(n : ℤ))) atTop (𝓝 l)) :
    Tendsto a cofinite (𝓝 l) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hp) ε hε)
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hn) ε hε)
  apply eventually_cofinite.mpr
  apply (Set.finite_Icc (-((max N M : ℕ) : ℤ)) ((max N M : ℕ) : ℤ)).subset
  intro k hk
  by_contra hb
  have hlarge : max N M ≤ k.natAbs := by
    have h₁ := Int.le_natAbs (a := k)
    have h₂ := Int.le_natAbs (a := -k)
    simp only [Int.natAbs_neg] at h₂
    simp only [Set.mem_Icc] at hb
    omega
  rcases le_total 0 k with h | h
  · have heq : (k.natAbs : ℤ) = k := by
      simpa only [abs_of_nonneg h] using Int.natCast_natAbs k
    exact hk (by simpa only [heq] using hN k.natAbs ((le_max_left N M).trans hlarge))
  · have heq : -(k.natAbs : ℤ) = k := by omega
    exact hk (by simpa only [heq] using hM k.natAbs ((le_max_right N M).trans hlarge))

/-- Every fixed positive phase perturbation disappears at both orbit tails,
including the two fixed endpoint orbits. No uniformity over base points is assumed. -/
theorem action_orbit_displacement_tendsto (c : ℝ) (hc : 0 < c) (p : I) :
    Tendsto (fun k : ℤ => dist (action c hc ((f ^ k) p)) ((f ^ k) p)) cofinite (𝓝 0) := by
  have hcont : Continuous (fun u : I => dist (action c hc u) u) :=
    (homeomorph c hc).continuous.dist continuous_id
  apply cofinite_limit_of_signed_naturals
  · rcases eq_or_lt_of_le p.property.1 with hp | hp
    · have heq : p = ⟨0, by norm_num⟩ := Subtype.ext hp.symm
      subst p
      simpa only [f_zpow, homeomorph_apply, action_zero, dist_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have ht : Tendsto (fun n : ℕ => (f ^ (n : ℤ)) p) atTop (𝓝 (⟨1, by norm_num⟩ : I)) :=
        tendsto_subtype_rng.mpr (orbit_pos_tendsto p hp)
      simpa only [Function.comp_def, action_top, dist_self] using hcont.continuousAt.tendsto.comp ht
  · rcases lt_or_eq_of_le p.property.2 with hp | hp
    · have ht : Tendsto (fun n : ℕ => (f ^ (-(n : ℤ))) p) atTop (𝓝 (⟨0, by norm_num⟩ : I)) :=
        tendsto_subtype_rng.mpr (orbit_neg_tendsto p hp)
      simpa only [Function.comp_def, action_zero, dist_self] using
        hcont.continuousAt.tendsto.comp ht
    · have heq : p = ⟨1, by norm_num⟩ := Subtype.ext hp
      subst p
      simpa only [f_zpow, homeomorph_apply, action_top, dist_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Full-domain limit tracing for arbitrary two-sided vanishing errors;
infinitely many nonzero errors are allowed. -/
theorem T_limit_shadowing (x : P)
    (hx : Tendsto (CompactSelector.linkError f x.1) cofinite (𝓝 0)) :
    Tendsto (fun k : ℤ => dist ((f ^ k) (T x)) (x.1 k)) cofinite (𝓝 0) := by
  have hp := action_orbit_displacement_tendsto (1 + memory x)
    (by linarith [memory_nonneg x]) (R x)
  simp only [← T_iterate] at hp
  have hr := (R_global_and_limit_shadowing.2 x hx).2
  have hu := hp.add hr
  simp only [add_zero] at hu
  exact squeeze_zero (fun _ => dist_nonneg) (fun k => dist_triangle _ _ _) hu

/-- Literal Definition 4.5: the same output globally traces and two-sided limit
traces every admitted limit pseudo-orbit, at a scale depending only on accuracy. -/
theorem T_L_shadowing_map :
    Continuous T ∧
    (∀ p : I, T (CompactSelector.trueOrbit f (by norm_num) p) = p) ∧
    (∀ ε > 0, ∃ γ > 0, ∃ hγδ : γ ≤ (1 / 256 : ℝ),
      ∀ x : CompactSelector.Space f γ,
        Tendsto (CompactSelector.linkError f x.1) cofinite (𝓝 0) →
        (∀ k : ℤ, dist ((f ^ k) (T (CompactSelector.inclusion f hγδ x))) (x.1 k) < ε) ∧
        Tendsto (fun k : ℤ => dist ((f ^ k) (T (CompactSelector.inclusion f hγδ x)))
          (x.1 k)) cofinite (𝓝 0)) := by
  refine ⟨continuous_T, T_trueOrbit, ?_⟩
  intro ε hε
  obtain ⟨γ, hγ, hγδ, hglobal⟩ := T_global_shadowing ε hε
  exact ⟨γ, hγ, hγδ, fun x hx => ⟨hglobal x, T_limit_shadowing _ hx⟩⟩

#print axioms T_shadowing_map
#print axioms T_L_shadowing_map
#print axioms T_limit_shadowing

end D5.S1.Dynamics.Shadowing.RationalInterval
