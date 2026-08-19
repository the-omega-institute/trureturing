/- GID: D5/S0/Tower/DBonacciSurvivors/FiniteDepth
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciSurvivors/FiniteDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite strict d-bonacci backward-survivor depth is nonempty. -/

import D5.S0.Tower.DBonacciSurvivors.DBonacciPermanentSurvivors

/- Library-search audit trail (2026-08-18):
   * Repository search found the strict permanent sets proved empty for orders
     four and five, the boundary champion identities, and the Perron-root
     bounds, but no statement about individual finite depths at general order.
   * The order-two and order-three towers carry their own state types and were
     settled in their own modules; this module neither imports nor replaces
     them.  Its hypothesis is `3 ≤ d`, so order two is outside its range, and
     the order-three instance here is a separate statement about `State 3`
     rather than a restatement of the Tribonacci module.
   * Emptiness of the all-depth intersection does not decide any finite level:
     the levels are open sets, so the nested intersection may be empty while
     every level is nonempty.
   * Pinned Mathlib supplies `pow_pos`, `one_le_pow₀`, and ordered-field
     lemmas; no external theorem specializes to this piecewise map. -/

namespace D5.S0.Tower.DBonacciSurvivors.FiniteDepth

open D5.S0.Tower.DBonacciSurvivors.DBonacciPermanentSurvivors

/-- The large phase of the boundary period-two champion orbit. -/
noncomputable def championTop (d : Nat) : Real := beta d / (beta d ^ 2 - 1)

/-- The predecessor phase of the same orbit. -/
noncomputable def championMid (d : Nat) : Real := 1 / (beta d ^ 2 - 1)

/-- The uniform perturbation budget: membership slack and branch slack, whichever
is tighter. -/
noncomputable def perturbationBudget (d : Nat) : Real :=
  min (championMid d - threshold d) (championTop d - (beta d)⁻¹)

theorem beta_lt_two (d : Nat) (hd : 2 ≤ d) : beta d < 2 :=
  D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_lt_two d hd

theorem beta_pos (d : Nat) (hd : 2 ≤ d) : 0 < beta d :=
  lt_trans zero_lt_one (beta_one_lt d hd)

theorem champion_top_eq (d : Nat) (hd : 2 ≤ d) :
    championTop d = 1 - threshold d := (one_sub_threshold d hd).symm

theorem threshold_eq (d : Nat) (hd : 2 ≤ d) :
    threshold d = 1 - beta d / (beta d ^ 2 - 1) := by
  have := one_sub_threshold d hd; linarith

/-- The two closure identities of the champion orbit.  They hold for any base
with `beta d ^ 2 ≠ 1`, so they carry no order-specific content. -/
theorem champion_step_top (d : Nat) (hd : 2 ≤ d) :
    beta d * championTop d - 1 = championMid d := by
  have hden : beta d ^ 2 - 1 ≠ 0 := ne_of_gt (denominator_pos d hd)
  simp only [championTop, championMid]
  field_simp
  ring

theorem champion_step_mid (d : Nat) (hd : 2 ≤ d) :
    beta d * championMid d = championTop d := by
  have hden : beta d ^ 2 - 1 ≠ 0 := ne_of_gt (denominator_pos d hd)
  simp only [championTop, championMid]
  field_simp

/-- The pivot: the threshold stays below the predecessor phase exactly because
every d-bonacci Perron root is below two. -/
theorem threshold_lt_champion_mid (d : Nat) (hd : 2 ≤ d) :
    threshold d < championMid d := by
  have hden := denominator_pos d hd
  have hlt := beta_lt_two d hd
  have hgt := beta_one_lt d hd
  have hsum : 1 / (beta d ^ 2 - 1) + beta d / (beta d ^ 2 - 1)
      = (1 + beta d) / (beta d ^ 2 - 1) := by field_simp
  rw [threshold_eq d hd, championMid, sub_lt_iff_lt_add, hsum, lt_div_iff₀ hden]
  nlinarith

/-- The branch slack is unconditionally positive. -/
theorem champion_top_gt_inverse (d : Nat) (hd : 2 ≤ d) :
    (beta d)⁻¹ < championTop d := by
  have hden := denominator_pos d hd
  have hbpos := beta_pos d hd
  rw [championTop, inv_eq_one_div, div_lt_div_iff₀ hbpos hden]
  nlinarith

theorem perturbation_budget_pos (d : Nat) (hd : 2 ≤ d) :
    0 < perturbationBudget d := by
  rw [perturbationBudget, lt_min_iff]
  exact ⟨by linarith [threshold_lt_champion_mid d hd],
    by linarith [champion_top_gt_inverse d hd]⟩

/-- Above order two the Perron root exceeds the golden ratio. -/
theorem golden_lt_beta (d : Nat) (hd : 3 ≤ d) : Real.goldenRatio < beta d := by
  have hmono := D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_strictMonoOn
    (a := 2) (b := d) (by simp) (by simp; omega) (by omega)
  rwa [D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_two_eq_goldenRatio] at hmono

/-- The common core of the remaining bounds. -/
theorem beta_sq_sub_beta_sub_one_pos (d : Nat) (hd : 3 ≤ d) :
    0 < beta d ^ 2 - beta d - 1 := by
  have hg := golden_lt_beta d hd
  have hsq := Real.goldenRatio_sq
  have hone := Real.one_lt_goldenRatio
  nlinarith

theorem champion_mid_le_inverse (d : Nat) (hd : 3 ≤ d) :
    championMid d ≤ (beta d)⁻¹ := by
  have hden := denominator_pos d (by omega)
  have hbpos := beta_pos d (by omega)
  have hkey := beta_sq_sub_beta_sub_one_pos d hd
  rw [championMid, inv_eq_one_div, div_le_div_iff₀ hden hbpos]
  linarith

theorem champion_mid_lt_predecessor_window (d : Nat) (hd : 3 ≤ d) :
    championMid d < (beta d - 1) - threshold d := by
  have hden := denominator_pos d (by omega)
  have hgt := beta_one_lt d (by omega)
  have hkey := beta_sq_sub_beta_sub_one_pos d hd
  have hcube : 0 < beta d ^ 3 - 2 * beta d ^ 2 + 1 := by
    have hfactor : beta d ^ 3 - 2 * beta d ^ 2 + 1
        = (beta d - 1) * (beta d ^ 2 - beta d - 1) := by ring
    rw [hfactor]
    exact mul_pos (by linarith [beta_one_lt d (by omega : 2 ≤ d)]) hkey
  have hsum : 1 / (beta d ^ 2 - 1) - beta d / (beta d ^ 2 - 1)
      = (1 - beta d) / (beta d ^ 2 - 1) := by field_simp
  have hkey2 : 1 / (beta d ^ 2 - 1) - beta d / (beta d ^ 2 - 1) < beta d - 2 := by
    rw [hsum, div_lt_iff₀ hden]
    nlinarith [hcube]
  rw [threshold_eq d (by omega), championMid]
  linarith

theorem champion_mid_add_threshold_le_one (d : Nat) (hd : 2 ≤ d) :
    championMid d + threshold d ≤ 1 := by
  have hden := denominator_pos d hd
  have hgt := beta_one_lt d hd
  have hmul : (1 / (beta d ^ 2 - 1) - beta d / (beta d ^ 2 - 1)) * (beta d ^ 2 - 1)
      = 1 - beta d := by field_simp
  rw [threshold_eq d hd, championMid]
  nlinarith [hmul, hden, hgt]

theorem top_mem (d : Nat) (hd : 3 ≤ d) (eps : Real) (hpos : 0 < eps)
    (hsmall : eps < perturbationBudget d) :
    (⟨top d (by omega), championTop d - eps⟩ : State d) ∈ strictSet d := by
  have hlen := normalized_top_length d (by omega)
  have htop := champion_top_eq d (by omega)
  have hle := champion_mid_add_threshold_le_one d (by omega)
  have hmin : perturbationBudget d ≤ championMid d - threshold d :=
    min_le_left _ _
  rw [strict_mem_iff]
  refine ⟨by rw [htop] at *; linarith, ?_⟩
  rw [hlen, htop]
  linarith

theorem mid_mem (d : Nat) (hd : 3 ≤ d) (eps : Real) (hpos : 0 < eps)
    (hsmall : eps < perturbationBudget d) :
    (⟨⟨d - 2, by omega⟩, championMid d - eps⟩ : State d) ∈ strictSet d := by
  have hlen := normalized_predecessor_length d hd
  have hwin := champion_mid_lt_predecessor_window d hd
  have hmin : perturbationBudget d ≤ championMid d - threshold d :=
    min_le_left _ _
  rw [strict_mem_iff]
  exact ⟨by linarith, by rw [hlen]; linarith⟩

/-- Both phases of the perturbed champion orbit survive to every finite strict
depth, provided the perturbation stays inside the budget after `n` expansions. -/
theorem perturbed_champion_mem (d : Nat) (hd : 3 ≤ d) :
    ∀ (n : Nat) (eps : Real), 0 < eps → beta d ^ n * eps < perturbationBudget d →
      (⟨top d (by omega), championTop d - eps⟩ : State d) ∈
          backward d (by omega) (strictSet d) n ∧
        (⟨⟨d - 2, by omega⟩, championMid d - eps⟩ : State d) ∈
          backward d (by omega) (strictSet d) n := by
  intro n
  induction n with
  | zero =>
      intro eps hpos hbound
      have hsmall : eps < perturbationBudget d := by simpa using hbound
      exact ⟨top_mem d hd eps hpos hsmall, mid_mem d hd eps hpos hsmall⟩
  | succ n ih =>
      intro eps hpos hbound
      have hbpos := beta_pos d (by omega)
      have hstep : beta d ^ n * (beta d * eps) < perturbationBudget d := by
        have hrw : beta d ^ n * (beta d * eps) = beta d ^ (n + 1) * eps := by ring
        rw [hrw]; exact hbound
      have hnext := ih (beta d * eps) (mul_pos hbpos hpos) hstep
      have hsmall : eps < perturbationBudget d := by
        have hone : (1 : Real) ≤ beta d ^ (n + 1) :=
          one_le_pow₀ (le_of_lt
            (beta_one_lt d (by omega)))
        nlinarith
      have hminb : perturbationBudget d ≤ championTop d - (beta d)⁻¹ :=
        min_le_right _ _
      constructor
      · rw [backward_succ]
        refine ⟨top_mem d hd eps hpos hsmall, ?_⟩
        rw [Set.mem_preimage]
        have hzero : (⟨top d (by omega), championTop d - eps⟩ : State d).kind.1 ≠ 0 := by
          simp [top, D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter]; omega
        have hright : ¬ (⟨top d (by omega), championTop d - eps⟩ : State d).coordinate
            ≤ (beta d)⁻¹ := by
          simp only
          exact not_le.mpr (by linarith)
        rw [transition_right d (by omega) _ hzero hright]
        have hstate : (⟨⟨(⟨top d (by omega), championTop d - eps⟩ : State d).kind.1 - 1,
              by omega⟩, beta d * (championTop d - eps) - 1⟩ : State d)
            = ⟨⟨d - 2, by omega⟩, championMid d - beta d * eps⟩ := by
          refine state_ext ?_ ?_
          · simp [top, D5.S0.Tower.DBonacci.GapAlphabet.topGapLetter]; omega
          · simp only
            have := champion_step_top d (by omega)
            linarith [this]
        simpa only [hstate] using hnext.2
      · rw [backward_succ]
        refine ⟨mid_mem d hd eps hpos hsmall, ?_⟩
        rw [Set.mem_preimage]
        have hzero : (⟨⟨d - 2, by omega⟩, championMid d - eps⟩ : State d).kind.1 ≠ 0 := by
          simp; omega
        have hleft : (⟨⟨d - 2, by omega⟩, championMid d - eps⟩ : State d).coordinate
            ≤ (beta d)⁻¹ := by
          simp only
          linarith [champion_mid_le_inverse d hd]
        rw [transition_left d (by omega) _ hzero hleft]
        have hstate : (⟨top d (by omega), beta d * (championMid d - eps)⟩ : State d)
            = ⟨top d (by omega), championTop d - beta d * eps⟩ := by
          refine state_ext rfl ?_
          simp only
          have := champion_step_mid d (by omega)
          linarith [this]
        simpa only [hstate] using hnext.1

/-- Every finite strict depth is nonempty, uniformly in the order. -/
theorem strict_backward_nonempty (d : Nat) (hd : 3 ≤ d) (n : Nat) :
    (backward d (by omega) (strictSet d) n).Nonempty := by
  have hbpow : 0 < beta d ^ n := pow_pos (beta_pos d (by omega)) n
  have hbud := perturbation_budget_pos d (by omega)
  refine ⟨⟨top d (by omega),
    championTop d - perturbationBudget d / (2 * beta d ^ n)⟩, ?_⟩
  refine (perturbed_champion_mem d hd n _ (by positivity) ?_).1
  have hcancel : beta d ^ n * (perturbationBudget d / (2 * beta d ^ n))
      = perturbationBudget d / 2 := by field_simp
  rw [hcancel]
  linarith

/-- The separation at orders four and five, whose all-depth intersections are
already known to be empty. -/
theorem four_finite_depths_nonempty_and_permanent_empty :
    (∀ n : Nat, (backward 4 (by omega) (strictSet 4) n).Nonempty) ∧
      strictPermanent 4 (by omega) = ∅ :=
  ⟨strict_backward_nonempty 4 (by omega),
    dbonacci_four_strict_permanent_set_eq_empty⟩

theorem five_finite_depths_nonempty_and_permanent_empty :
    (∀ n : Nat, (backward 5 (by omega) (strictSet 5) n).Nonempty) ∧
      strictPermanent 5 (by omega) = ∅ :=
  ⟨strict_backward_nonempty 5 (by omega),
    dbonacci_five_strict_permanent_set_eq_empty⟩

end D5.S0.Tower.DBonacciSurvivors.FiniteDepth
