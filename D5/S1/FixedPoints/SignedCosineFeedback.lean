/- GID: D5/S1/FixedPoints/SignedCosineFeedback
   generality: I
   mirror-B: D5/B/S1/FixedPoints/SignedCosineFeedback
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed cosine feedback: one real fixed point, sin 1 contraction, period-two sign policy, free-sign modulus limit. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue

/- Library-search audit trail (2026-11-10):
   * Repository search of `D5/` for the statement shape (`Real.sin 1`,
     iterates of `Real.cos`, `cos x = x`, cosine feedback) found no
     declaration; the nearest neighbour `affine_feedback_threshold` treats
     affine maps only and does not apply to the cosine.
   * Pinned-Mathlib search (`dottie`, `cos x = x`, `IsFixedPt cos`) found no
     fixed-point theorem for the cosine. `Real.abs_cos_sub_cos_le` gives the
     Lipschitz constant one, which is not a contraction.
   * Pinned-Mathlib hits `Real.cos_sub_cos`, `Real.abs_sin_le_abs`,
     `Real.sin_le_sin_of_le_of_le_pi_div_two`, `Real.one_le_pi_div_two`,
     `Real.sin_lt`, `intermediate_value_Icc'` and
     `tendsto_pow_atTop_nhds_zero_of_lt_one` are applied below.
   * Pinned-Mathlib hit `ContractingWith` (`Mathlib.Topology.MetricSpace.Contracting`)
     is not applied: the cosine is only 1-Lipschitz on the real line, and the
     restricted version bounds the error by `edist x (f x) * K ^ n / (1 - K)`
     rather than by `K ^ n` times the error after the first step.
   * Loogle queries `Real.cos ?x = ?x`, `Function.IsFixedPt Real.cos`,
     `"dottie"`, `Real.cos, Nat.iterate, Filter.Tendsto` and
     `|Real.cos ?x - Real.cos ?y| ≤ Real.sin 1 * _` each returned no hit. -/

namespace D5.S1.FixedPoints.SignedCosineFeedback

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- On `[-1, 1]` the sine is bounded in absolute value by `sin 1`. -/
private theorem abs_sin_le_sin_one {u : ℝ} (hu : |u| ≤ 1) :
    |Real.sin u| ≤ Real.sin 1 := by
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := Real.one_le_pi_div_two
  obtain ⟨hl, hr⟩ := abs_le.mp hu
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := -1) (y := u) (by linarith) (by linarith) hl
    rwa [Real.sin_neg] at h
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hpi hr

/-- On `[-1, 1]` the cosine is Lipschitz with constant `sin 1`. -/
private theorem abs_cos_sub_cos_le_sin_one_mul {x y : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |Real.cos x - Real.cos y| ≤ Real.sin 1 * |x - y| := by
  have hmid : |(x + y) / 2| ≤ 1 := by
    rw [abs_div, abs_two]
    have hadd : |x + y| ≤ |x| + |y| := abs_add_le x y
    linarith
  have hsin := abs_sin_le_sin_one hmid
  have hhalf : |Real.sin ((x - y) / 2)| ≤ |(x - y) / 2| := Real.abs_sin_le_abs
  have hnonneg : 0 ≤ |Real.sin ((x + y) / 2)| := abs_nonneg _
  have hprod :
      |Real.sin ((x + y) / 2)| * |Real.sin ((x - y) / 2)| ≤
        Real.sin 1 * |(x - y) / 2| :=
    mul_le_mul hsin hhalf (abs_nonneg _) (hnonneg.trans hsin)
  have htwo : |(-2 : ℝ)| = 2 := by norm_num
  have hsplit : |(x - y) / 2| = |x - y| / 2 := by rw [abs_div, abs_two]
  rw [Real.cos_sub_cos, abs_mul, abs_mul, htwo]
  rw [hsplit] at hprod
  linarith

/-- The two signed cosine maps `x ↦ s * cos x`, `s = ±1`, share one positive
number `r` in `(0, 1)` with `cos r = r`. The map with sign `s` has `s * r` as
its only real fixed point, sends every real number into `[-1, 1]`, multiplies
distances on `[-1, 1]` by at most `sin 1 < 1`, and its iterates approach
`s * r` with that error ratio. The equations `cos x = x` and `cos x = -x` have
no common real solution, and every policy `G (s, x) = (-s, -s * cos x)` on the
two signs exchanges `(1, r)` and `(-1, -r)`. If the sign is chosen freely at
every step, the absolute values still follow the cosine after one step and
converge to `r`, while the sign itself can alternate forever. -/
theorem signed_cosine_feedback_fixed_point :
    ∃ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 ∧ Real.cos r = r ∧
      (∀ y ∈ Set.Ioo (0 : ℝ) 1, Real.cos y = y → y = r) ∧
      0 < Real.sin 1 ∧ Real.sin 1 < 1 ∧
      (∀ s : ℝ, s = 1 ∨ s = -1 →
        (∀ x : ℝ, s * Real.cos x = x ↔ x = s * r) ∧
        (∀ x : ℝ, s * Real.cos x ∈ Set.Icc (-1 : ℝ) 1) ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
          |s * Real.cos x - s * Real.cos y| ≤ Real.sin 1 * |x - y|) ∧
        (∀ (x : ℝ) (n : ℕ),
          |(fun y : ℝ => s * Real.cos y)^[n + 1] x - s * r| ≤
            Real.sin 1 ^ n * |s * Real.cos x - s * r|) ∧
        (∀ x : ℝ,
          Filter.Tendsto (fun n : ℕ => (fun y : ℝ => s * Real.cos y)^[n] x)
            Filter.atTop (nhds (s * r)))) ∧
      (¬ ∃ x : ℝ, Real.cos x = x ∧ Real.cos x = -x) ∧
      (∀ G : ℝ × ℝ → ℝ × ℝ,
        (∀ s x : ℝ, s = 1 ∨ s = -1 → G (s, x) = (-s, -s * Real.cos x)) →
          G (1, r) = (-1, -r) ∧ G (-1, -r) = (1, r) ∧
            ((1 : ℝ), r) ≠ ((-1 : ℝ), -r)) ∧
      (∀ σ x : ℕ → ℝ, (∀ n : ℕ, σ n = 1 ∨ σ n = -1) →
        (∀ n : ℕ, x (n + 1) = σ n * Real.cos (x n)) →
          (∀ n : ℕ, |x (n + 2)| = Real.cos |x (n + 1)|) ∧
            Filter.Tendsto (fun n : ℕ => |x n|) Filter.atTop (nhds r)) ∧
      (∃ σ x : ℕ → ℝ, (∀ n : ℕ, σ n = 1 ∨ σ n = -1) ∧
        (∀ n : ℕ, x (n + 1) = σ n * Real.cos (x n)) ∧
          (∀ n : ℕ, x (n + 1) = -x n) ∧ x 0 = r) := by
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := Real.one_le_pi_div_two
  have hsin_pos : 0 < Real.sin 1 :=
    Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith)
  have hsin_lt : Real.sin 1 < 1 := Real.sin_lt one_pos
  have hcos_one : Real.cos 1 < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := 1) le_rfl (by linarith) one_pos
    rwa [Real.cos_zero] at h
  -- Existence: `cos x - x` changes sign on `[0, 1]`.
  have hcont : ContinuousOn (fun x : ℝ => Real.cos x - x) (Set.Icc 0 1) :=
    (Real.continuous_cos.sub continuous_id).continuousOn
  have hzero :
      (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => Real.cos x - x) 1)
        ((fun x : ℝ => Real.cos x - x) 0) := by
    constructor
    · show Real.cos 1 - 1 ≤ 0
      linarith
    · show (0 : ℝ) ≤ Real.cos 0 - 0
      rw [Real.cos_zero]
      norm_num
  obtain ⟨r, hrmem, hrzero⟩ :=
    intermediate_value_Icc' (zero_le_one' ℝ) hcont hzero
  have hr : Real.cos r = r := by
    have h : Real.cos r - r = 0 := hrzero
    linarith
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, Real.cos_zero] at hr
    exact one_ne_zero hr
  have hr1 : r ≠ 1 := by
    intro h
    rw [h] at hr
    linarith
  have hrIoo : r ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hrmem.1 (Ne.symm hr0), lt_of_le_of_ne hrmem.2 hr1⟩
  have hrabs : |r| ≤ 1 := abs_le.mpr ⟨by linarith [hrIoo.1], hrIoo.2.le⟩
  -- Facts shared by both signs.
  have hsign_abs : ∀ s : ℝ, s = 1 ∨ s = -1 → |s| = 1 := by
    intro s hs
    rcases hs with rfl | rfl <;> norm_num
  have himage : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ x : ℝ, |s * Real.cos x| ≤ 1 := by
    intro s hs x
    rw [abs_mul, hsign_abs s hs, one_mul]
    exact Real.abs_cos_le_one x
  have hfixed : ∀ s : ℝ, s = 1 ∨ s = -1 → s * Real.cos (s * r) = s * r := by
    intro s hs
    rcases hs with rfl | rfl
    · simp [hr]
    · simp [Real.cos_neg, hr]
  have hsr_abs : ∀ s : ℝ, s = 1 ∨ s = -1 → |s * r| ≤ 1 := by
    intro s hs
    rw [abs_mul, hsign_abs s hs, one_mul]
    exact hrabs
  -- One step of the signed map contracts the distance to `s * r` on `[-1, 1]`.
  have hstep : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ x : ℝ, |x| ≤ 1 →
      |s * Real.cos x - s * r| ≤ Real.sin 1 * |x - s * r| := by
    intro s hs x hx
    have hrewrite :
        s * Real.cos x - s * r = s * (Real.cos x - Real.cos (s * r)) := by
      have h := hfixed s hs
      linarith
    rw [hrewrite, abs_mul, hsign_abs s hs, one_mul]
    exact abs_cos_sub_cos_le_sin_one_mul hx (hsr_abs s hs)
  have hunique : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ x : ℝ,
      (s * Real.cos x = x ↔ x = s * r) := by
    intro s hs x
    constructor
    · intro hx
      have hxabs : |x| ≤ 1 := by
        rw [← hx]
        exact himage s hs x
      have hcontract := hstep s hs x hxabs
      rw [hx] at hcontract
      have hdist : |x - s * r| ≤ 0 := by
        by_contra hpos
        have hpos' : 0 < |x - s * r| := lt_of_not_ge hpos
        nlinarith
      exact sub_eq_zero.mp (abs_nonpos_iff.mp hdist)
    · intro hx
      rw [hx]
      exact hfixed s hs
  have hbound : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ (x : ℝ) (n : ℕ),
      |(fun y : ℝ => s * Real.cos y)^[n + 1] x - s * r| ≤
        Real.sin 1 ^ n * |s * Real.cos x - s * r| := by
    intro s hs x n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hin : |(fun y : ℝ => s * Real.cos y)^[n + 1] x| ≤ 1 := by
        rw [Function.iterate_succ_apply']
        exact himage s hs _
      have hone := hstep s hs _ hin
      calc
        |s * Real.cos ((fun y : ℝ => s * Real.cos y)^[n + 1] x) - s * r|
            ≤ Real.sin 1 * |(fun y : ℝ => s * Real.cos y)^[n + 1] x - s * r| :=
          hone
        _ ≤ Real.sin 1 * (Real.sin 1 ^ n * |s * Real.cos x - s * r|) :=
          mul_le_mul_of_nonneg_left ih hsin_pos.le
        _ = Real.sin 1 ^ (n + 1) * |s * Real.cos x - s * r| := by ring
  have hlimit : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ x : ℝ,
      Filter.Tendsto (fun n : ℕ => (fun y : ℝ => s * Real.cos y)^[n] x)
        Filter.atTop (nhds (s * r)) := by
    intro s hs x
    have hpow :
        Filter.Tendsto
          (fun n : ℕ => Real.sin 1 ^ n * |s * Real.cos x - s * r|)
          Filter.atTop (nhds 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hsin_pos.le hsin_lt).mul_const
        |s * Real.cos x - s * r|
      simpa using h
    have hshift :
        Filter.Tendsto
          (fun n : ℕ => (fun y : ℝ => s * Real.cos y)^[n + 1] x)
          Filter.atTop (nhds (s * r)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hpow
      rw [Real.dist_eq]
      exact hbound s hs x n
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp hshift
  have hlipschitz : ∀ s : ℝ, s = 1 ∨ s = -1 →
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
        |s * Real.cos x - s * Real.cos y| ≤ Real.sin 1 * |x - y| := by
    intro s hs x hx y hy
    rw [← mul_sub, abs_mul, hsign_abs s hs, one_mul]
    exact abs_cos_sub_cos_le_sin_one_mul (abs_le.mpr ⟨hx.1, hx.2⟩)
      (abs_le.mpr ⟨hy.1, hy.2⟩)
  refine ⟨r, hrIoo, hr, ?_, hsin_pos, hsin_lt, ?_, ?_, ?_, ?_, ?_⟩
  · intro y _ hy
    have h := (hunique 1 (Or.inl rfl) y).mp (by simpa using hy)
    simpa using h
  · intro s hs
    exact ⟨hunique s hs, fun x => abs_le.mp (himage s hs x), hlipschitz s hs,
      hbound s hs, hlimit s hs⟩
  · rintro ⟨x, hx, hxneg⟩
    have hx0 : x = 0 := by linarith
    rw [hx0, Real.cos_zero] at hx
    exact one_ne_zero hx
  · intro G hG
    refine ⟨?_, ?_, ?_⟩
    · rw [hG 1 r (Or.inl rfl), hr]
      simp
    · rw [hG (-1) (-r) (Or.inr rfl), Real.cos_neg, hr]
      simp
    · intro h
      have h1 : (1 : ℝ) = -1 := congrArg Prod.fst h
      norm_num at h1
  · intro σ x hσ hx
    have hxabs : ∀ n : ℕ, |x (n + 1)| ≤ 1 := by
      intro n
      rw [hx n]
      exact himage (σ n) (hσ n) (x n)
    have hmod : ∀ n : ℕ, |x (n + 2)| = Real.cos |x (n + 1)| := by
      intro n
      have hcos : 0 ≤ Real.cos (x (n + 1)) := by
        obtain ⟨hl, hu⟩ := abs_le.mp (hxabs n)
        exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
      rw [hx (n + 1), abs_mul, hsign_abs _ (hσ (n + 1)), one_mul,
        abs_of_nonneg hcos, Real.cos_abs]
    refine ⟨hmod, ?_⟩
    have hiter : ∀ n : ℕ,
        |x (n + 1)| = (fun y : ℝ => 1 * Real.cos y)^[n] |x 1| := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ← ih, one_mul]
        exact hmod n
    have hcosine := hlimit 1 (Or.inl rfl) |x 1|
    rw [one_mul] at hcosine
    have hshift :
        Filter.Tendsto (fun n : ℕ => |x (n + 1)|) Filter.atTop (nhds r) := by
      have hfun :
          (fun n : ℕ => |x (n + 1)|) =
            fun n : ℕ => (fun y : ℝ => 1 * Real.cos y)^[n] |x 1| :=
        funext hiter
      rw [hfun]
      exact hcosine
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp hshift
  · refine ⟨fun n => (-1) ^ (n + 1), fun n => (-1) ^ n * r, ?_, ?_, ?_, ?_⟩
    · intro n
      exact neg_one_pow_eq_or ℝ (n + 1)
    · intro n
      have hcos : Real.cos ((-1) ^ n * r) = r := by
        rcases neg_one_pow_eq_or ℝ n with h | h
        · rw [h, one_mul, hr]
        · rw [h, neg_one_mul, Real.cos_neg, hr]
      rw [hcos]
    · intro n
      show (-1 : ℝ) ^ (n + 1) * r = -((-1) ^ n * r)
      rw [pow_succ]
      ring
    · simp

/-- Hypothesis probe: the policy premise is satisfiable. -/
example :
    ∃ G : ℝ × ℝ → ℝ × ℝ,
      ∀ s x : ℝ, s = 1 ∨ s = -1 → G (s, x) = (-s, -s * Real.cos x) :=
  ⟨fun p => (-p.1, -p.1 * Real.cos p.2), fun _ _ _ => rfl⟩

/-- Reverse probe: the theorem places every real solution of `cos x = x` in
the open unit interval, because the fixed-point clause identifies it with `r`. -/
example {x : ℝ} (hx : Real.cos x = x) : 0 < x ∧ x < 1 := by
  obtain ⟨r, hrmem, _, _, _, _, hsigned, _⟩ := signed_cosine_feedback_fixed_point
  have h := ((hsigned 1 (Or.inl rfl)).1 x).mp (by simpa using hx)
  rw [h, one_mul]
  exact hrmem

/-- Trivialization probe: zero solves neither `cos x = x` nor `cos x = -x`. -/
example : Real.cos 0 ≠ 0 ∧ Real.cos 0 ≠ -0 := by
  rw [Real.cos_zero]
  norm_num

#print axioms signed_cosine_feedback_fixed_point

end D5.S1.FixedPoints.SignedCosineFeedback
