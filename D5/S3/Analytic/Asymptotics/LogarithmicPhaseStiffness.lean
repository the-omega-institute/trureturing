/- GID: D5/S3/Analytic/Asymptotics/LogarithmicPhaseStiffness
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/LogarithmicPhaseStiffness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Raw spectral counts produce global C1 phases and logarithmic square bounds. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

set_option autoImplicit false
open Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness

noncomputable def realCutoff {ι : Type*} (γ : ι → ℝ)
    (hfinite : ∀ Y : ℝ, Set.Finite {i | γ i < Y}) (Y : ℝ) : Finset ι :=
  (hfinite Y).toFinset

noncomputable def strictCount {ι : Type*} (γ m : ι → ℝ)
    (hfinite : ∀ Y : ℝ, Set.Finite {i | γ i < Y}) (Y : ℝ) : ℝ :=
  ∑ i ∈ realCutoff γ hfinite Y, m i

/- Production of the integral bridge from the raw locally finite spectrum.
   No partial-moment identity is assumed. Strict cutoffs avoid silently dropping
   a multiplicity jump at the moving endpoint. -/

noncomputable def phaseWeight {ι : Type*} (γ m : ι → ℝ) (i : ι) : ℝ :=
  m i / (γ i * (1/4+(γ i)^2))

noncomputable def phaseMoment {ι : Type*} (γ m : ι → ℝ)
    (hfinite : ∀ u : ℝ, Set.Finite {i | γ i < u}) (Y : ℝ) : ℝ :=
  ∑ i ∈ realCutoff γ hfinite Y, phaseWeight γ m i * (γ i)^2

noncomputable def phaseCost {ι : Type*} (γ a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑' i, 2*a i*(1-Real.cos (γ i*t))

/- The error bound retains the fixed lower-cutoff and total-weight contributions. -/

noncomputable def momentErrorBound (L Y c C mass : ℝ) : ℝ :=
  c*Real.log Y+C+c/2*(Real.log L)^2+C*(Real.log Y-Real.log L)+mass/4

/- Raw counting produces both sides of the adaptive split. -/

noncomputable def phaseSlope {ι : Type*} (γ a : ι → ℝ) (t : ℝ) : ℝ :=
  ∑' i, 2*a i*γ i*Real.sin (γ i*t)

set_option maxHeartbeats 1600000 in
-- The proof assembles improper integral tails and uniform moving-cutoff estimates.
/-- A raw weighted real-spectrum count produces C1 cosine phase and uniform
moving-cutoff errors, without any moment or infinite-tail premise. -/
theorem logarithmic_phase_stiffness {ι : Type*} (γ m : ι → ℝ)
    (hfinite : ∀ u : ℝ, Set.Finite {i | γ i < u}) {L c C : ℝ}
    (hL : 1 < L) (hγ : ∀ i, L ≤ γ i) (hm : ∀ i, 0 ≤ m i) (hc : 0 ≤ c)
    (hcount : ∀ u, L ≤ u →
      |strictCount γ m hfinite u - c*u*Real.log u| ≤ C*u) :
    Summable (phaseWeight γ m) ∧
    Summable (fun i => phaseWeight γ m i*γ i) ∧
    (∀ t, HasDerivAt (phaseCost γ (phaseWeight γ m)) (phaseSlope γ (phaseWeight γ m) t) t) ∧
    Continuous (phaseSlope γ (phaseWeight γ m)) ∧
    ∀ t, 0 < |t| → L*|t| ≤ 1 →
      let Y := |t|⁻¹
      |phaseCost γ (phaseWeight γ m) t-t^2*phaseMoment γ m hfinite Y| ≤
        t^2*(9*c*Real.log Y+8*c+9*C) ∧
      |phaseSlope γ (phaseWeight γ m) t-2*t*phaseMoment γ m hfinite Y| ≤
        |t| * (5*c*Real.log Y+4*c+5*C) ∧
      |phaseCost γ (phaseWeight γ m) t-c/2*t^2*(Real.log Y)^2| ≤
        t^2*(9*c*Real.log Y+8*c+9*C+
          momentErrorBound L Y c C (∑' i, phaseWeight γ m i)) ∧
      |phaseSlope γ (phaseWeight γ m) t-c*t*(Real.log Y)^2| ≤
        |t| * (5*c*Real.log Y+4*c+5*C+
          2*momentErrorBound L Y c C (∑' i, phaseWeight γ m i)) := by
  let reciprocalMoment (γ m : ι → ℝ)
      (hfinite : ∀ Y : ℝ, Set.Finite {i | γ i < Y}) (Y : ℝ) : ℝ :=
    ∑ i ∈ realCutoff γ hfinite Y, m i / γ i
  have finite_reciprocal_count_identity (s : Finset ι)
      (γ m : ι → ℝ) {L Y : ℝ} (hL : 0 < L) (hLY : L ≤ Y)
      (hγ : ∀ i ∈ s, γ i ∈ Icc L Y) :
      ∑ i ∈ s, m i / γ i = (∑ i ∈ s, m i) / Y +
        ∫ u in L..Y, (∑ i ∈ s, if γ i < u then m i else 0) / u^2 := by
    classical
    have primitive (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
        (∫ u in a..b, (1 : ℝ) / u^2) = 1 / a - 1 / b := by
      have hz := integral_zpow (a := a) (b := b) (n := (-2 : ℤ))
        (Or.inr ⟨by norm_num, notMem_uIcc_of_lt ha (ha.trans_le hab)⟩)
      norm_num [zpow_neg, zpow_ofNat] at hz
      simpa only [one_div, div_neg, div_one, neg_sub] using hz
    have kernel (i : ι) : IntervalIntegrable (fun u : ℝ => m i / u^2) volume L Y := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_const.div (continuousOn_id.pow 2)
      intro u hu
      rw [uIcc_of_le hLY] at hu
      exact pow_ne_zero _ (ne_of_gt (hL.trans_le hu.1))
    have hint (i : ι) : IntervalIntegrable
        (fun u : ℝ => if γ i < u then m i / u^2 else 0) volume L Y := by
      have hi : IntervalIntegrable ((Iic (γ i)).indicator (fun u : ℝ => m i / u^2))
          volume L Y := ⟨(kernel i).1.indicator measurableSet_Iic,
            (kernel i).2.indicator measurableSet_Iic⟩
      convert (kernel i).sub hi using 1
      funext u
      by_cases h : γ i < u
      · simp [h, not_le.mpr h]
      · simp [h, le_of_not_gt h]
    have hsingle (i : ι) (hi : i ∈ s) :
        (∫ u in L..Y, if γ i < u then m i / u^2 else 0) =
          m i / γ i - m i / Y := by
      have hγi := hγ i hi
      have hind : IntervalIntegrable ((Iic (γ i)).indicator (fun u : ℝ => m i / u^2))
          volume L Y := ⟨(kernel i).1.indicator measurableSet_Iic,
            (kernel i).2.indicator measurableSet_Iic⟩
      have heq : (fun u : ℝ => if γ i < u then m i / u^2 else 0) =
          (fun u => m i / u^2 - (Iic (γ i)).indicator (fun v => m i / v^2) u) := by
        funext u
        by_cases h : γ i < u
        · simp [h, not_le.mpr h]
        · simp [h, le_of_not_gt h]
      rw [heq, intervalIntegral.integral_sub (kernel i) hind]
      change (∫ u in L..Y, m i / u^2) -
        (∫ u in L..Y, ({u : ℝ | u ≤ γ i}).indicator (fun v => m i / v^2) u) = _
      rw [intervalIntegral.integral_indicator hγi]
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rw [show (fun u : ℝ => (u^2)⁻¹) = (fun u : ℝ => 1/u^2) by ext; simp]
      rw [primitive L Y hL hLY, primitive L (γ i) hL hγi.1]
      ring
    have hsum : (∫ u in L..Y, (∑ i ∈ s, if γ i < u then m i else 0) / u^2) =
        ∑ i ∈ s, (m i / γ i - m i / Y) := by
      rw [show (fun u : ℝ => (∑ i ∈ s, if γ i < u then m i else 0) / u^2) =
          (fun u => ∑ i ∈ s, if γ i < u then m i / u^2 else 0) by
        ext u
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> simp]
      rw [intervalIntegral.integral_finsetSum (fun i _ => hint i)]
      exact Finset.sum_congr rfl hsingle
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_div]
    ring

  have reciprocal_moment_identity (γ m : ι → ℝ)
      (hfinite : ∀ Y : ℝ, Set.Finite {i | γ i < Y}) {L Y : ℝ}
      (hL : 0 < L) (hLY : L ≤ Y) (hγ : ∀ i, L ≤ γ i) :
      reciprocalMoment γ m hfinite Y = strictCount γ m hfinite Y / Y +
        ∫ u in L..Y, strictCount γ m hfinite u / u^2 := by
    classical
    have hcut : ∀ i ∈ realCutoff γ hfinite Y, γ i ∈ Icc L Y := by
      intro i hi
      have hiy : γ i < Y := by simpa only [realCutoff, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq] using hi
      exact ⟨hγ i, hiy.le⟩
    have hcount (u : ℝ) (hu : u ≤ Y) :
        (∑ i ∈ realCutoff γ hfinite Y, if γ i < u then m i else 0) =
          strictCount γ m hfinite u := by
      have hfilter : (realCutoff γ hfinite Y).filter (fun i => γ i < u) =
          realCutoff γ hfinite u := by
        ext i
        simp only [Finset.mem_filter, realCutoff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun hi => ⟨hi.trans_le hu, hi⟩⟩
      rw [← Finset.sum_filter, hfilter]
      rfl
    unfold reciprocalMoment strictCount
    rw [finite_reciprocal_count_identity (realCutoff γ hfinite Y) γ m hL hLY hcut]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hLY] at hu
    change (∑ i ∈ realCutoff γ hfinite Y, if γ i < u then m i else 0) / u^2 =
      strictCount γ m hfinite u / u^2
    rw [hcount u hu.2]

  /- The raw count residual is integrated at its real cutoff. This theorem does
     not take the desired logarithmic moment asymptotic as a hypothesis. -/

  have reciprocal_moment_log_sq_error_bound (γ m : ι → ℝ)
      (hfinite : ∀ Y : ℝ, Set.Finite {i | γ i < Y}) {L Y c C : ℝ}
      (hL : 1 < L) (hLY : L ≤ Y) (hγ : ∀ i, L ≤ γ i)
      (hm : ∀ i, 0 ≤ m i) (hc : 0 ≤ c)
      (hcount : ∀ u, L ≤ u →
        |strictCount γ m hfinite u - c * u * Real.log u| ≤ C * u) :
      |reciprocalMoment γ m hfinite Y - c / 2 * (Real.log Y)^2| ≤
        c * Real.log Y + C + c / 2 * (Real.log L)^2 +
          C * (Real.log Y - Real.log L) := by
    classical
    let N := strictCount γ m hfinite
    have hL0 : 0 < L := zero_lt_one.trans hL
    have hY0 : 0 < Y := hL0.trans_le hLY
    have hmono : Monotone N := by
      intro u v huv
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [realCutoff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi ⊢
        exact hi.trans_le huv
      · intro i _ _
        exact hm i
    have hup (u : ℝ) (hu : u ∈ uIcc L Y) : 0 < u := by
      rw [uIcc_of_le hLY] at hu
      exact hL0.trans_le hu.1
    have hnint : IntervalIntegrable (fun u : ℝ => N u / u^2) volume L Y := by
      have hk : ContinuousOn (fun u : ℝ => (u^2)⁻¹) (uIcc L Y) :=
        (continuousOn_id.pow 2).inv₀ (fun u hu => pow_ne_zero _ (hup u hu).ne')
      simpa only [div_eq_mul_inv] using hmono.intervalIntegrable.mul_continuousOn hk
    have hmainint : IntervalIntegrable (fun u : ℝ => c * Real.log u / u) volume L Y := by
      apply ContinuousOn.intervalIntegrable
      exact (continuousOn_const.mul
        (Real.continuousOn_log.mono (fun u hu => (hup u hu).ne'))).div continuousOn_id
          (fun u hu => (hup u hu).ne')
    have hmain : (∫ u in L..Y, c * Real.log u / u) =
        c / 2 * ((Real.log Y)^2 - (Real.log L)^2) := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u : ℝ => c / 2 * (Real.log u)^2)
        (f' := fun u : ℝ => c * Real.log u / u)
        (fun u hu => by
          convert! ((Real.hasDerivAt_log (hup u hu).ne').pow 2).const_mul (c / 2) using 1
          norm_num [div_eq_mul_inv]
          ring) hmainint
      exact h.trans (by ring)
    have hdomint : IntervalIntegrable (fun u : ℝ => C / u) volume L Y := by
      exact (continuousOn_const.div continuousOn_id (fun u hu => (hup u hu).ne')).intervalIntegrable
    have herror : |∫ u in L..Y, N u / u^2 - c * Real.log u / u| ≤
        C * (Real.log Y - Real.log L) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le hLY
        (f := fun u : ℝ => N u / u^2 - c * Real.log u / u)
        (g := fun u : ℝ => C / u) (Eventually.of_forall (fun u hu => by
          have hu0 : 0 < u := hL0.trans hu.1
          have heq : N u / u^2 - c * Real.log u / u =
              (N u - c * u * Real.log u) / u^2 := by field_simp
          rw [heq, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg u)]
          apply (div_le_iff₀ (sq_pos_of_pos hu0)).mpr
          calc
            |N u - c * u * Real.log u| ≤ C * u := hcount u hu.1.le
            _ = C / u * u^2 := by field_simp)) hdomint
      have hg : (∫ u in L..Y, C / u) = C * (Real.log Y - Real.log L) := by
        simp_rw [show (fun u : ℝ => C/u) = (fun u => C * (1/u)) by ext; ring]
        rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hL0 hY0,
          Real.log_div hY0.ne' hL0.ne']
      simpa only [Real.norm_eq_abs, hg] using h
    have hboundary : |N Y / Y - c * Real.log Y| ≤ C := by
      have heq : N Y / Y - c * Real.log Y = (N Y - c * Y * Real.log Y) / Y := by
        field_simp
      rw [heq, abs_div, abs_of_pos hY0]
      exact (div_le_iff₀ hY0).mpr (hcount Y hLY)
    have hmiddle : |c * Real.log Y - c / 2 * (Real.log L)^2| ≤
        c * Real.log Y + c / 2 * (Real.log L)^2 := by
      have hlogY : 0 ≤ Real.log Y := (Real.log_pos (hL.trans_le hLY)).le
      have hsecond : 0 ≤ c / 2 * (Real.log L)^2 := by positivity
      have hfirst := mul_nonneg hc hlogY
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hfull := reciprocal_moment_identity γ m hfinite hL0 hLY hγ
    have herr := intervalIntegral.integral_sub hnint hmainint
    rw [hmain] at herr
    have heq : reciprocalMoment γ m hfinite Y - c / 2 * (Real.log Y)^2 =
        (N Y / Y - c * Real.log Y) +
        (c * Real.log Y - c / 2 * (Real.log L)^2) +
        (∫ u in L..Y, N u / u^2 - c * Real.log u / u) := by
      dsimp only [N] at herr ⊢
      linarith [hfull]
    rw [heq]
    calc
      |(N Y / Y - c * Real.log Y) + (c * Real.log Y - c / 2 * (Real.log L)^2) +
          (∫ u in L..Y, N u / u^2 - c * Real.log u / u)| ≤
        |N Y / Y - c * Real.log Y| + |c * Real.log Y - c / 2 * (Real.log L)^2| +
          |∫ u in L..Y, N u / u^2 - c * Real.log u / u| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ C + (c * Real.log Y + c / 2 * (Real.log L)^2) +
          C * (Real.log Y - Real.log L) := add_le_add (add_le_add hboundary hmiddle) herror
      _ = _ := by ring


  /- Temporary analytic primitives for the raw count consumer. -/

  have inverse_cube_integral {Y w : ℝ} (hY : 0 < Y) (hw : 0 ≤ w) :
      IntegrableOn (fun u : ℝ => 2 * w / u^3) (Ioi Y) ∧
        (∫ u in Ioi Y, 2 * w / u^3) = w / Y^2 := by
    have hd : ∀ u ∈ Ici Y, HasDerivAt (fun v : ℝ => -w / v^2)
        (2 * w / u^3) u := by
      intro u hu
      have hu0 := hY.trans_le hu
      convert! (hasDerivAt_const u (-w)).div ((hasDerivAt_id u).pow 2)
        (pow_ne_zero _ hu0.ne') using 1
      simp only [Pi.pow_apply, id_eq]
      field_simp
      ring
    have ht : Tendsto (fun u : ℝ => -w / u^2) atTop (𝓝 0) := by
      convert! (tendsto_inv_atTop_zero.pow 2).const_mul (-w) using 1 <;>
        simp [div_eq_mul_inv, inv_pow]
    have hn : ∀ u ∈ Ioi Y, 0 ≤ 2 * w / u^3 := by
      intro u hu
      exact div_nonneg (mul_nonneg (by norm_num) hw) (pow_nonneg (hY.trans hu).le _)
    exact ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn ht,
      by simpa only [zero_sub, neg_div, neg_neg] using
        integral_Ioi_of_hasDerivAt_of_nonneg' hd hn ht⟩

  have count_majorant_integral {Y c C : ℝ} (hY : 1 < Y)
      (hc : 0 ≤ c) (hC : 0 ≤ C) :
      IntegrableOn (fun u : ℝ => 2 * (c * Real.log u + C) / u^2) (Ioi Y) ∧
        (∫ u in Ioi Y, 2 * (c * Real.log u + C) / u^2) =
          2 * (c * (Real.log Y + 1) + C) / Y := by
    have hd : ∀ u ∈ Ici Y,
        HasDerivAt (fun v : ℝ => -(2 * (c * (Real.log v + 1) + C)) / v)
          (2 * (c * Real.log u + C) / u^2) u := by
      intro u hu
      have hu0 : 0 < u := zero_lt_one.trans (hY.trans_le hu)
      convert! (((((Real.hasDerivAt_log hu0.ne').add_const 1).const_mul c).add_const
        C).const_mul 2).neg.div (hasDerivAt_id u) hu0.ne' using 1
      simp only [Pi.neg_apply, id_eq]
      field_simp
      ring
    have htlog : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have ht : Tendsto (fun u : ℝ => -(2 * (c * (Real.log u + 1) + C)) / u)
        atTop (𝓝 0) := by
      convert! ((htlog.const_mul (2*c)).add
        (tendsto_inv_atTop_zero.const_mul (2*(c+C)))).neg using 1
      · ext u
        simp only [div_eq_mul_inv]
        ring
      · simp
    have hn : ∀ u ∈ Ioi Y, 0 ≤ 2 * (c * Real.log u + C) / u^2 := by
      intro u hu
      have hlog : 0 ≤ Real.log u := (Real.log_pos (hY.trans hu)).le
      positivity
    exact ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn ht,
      by simpa only [zero_sub, neg_div, neg_neg] using
        integral_Ioi_of_hasDerivAt_of_nonneg' hd hn ht⟩

  /- Arbitrary finite high-frequency sets are bounded by the original full count.
     In particular no tail sum or tail integrability hypothesis is assumed. -/

  have finite_high_inverse_square_bound (s : Finset ι) (γ m : ι → ℝ)
      (hfinite : ∀ u : ℝ, Set.Finite {i | γ i < u}) {L Y c C : ℝ}
      (hL : 1 < L) (hLY : L ≤ Y) (hm : ∀ i, 0 ≤ m i)
      (hc : 0 ≤ c) (hC : 0 ≤ C)
      (hhigh : ∀ i ∈ s, Y ≤ γ i)
      (hcount : ∀ u, L ≤ u → strictCount γ m hfinite u ≤ c*u*Real.log u+C*u) :
      ∑ i ∈ s, m i / (γ i)^2 ≤ 2 * (c*(Real.log Y+1)+C) / Y := by
    classical
    have hY : 1 < Y := hL.trans_le hLY
    have hY0 : 0 < Y := zero_lt_one.trans hY
    let kernel := fun (i : ι) (u : ℝ) =>
      if γ i < u then 2 * m i / u^3 else 0
    have hk (i : ι) : IntegrableOn (kernel i) (Ioi Y) := by
      have h := (inverse_cube_integral hY0 (hm i)).1.indicator (t := Ioi (γ i)) measurableSet_Ioi
      convert! h using 1
    have heach (i : ι) (hi : i ∈ s) :
        (∫ u in Ioi Y, kernel i u) = m i / (γ i)^2 := by
      change (∫ u in Ioi Y, (Ioi (γ i)).indicator (fun u => 2*m i/u^3) u) = _
      rw [setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr (Ioi_subset_Ioi (hhigh i hi))]
      exact (inverse_cube_integral (hY0.trans_le (hhigh i hi)) (hm i)).2
    have hsint : IntegrableOn (fun u : ℝ => ∑ i ∈ s, kernel i u) (Ioi Y) :=
      integrable_finsetSum s (fun i _ => hk i)
    have hmaj := count_majorant_integral hY hc hC
    have hcomp (u : ℝ) (hu : u ∈ Ioi Y) :
        (∑ i ∈ s, kernel i u) ≤ 2*(c*Real.log u+C)/u^2 := by
      have hu0 : 0 < u := hY0.trans hu
      have hsub : s.filter (fun i => γ i < u) ⊆ realCutoff γ hfinite u := by
        intro i hi
        simpa only [realCutoff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
          (Finset.mem_filter.mp hi).2
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hm i)
      have heq : (∑ i ∈ s, kernel i u) =
          2 * (∑ i ∈ s.filter (fun i => γ i < u), m i) / u^3 := by
        rw [← Finset.sum_filter]
        rw [← Finset.sum_div, ← Finset.mul_sum]
      rw [heq]
      apply (div_le_iff₀ (pow_pos hu0 3)).mpr
      have hn := hsum.trans (hcount u (hLY.trans hu.le))
      change (∑ i ∈ s.filter (fun i => γ i < u), m i) ≤ _ at hn
      have heq2 : 2*(c*Real.log u+C)/u^2*u^3 = 2*(c*u*Real.log u+C*u) := by
        field_simp
      rw [heq2]
      linarith
    have hineq := setIntegral_mono_on hsint hmaj.1 measurableSet_Ioi hcomp
    rw [integral_finsetSum s (fun i _ => hk i), hmaj.2] at hineq
    rw [Finset.sum_congr rfl heach] at hineq
    exact hineq


  /- Summability is produced from the same finite bounds, including the moving
     endpoint ordinate. The cube tail uses its extra factor 1/gamma <= 1/Y. -/

  have high_inverse_power_tails (γ m : ι → ℝ)
      (hfinite : ∀ u : ℝ, Set.Finite {i | γ i < u}) {L Y c C : ℝ}
      (hL : 1 < L) (hLY : L ≤ Y) (hm : ∀ i, 0 ≤ m i) (hc : 0 ≤ c)
      (hcount : ∀ u, L ≤ u →
        |strictCount γ m hfinite u - c*u*Real.log u| ≤ C*u) :
      Summable (fun i => if Y ≤ γ i then m i / (γ i)^2 else 0) ∧
      (∑' i, if Y ≤ γ i then m i / (γ i)^2 else 0) ≤
        2*(c*(Real.log Y+1)+C)/Y ∧
      Summable (fun i => if Y ≤ γ i then m i / (γ i)^3 else 0) ∧
      (∑' i, if Y ≤ γ i then m i / (γ i)^3 else 0) ≤
        2*(c*(Real.log Y+1)+C)/Y^2 := by
    classical
    have hL0 : 0 < L := zero_lt_one.trans hL
    have hY0 : 0 < Y := hL0.trans_le hLY
    have hC : 0 ≤ C := by
      have h := (abs_nonneg (strictCount γ m hfinite L - c*L*Real.log L)).trans
        (hcount L le_rfl)
      nlinarith
    have hupper (u : ℝ) (hu : L ≤ u) :
        strictCount γ m hfinite u ≤ c*u*Real.log u+C*u := by
      have h := (abs_le.mp (hcount u hu)).2
      linarith
    let f := fun i => if Y ≤ γ i then m i / (γ i)^2 else 0
    have hf0 : ∀ i, 0 ≤ f i := by
      intro i
      dsimp only [f]
      split_ifs
      · exact div_nonneg (hm i) (sq_nonneg _)
      · exact le_rfl
    have hfinitebound (s : Finset ι) : ∑ i ∈ s, f i ≤ 2*(c*(Real.log Y+1)+C)/Y := by
      have h := finite_high_inverse_square_bound (s.filter (fun i => Y ≤ γ i)) γ m
        hfinite hL hLY hm hc hC (fun i hi => (Finset.mem_filter.mp hi).2) hupper
      simpa only [Finset.sum_filter, f] using h
    have hfs : Summable f := summable_of_sum_le hf0 hfinitebound
    have hfb : (∑' i, f i) ≤ 2*(c*(Real.log Y+1)+C)/Y :=
      Real.tsum_le_of_sum_le hf0 hfinitebound
    let g := fun i => if Y ≤ γ i then m i / (γ i)^3 else 0
    have hg0 : ∀ i, 0 ≤ g i := by
      intro i
      dsimp only [g]
      split_ifs with hi
      · exact div_nonneg (hm i) (pow_nonneg (hY0.trans_le hi).le _)
      · exact le_rfl
    have hgf (i : ι) : g i ≤ Y⁻¹ * f i := by
      dsimp only [g, f]
      split_ifs with hi
      · have hγ0 := hY0.trans_le hi
        apply (div_le_iff₀ (pow_pos hγ0 3)).mpr
        have heq : Y⁻¹ * (m i / (γ i)^2) * (γ i)^3 = m i * γ i / Y := by
          field_simp
        rw [heq]
        apply (le_div_iff₀ hY0).mpr
        exact mul_le_mul_of_nonneg_left hi (hm i)
      · simp
    have hgs : Summable g := .of_nonneg_of_le hg0 hgf (hfs.mul_left Y⁻¹)
    have hgb : (∑' i, g i) ≤ 2*(c*(Real.log Y+1)+C)/Y^2 := by
      calc
        (∑' i, g i) ≤ ∑' i, Y⁻¹*f i := hgs.tsum_le_tsum hgf (hfs.mul_left Y⁻¹)
        _ = Y⁻¹*(∑' i, f i) := tsum_mul_left
        _ ≤ Y⁻¹*(2*(c*(Real.log Y+1)+C)/Y) :=
          mul_le_mul_of_nonneg_left hfb (inv_nonneg.mpr hY0.le)
        _ = _ := by ring
    exact ⟨hfs, hfb, hgs, hgb⟩

  have phase_weight_count_bounds (γ m : ι → ℝ)
      (hfinite : ∀ u : ℝ, Set.Finite {i | γ i < u}) {L c C : ℝ}
      (hL : 1 < L) (hγ : ∀ i, L ≤ γ i) (hm : ∀ i, 0 ≤ m i) (hc : 0 ≤ c)
      (hcount : ∀ u, L ≤ u →
        |strictCount γ m hfinite u - c*u*Real.log u| ≤ C*u) :
      Summable (phaseWeight γ m) ∧
      Summable (fun i => phaseWeight γ m i * γ i) ∧
      ∀ Y, L ≤ Y →
        (∑' i, if Y ≤ γ i then phaseWeight γ m i else 0) ≤
          2*(c*(Real.log Y+1)+C)/Y^2 ∧
        (∑' i, if Y ≤ γ i then phaseWeight γ m i * γ i else 0) ≤
          2*(c*(Real.log Y+1)+C)/Y ∧
        (∑ i ∈ realCutoff γ hfinite Y, phaseWeight γ m i * (γ i)^4) ≤
          Y^2*(c*Real.log Y+C) := by
    classical
    have hγ0 (i : ι) : 0 < γ i := (zero_lt_one.trans hL).trans_le (hγ i)
    have ha0 (i : ι) : 0 ≤ phaseWeight γ m i := by
      unfold phaseWeight
      exact div_nonneg (hm i) (mul_nonneg (hγ0 i).le (by positivity))
    have hacube (i : ι) : phaseWeight γ m i ≤ m i / (γ i)^3 := by
      unfold phaseWeight
      apply div_le_div_of_nonneg_left (hm i) (pow_pos (hγ0 i) 3)
      nlinarith [hγ0 i]
    have hagamma (i : ι) : phaseWeight γ m i * γ i = m i / (1/4+(γ i)^2) := by
      unfold phaseWeight
      field_simp [(hγ0 i).ne']
    have hasquare (i : ι) : phaseWeight γ m i * γ i ≤ m i / (γ i)^2 := by
      rw [hagamma]
      exact div_le_div_of_nonneg_left (hm i) (sq_pos_of_pos (hγ0 i)) (by linarith)
    have halow (i : ι) : phaseWeight γ m i * (γ i)^4 ≤ m i * γ i := by
      have heq : phaseWeight γ m i * (γ i)^4 = m i * (γ i)^3 / (1/4+(γ i)^2) := by
        unfold phaseWeight
        field_simp
      rw [heq]
      apply (div_le_iff₀ (by positivity : 0 < (1:ℝ)/4+(γ i)^2)).mpr
      nlinarith [mul_nonneg (hm i) (hγ0 i).le]
    have htailL := high_inverse_power_tails γ m hfinite hL le_rfl hm hc hcount
    have hsquare : Summable (fun i => m i / (γ i)^2) := by
      simpa only [if_pos (hγ _)] using htailL.1
    have hcube : Summable (fun i => m i / (γ i)^3) := by
      simpa only [if_pos (hγ _)] using htailL.2.2.1
    have hsa : Summable (phaseWeight γ m) := .of_nonneg_of_le ha0 hacube hcube
    have hsag : Summable (fun i => phaseWeight γ m i * γ i) :=
      .of_nonneg_of_le (fun i => mul_nonneg (ha0 i) (hγ0 i).le) hasquare hsquare
    refine ⟨hsa, hsag, ?_⟩
    intro Y hLY
    have htail := high_inverse_power_tails γ m hfinite hL hLY hm hc hcount
    have hcuba (i : ι) :
        (if Y ≤ γ i then phaseWeight γ m i else 0) ≤
          (if Y ≤ γ i then m i / (γ i)^3 else 0) := by
      split_ifs
      · exact hacube i
      · exact le_rfl
    have hsqag (i : ι) :
        (if Y ≤ γ i then phaseWeight γ m i * γ i else 0) ≤
          (if Y ≤ γ i then m i / (γ i)^2 else 0) := by
      split_ifs
      · exact hasquare i
      · exact le_rfl
    have hta0 (i : ι) : 0 ≤ (if Y ≤ γ i then phaseWeight γ m i else 0) := by
      split_ifs
      · exact ha0 i
      · exact le_rfl
    have htag0 (i : ι) : 0 ≤ (if Y ≤ γ i then phaseWeight γ m i*γ i else 0) := by
      split_ifs
      · exact mul_nonneg (ha0 i) (hγ0 i).le
      · exact le_rfl
    refine ⟨(Summable.tsum_le_tsum hcuba
        (.of_nonneg_of_le hta0 hcuba htail.2.2.1) htail.2.2.1).trans htail.2.2.2,
      (Summable.tsum_le_tsum hsqag
        (.of_nonneg_of_le htag0 hsqag htail.1) htail.1).trans htail.2.1, ?_⟩
    have hupper := (abs_le.mp (hcount Y hLY)).2
    have hsum : (∑ i ∈ realCutoff γ hfinite Y, phaseWeight γ m i*(γ i)^4) ≤
        Y * strictCount γ m hfinite Y := by
      unfold strictCount
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hiy : γ i < Y := by
        simpa only [realCutoff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hi
      calc
        phaseWeight γ m i*(γ i)^4 ≤ m i*γ i := halow i
        _ ≤ m i*Y := mul_le_mul_of_nonneg_left hiy.le (hm i)
        _ = Y*m i := mul_comm _ _
    have hY0 : 0 ≤ Y := (zero_lt_one.trans hL).le.trans hLY
    calc
      _ ≤ Y * strictCount γ m hfinite Y := hsum
      _ ≤ Y * (c*Y*Real.log Y+C*Y) := mul_le_mul_of_nonneg_left (by linarith) hY0
      _ = _ := by ring

  have phase_moment_log_sq_error_bound (γ m : ι → ℝ)
      (hfinite : ∀ u : ℝ, Set.Finite {i | γ i < u}) {L Y c C : ℝ}
      (hL : 1 < L) (hLY : L ≤ Y) (hγ : ∀ i, L ≤ γ i)
      (hm : ∀ i, 0 ≤ m i) (hc : 0 ≤ c)
      (hcount : ∀ u, L ≤ u →
        |strictCount γ m hfinite u - c*u*Real.log u| ≤ C*u) :
      |phaseMoment γ m hfinite Y - c/2*(Real.log Y)^2| ≤
        c*Real.log Y+C+c/2*(Real.log L)^2+C*(Real.log Y-Real.log L)+
          (∑' i, phaseWeight γ m i)/4 := by
    classical
    have hγ0 (i : ι) : 0 < γ i := (zero_lt_one.trans hL).trans_le (hγ i)
    have ha0 (i : ι) : 0 ≤ phaseWeight γ m i := by
      unfold phaseWeight
      exact div_nonneg (hm i) (mul_nonneg (hγ0 i).le (by positivity))
    have hsa := (phase_weight_count_bounds γ m hfinite hL hγ hm hc hcount).1
    have hident : reciprocalMoment γ m hfinite Y - phaseMoment γ m hfinite Y =
        (∑ i ∈ realCutoff γ hfinite Y, phaseWeight γ m i)/4 := by
      unfold reciprocalMoment phaseMoment
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      unfold phaseWeight
      field_simp [(hγ0 i).ne']
      ring
    have hsum0 : 0 ≤ ∑ i ∈ realCutoff γ hfinite Y, phaseWeight γ m i :=
      Finset.sum_nonneg (fun i _ => ha0 i)
    have hsum := hsa.sum_le_tsum (realCutoff γ hfinite Y) (fun i _ => ha0 i)
    have hdiff : |phaseMoment γ m hfinite Y - reciprocalMoment γ m hfinite Y| ≤
        (∑' i, phaseWeight γ m i)/4 := by
      rw [abs_sub_comm, hident, abs_of_nonneg (div_nonneg hsum0 (by norm_num))]
      exact div_le_div_of_nonneg_right hsum (by norm_num)
    have hmom := reciprocal_moment_log_sq_error_bound γ m hfinite hL hLY hγ hm hc hcount
    calc
      _ ≤ |phaseMoment γ m hfinite Y - reciprocalMoment γ m hfinite Y| +
          |reciprocalMoment γ m hfinite Y - c/2*(Real.log Y)^2| := abs_sub_le _ _ _
      _ ≤ (∑' i, phaseWeight γ m i)/4 +
          (c*Real.log Y+C+c/2*(Real.log L)^2+C*(Real.log Y-Real.log L)) :=
        add_le_add hdiff hmom
      _ = _ := by ring

  have cosine_cutoff_error (γ a : ι → ℝ)
      (hfinite : ∀ u : ℝ, Set.Finite {i | γ i < u}) {Y t : ℝ}
      (ha0 : ∀ i, 0 ≤ a i) (hsa : Summable a)
      (hsmall : ∀ i, γ i < Y → |γ i*t| ≤ 1) :
      |phaseCost γ a t - t^2*(∑ i ∈ realCutoff γ hfinite Y, a i*(γ i)^2)| ≤
        t^4*(∑ i ∈ realCutoff γ hfinite Y, a i*(γ i)^4) +
          4*(∑' i, if Y ≤ γ i then a i else 0) := by
    classical
    let cut := realCutoff γ hfinite Y
    have hmem (i : ι) : i ∈ cut ↔ γ i < Y := by
      simp only [cut, realCutoff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    have finite_mask (b : ι → ℝ) : Summable (fun i => if γ i < Y then b i else 0) := by
      apply summable_of_ne_finset_zero (s := cut)
      intro i hi
      simp only [hmem] at hi
      simp only [if_neg hi]
    have mask_sum (b : ι → ℝ) :
        (∑' i, if γ i < Y then b i else 0) = ∑ i ∈ cut, b i := by
      rw [tsum_eq_sum (s := cut) (fun i hi => by
        simp only [hmem] at hi
        simp only [if_neg hi])]
      exact Finset.sum_congr rfl (fun i hi => if_pos ((hmem i).mp hi))
    let p := fun i => 2*a i*(1-Real.cos (γ i*t))
    have hpbound (i : ι) : ‖p i‖ ≤ 4*a i := by
      have hai := ha0 i
      dsimp only [p]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*a i)]
      have hcos : |1-Real.cos (γ i*t)| ≤ 2 := abs_le.mpr
        ⟨by linarith [Real.cos_le_one (γ i*t)], by linarith [Real.neg_one_le_cos (γ i*t)]⟩
      calc
        2*a i*|1-Real.cos (γ i*t)| ≤ 2*a i*2 :=
          mul_le_mul_of_nonneg_left hcos (by positivity)
        _ = _ := by ring
    have hsp : Summable p := (hsa.mul_left 4).of_norm_bounded hpbound
    let corr := fun i => if γ i < Y then t^2*a i*(γ i)^2 else 0
    let low := fun i => if γ i < Y then t^4*a i*(γ i)^4 else 0
    let high := fun i => if Y ≤ γ i then a i else 0
    have hshigh : Summable high := .of_nonneg_of_le
      (fun i => by dsimp only [high]; split_ifs; exact ha0 i; exact le_rfl)
      (fun i => by dsimp only [high]; split_ifs; exact le_rfl; exact ha0 i) hsa
    have hbound (i : ι) : ‖p i-corr i‖ ≤ low i+4*high i := by
      have hai := ha0 i
      by_cases hi : γ i < Y
      · dsimp only [p, corr, low, high]
        simp only [if_pos hi, if_neg (not_le.mpr hi), mul_zero, add_zero, Real.norm_eq_abs]
        have heq : 2*a i*(1-Real.cos (γ i*t))-t^2*a i*(γ i)^2 =
            -(2*a i*(Real.cos (γ i*t)-(1-(γ i*t)^2/2))) := by ring
        rw [heq, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*a i)]
        have hcos := Real.cos_bound (hsmall i hi)
        rw [(by decide : Even (4:ℕ)).pow_abs] at hcos
        have hmul := mul_le_mul_of_nonneg_left hcos (by positivity : 0 ≤ 2*a i)
        have hnonneg := mul_nonneg hai ((by decide : Even (4:ℕ)).pow_nonneg (γ i*t))
        calc
          _ ≤ 2*a i*((γ i*t)^4*(5/96)) := hmul
          _ = (2*(5/96))*(a i*(γ i*t)^4) := by ring
          _ ≤ 1*(a i*(γ i*t)^4) :=
            mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)*(5/96) ≤ 1) hnonneg
          _ = _ := by ring
      · dsimp only [corr, low, high]
        simp only [if_neg hi, if_pos (le_of_not_gt hi), sub_zero, zero_add]
        exact hpbound i
    have hsb : Summable (fun i => low i+4*high i) :=
      (finite_mask (fun i => t^4*a i*(γ i)^4)).add (hshigh.mul_left 4)
    have hnorm := tsum_of_norm_bounded hsb.hasSum hbound
    have hscorr : Summable corr := finite_mask (fun i => t^2*a i*(γ i)^2)
    rw [hsp.tsum_sub hscorr,
      (finite_mask (fun i => t^4*a i*(γ i)^4)).tsum_add (hshigh.mul_left 4),
      tsum_mul_left] at hnorm
    have hcorrsum : (∑' i, corr i) = t^2*(∑ i ∈ cut, a i*(γ i)^2) := by
      rw [mask_sum]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hlowsum : (∑' i, low i) = t^4*(∑ i ∈ cut, a i*(γ i)^4) := by
      rw [mask_sum]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hcorrsum, hlowsum, Real.norm_eq_abs] at hnorm
    exact hnorm

  have count_to_adaptive_cosine (γ m : ι → ℝ)
      (hfinite : ∀ u : ℝ, Set.Finite {i | γ i < u}) {L c C t : ℝ}
      (hL : 1 < L) (hγ : ∀ i, L ≤ γ i) (hm : ∀ i, 0 ≤ m i) (hc : 0 ≤ c)
      (hcount : ∀ u, L ≤ u →
        |strictCount γ m hfinite u - c*u*Real.log u| ≤ C*u)
      (ht : 0 < |t|) (htsmall : L*|t| ≤ 1) :
      let Y := |t|⁻¹
      |phaseCost γ (phaseWeight γ m) t - t^2*phaseMoment γ m hfinite Y| ≤
        t^2*(9*c*Real.log Y+8*c+9*C) ∧
      |phaseCost γ (phaseWeight γ m) t - c/2*t^2*(Real.log Y)^2| ≤
        t^2*(9*c*Real.log Y+8*c+9*C+
          momentErrorBound L Y c C (∑' i, phaseWeight γ m i)) := by
    classical
    let Y := |t|⁻¹
    change _ ∧ _
    have htne : t ≠ 0 := by simpa only [abs_pos] using ht
    have hL0 : 0 < L := zero_lt_one.trans hL
    have hLY : L ≤ Y := by
      dsimp only [Y]
      rw [← one_div, le_div_iff₀ ht]
      exact htsmall
    have hγ0 (i : ι) : 0 < γ i := hL0.trans_le (hγ i)
    have ha0 (i : ι) : 0 ≤ phaseWeight γ m i := by
      unfold phaseWeight
      exact div_nonneg (hm i) (mul_nonneg (hγ0 i).le (by positivity))
    have hw := phase_weight_count_bounds γ m hfinite hL hγ hm hc hcount
    have hsmall (i : ι) (hi : γ i < Y) : |γ i*t| ≤ 1 := by
      rw [abs_mul, abs_of_pos (hγ0 i)]
      calc
        γ i*|t| ≤ Y*|t| := mul_le_mul_of_nonneg_right hi.le ht.le
        _ = 1 := inv_mul_cancel₀ ht.ne'
    have hcut := cosine_cutoff_error γ (phaseWeight γ m) hfinite ha0 hw.1 hsmall
    have hlow := (hw.2.2 Y hLY).2.2
    have hhigh := (hw.2.2 Y hLY).1
    have hYpow : Y^2 = (t^2)⁻¹ := by
      dsimp only [Y]
      rw [inv_pow, sq_abs]
    have hscale : t^4*(Y^2*(c*Real.log Y+C)) +
        4*(2*(c*(Real.log Y+1)+C)/Y^2) = t^2*(9*c*Real.log Y+8*c+9*C) := by
      rw [hYpow]
      field_simp
      ring
    have herror : |phaseCost γ (phaseWeight γ m) t - t^2*phaseMoment γ m hfinite Y| ≤
        t^2*(9*c*Real.log Y+8*c+9*C) := by
      calc
        _ ≤ t^4*(∑ i ∈ realCutoff γ hfinite Y, phaseWeight γ m i*(γ i)^4) +
            4*(∑' i, if Y ≤ γ i then phaseWeight γ m i else 0) := hcut
        _ ≤ t^4*(Y^2*(c*Real.log Y+C)) + 4*(2*(c*(Real.log Y+1)+C)/Y^2) :=
          add_le_add (mul_le_mul_of_nonneg_left hlow ((by decide : Even (4:ℕ)).pow_nonneg t))
            (mul_le_mul_of_nonneg_left hhigh (by norm_num))
        _ = _ := hscale
    refine ⟨herror, ?_⟩
    have hmom := phase_moment_log_sq_error_bound γ m hfinite hL hLY hγ hm hc hcount
    have hmomscaled : |t^2*phaseMoment γ m hfinite Y-c/2*t^2*(Real.log Y)^2| ≤
        t^2*momentErrorBound L Y c C (∑' i, phaseWeight γ m i) := by
      rw [show t^2*phaseMoment γ m hfinite Y-c/2*t^2*(Real.log Y)^2 =
        t^2*(phaseMoment γ m hfinite Y-c/2*(Real.log Y)^2) by ring,
        abs_mul, abs_of_nonneg (sq_nonneg t)]
      exact mul_le_mul_of_nonneg_left hmom (sq_nonneg t)
    calc
      _ ≤ |phaseCost γ (phaseWeight γ m) t-t^2*phaseMoment γ m hfinite Y| +
          |t^2*phaseMoment γ m hfinite Y-c/2*t^2*(Real.log Y)^2| := abs_sub_le _ _ _
      _ ≤ t^2*(9*c*Real.log Y+8*c+9*C) +
          t^2*momentErrorBound L Y c C (∑' i, phaseWeight γ m i) := add_le_add herror hmomscaled
      _ = _ := by ring

  have sine_cutoff_error (γ a : ι → ℝ)
      (hfinite : ∀ u : ℝ, Set.Finite {i | γ i < u}) {Y t : ℝ}
      (ha0 : ∀ i, 0 ≤ a i) (hγ0 : ∀ i, 0 ≤ γ i)
      (hsag : Summable (fun i => a i*γ i)) :
      |phaseSlope γ a t - 2*t*(∑ i ∈ realCutoff γ hfinite Y, a i*(γ i)^2)| ≤
        |t|^3*(∑ i ∈ realCutoff γ hfinite Y, a i*(γ i)^4) +
          2*(∑' i, if Y ≤ γ i then a i*γ i else 0) := by
    classical
    let cut := realCutoff γ hfinite Y
    have hmem (i : ι) : i ∈ cut ↔ γ i < Y := by
      simp only [cut, realCutoff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    have finite_mask (b : ι → ℝ) : Summable (fun i => if γ i < Y then b i else 0) := by
      apply summable_of_ne_finset_zero (s := cut)
      intro i hi
      simp only [hmem] at hi
      simp only [if_neg hi]
    have mask_sum (b : ι → ℝ) :
        (∑' i, if γ i < Y then b i else 0) = ∑ i ∈ cut, b i := by
      rw [tsum_eq_sum (s := cut) (fun i hi => by
        simp only [hmem] at hi
        simp only [if_neg hi])]
      exact Finset.sum_congr rfl (fun i hi => if_pos ((hmem i).mp hi))
    let p := fun i => 2*a i*γ i*Real.sin (γ i*t)
    have hag0 (i : ι) : 0 ≤ a i*γ i := mul_nonneg (ha0 i) (hγ0 i)
    have hpbound (i : ι) : ‖p i‖ ≤ 2*(a i*γ i) := by
      have hai := ha0 i
      have hgi := hγ0 i
      dsimp only [p]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*a i*γ i)]
      calc
        2*a i*γ i*|Real.sin (γ i*t)| ≤ 2*a i*γ i*1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
        _ = _ := by ring
    have hsp : Summable p := (hsag.mul_left 2).of_norm_bounded hpbound
    let corr := fun i => if γ i < Y then 2*t*a i*(γ i)^2 else 0
    let low := fun i => if γ i < Y then |t|^3*a i*(γ i)^4 else 0
    let high := fun i => if Y ≤ γ i then a i*γ i else 0
    have hshigh : Summable high := .of_nonneg_of_le
      (fun i => by dsimp only [high]; split_ifs; exact hag0 i; exact le_rfl)
      (fun i => by dsimp only [high]; split_ifs; exact le_rfl; exact hag0 i) hsag
    have hbound (i : ι) : ‖p i-corr i‖ ≤ low i+2*high i := by
      have hai := ha0 i
      have hgi := hγ0 i
      by_cases hi : γ i < Y
      · dsimp only [p, corr, low, high]
        simp only [if_pos hi, if_neg (not_le.mpr hi), mul_zero, add_zero, Real.norm_eq_abs]
        have heq : 2*a i*γ i*Real.sin (γ i*t)-2*t*a i*(γ i)^2 =
            2*a i*γ i*(Real.sin (γ i*t)-γ i*t) := by ring
        rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*a i*γ i)]
        have hsin : |Real.sin (γ i*t)-γ i*t| ≤ |γ i*t|^3/6 := by
          rw [abs_sub_comm]
          exact Real.abs_sub_sin_le _
        have hmul := mul_le_mul_of_nonneg_left hsin (by positivity : 0 ≤ 2*a i*γ i)
        rw [abs_mul, abs_of_nonneg hgi, mul_pow] at hmul
        calc
          _ ≤ 2*a i*γ i*((γ i)^3*|t|^3/6) := hmul
          _ = (1/3)*(|t|^3*a i*(γ i)^4) := by ring
          _ ≤ 1*(|t|^3*a i*(γ i)^4) :=
            mul_le_mul_of_nonneg_right (by norm_num : (1:ℝ)/3 ≤ 1) (by positivity)
          _ = _ := by ring
      · dsimp only [corr, low, high]
        simp only [if_neg hi, if_pos (le_of_not_gt hi), sub_zero, zero_add]
        exact hpbound i
    have hslow := finite_mask (fun i => |t|^3*a i*(γ i)^4)
    have hsb : Summable (fun i => low i+2*high i) := hslow.add (hshigh.mul_left 2)
    have hnorm := tsum_of_norm_bounded hsb.hasSum hbound
    have hscorr : Summable corr := finite_mask (fun i => 2*t*a i*(γ i)^2)
    rw [hsp.tsum_sub hscorr, hslow.tsum_add (hshigh.mul_left 2), tsum_mul_left] at hnorm
    have hcorrsum : (∑' i, corr i) = 2*t*(∑ i ∈ cut, a i*(γ i)^2) := by
      rw [mask_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hlowsum : (∑' i, low i) = |t|^3*(∑ i ∈ cut, a i*(γ i)^4) := by
      rw [mask_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hcorrsum, hlowsum, Real.norm_eq_abs] at hnorm
    exact hnorm

  /- C1 uses only the summable first derivative majorant; there is no attempted
     exchange of the second derivative series. -/

  have phase_has_derivative (γ a : ι → ℝ)
      (ha0 : ∀ i, 0 ≤ a i) (hγ0 : ∀ i, 0 ≤ γ i)
      (hsag : Summable (fun i => a i*γ i)) :
      (∀ t, HasDerivAt (phaseCost γ a) (phaseSlope γ a t) t) ∧
        Continuous (phaseSlope γ a) := by
    have hd (i : ι) (t : ℝ) :
        HasDerivAt (fun v => 2*a i*(1-Real.cos (γ i*v)))
          (2*a i*γ i*Real.sin (γ i*t)) t := by
      convert! ((hasDerivAt_const t (1:ℝ)).sub
        ((Real.hasDerivAt_cos (γ i*t)).comp t
          ((hasDerivAt_id t).const_mul (γ i)))).const_mul (2*a i) using 1
      ring
    have hb (i : ι) (t : ℝ) : ‖2*a i*γ i*Real.sin (γ i*t)‖ ≤ 2*(a i*γ i) := by
      have hai := ha0 i
      have hgi := hγ0 i
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*a i*γ i)]
      calc
        2*a i*γ i*|Real.sin (γ i*t)| ≤ 2*a i*γ i*1 :=
          mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
        _ = _ := by ring
    have hzero : Summable (fun i => 2*a i*(1-Real.cos (γ i*(0:ℝ)))) := by simp
    refine ⟨fun t => hasDerivAt_tsum (hsag.mul_left 2) hd hb hzero t, ?_⟩
    exact continuous_tsum (fun i => continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))) (hsag.mul_left 2) hb

  have count_to_adaptive_sine (γ m : ι → ℝ)
      (hfinite : ∀ u : ℝ, Set.Finite {i | γ i < u}) {L c C t : ℝ}
      (hL : 1 < L) (hγ : ∀ i, L ≤ γ i) (hm : ∀ i, 0 ≤ m i) (hc : 0 ≤ c)
      (hcount : ∀ u, L ≤ u →
        |strictCount γ m hfinite u - c*u*Real.log u| ≤ C*u)
      (ht : 0 < |t|) (htsmall : L*|t| ≤ 1) :
      let Y := |t|⁻¹
      HasDerivAt (phaseCost γ (phaseWeight γ m)) (phaseSlope γ (phaseWeight γ m) t) t ∧
      Continuous (phaseSlope γ (phaseWeight γ m)) ∧
      |phaseSlope γ (phaseWeight γ m) t - 2*t*phaseMoment γ m hfinite Y| ≤
        |t| *(5*c*Real.log Y+4*c+5*C) ∧
      |phaseSlope γ (phaseWeight γ m) t - c*t*(Real.log Y)^2| ≤
        |t| *(5*c*Real.log Y+4*c+5*C+
          2*momentErrorBound L Y c C (∑' i, phaseWeight γ m i)) := by
    classical
    let Y := |t|⁻¹
    change _ ∧ _ ∧ _ ∧ _
    have hL0 : 0 < L := zero_lt_one.trans hL
    have hLY : L ≤ Y := by
      dsimp only [Y]
      rw [← one_div, le_div_iff₀ ht]
      exact htsmall
    have hγ0 (i : ι) : 0 < γ i := hL0.trans_le (hγ i)
    have ha0 (i : ι) : 0 ≤ phaseWeight γ m i := by
      unfold phaseWeight
      exact div_nonneg (hm i) (mul_nonneg (hγ0 i).le (by positivity))
    have hw := phase_weight_count_bounds γ m hfinite hL hγ hm hc hcount
    have hd := phase_has_derivative γ (phaseWeight γ m) ha0 (fun i => (hγ0 i).le) hw.2.1
    have hcut := sine_cutoff_error (Y := Y) (t := t) γ (phaseWeight γ m) hfinite ha0
      (fun i => (hγ0 i).le) hw.2.1
    have hlow := (hw.2.2 Y hLY).2.2
    have hhigh := (hw.2.2 Y hLY).2.1
    have hscale : |t|^3*(Y^2*(c*Real.log Y+C)) +
        2*(2*(c*(Real.log Y+1)+C)/Y) = |t| *(5*c*Real.log Y+4*c+5*C) := by
      dsimp only [Y]
      field_simp
      ring
    have herror : |phaseSlope γ (phaseWeight γ m) t - 2*t*phaseMoment γ m hfinite Y| ≤
        |t| *(5*c*Real.log Y+4*c+5*C) := by
      calc
        _ ≤ |t|^3*(∑ i ∈ realCutoff γ hfinite Y, phaseWeight γ m i*(γ i)^4) +
            2*(∑' i, if Y ≤ γ i then phaseWeight γ m i*γ i else 0) := hcut
        _ ≤ |t|^3*(Y^2*(c*Real.log Y+C)) + 2*(2*(c*(Real.log Y+1)+C)/Y) :=
          add_le_add (mul_le_mul_of_nonneg_left hlow (pow_nonneg ht.le 3))
            (mul_le_mul_of_nonneg_left hhigh (by norm_num))
        _ = _ := hscale
    refine ⟨hd.1 t, hd.2, herror, ?_⟩
    have hmom := phase_moment_log_sq_error_bound γ m hfinite hL hLY hγ hm hc hcount
    have hmomscaled : |2*t*phaseMoment γ m hfinite Y-c*t*(Real.log Y)^2| ≤
        2*|t| *momentErrorBound L Y c C (∑' i, phaseWeight γ m i) := by
      rw [show 2*t*phaseMoment γ m hfinite Y-c*t*(Real.log Y)^2 =
        2*t*(phaseMoment γ m hfinite Y-c/2*(Real.log Y)^2) by ring,
        abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact mul_le_mul_of_nonneg_left hmom (mul_nonneg (by norm_num) ht.le)
    calc
      _ ≤ |phaseSlope γ (phaseWeight γ m) t-2*t*phaseMoment γ m hfinite Y| +
          |2*t*phaseMoment γ m hfinite Y-c*t*(Real.log Y)^2| := abs_sub_le _ _ _
      _ ≤ |t| *(5*c*Real.log Y+4*c+5*C) +
          2*|t| *momentErrorBound L Y c C (∑' i, phaseWeight γ m i) := add_le_add herror hmomscaled
      _ = _ := by ring

  have hγ0 (i : ι) : 0 < γ i := (zero_lt_one.trans hL).trans_le (hγ i)
  have ha0 (i : ι) : 0 ≤ phaseWeight γ m i := by
    unfold phaseWeight
    exact div_nonneg (hm i) (mul_nonneg (hγ0 i).le (by positivity))
  have hw := phase_weight_count_bounds γ m hfinite hL hγ hm hc hcount
  have hd := phase_has_derivative γ (phaseWeight γ m) ha0 (fun i => (hγ0 i).le) hw.2.1
  refine ⟨hw.1,hw.2.1,hd.1,hd.2,?_⟩
  intro t ht htsmall
  have hcos := count_to_adaptive_cosine γ m hfinite hL hγ hm hc hcount ht htsmall
  have hsin := count_to_adaptive_sine γ m hfinite hL hγ hm hc hcount ht htsmall
  exact ⟨hcos.1,hsin.2.2.1,hcos.2,hsin.2.2.2⟩

#print axioms logarithmic_phase_stiffness
end D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness
