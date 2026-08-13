/- GID: D5/S3/Weil/ZetaPntBounds/ZetaBoundsAnalytic
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/ZetaBoundsAnalytic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the analytic foundation of the Zeta23 zeta bounds. -/

/- Ported from anthropics/zeta-23-lean commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510.
   Modified by trureturing on 2026-08-14: repository routing and module splitting. -/
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/ZetaBounds.lean.
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: removed the Architect blueprint tooling (import Architect,
blueprint_comment blocks, @[blueprint ...] attributes), redirected intra-project
imports to routed D5.S3.Weil modules, and added a (name := ...) tag to local notation.
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/
import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import D5.S3.Weil.ZetaPntBase.Auxiliary
import D5.S3.Weil.ZetaPntBase.Fourier
import D5.S3.Weil.ZetaPntBase.LogBasic
import D5.S3.Weil.ZetaPntBase.ResidueCalculus
import D5.S3.Weil.ZetaPntBase.EulerMaclaurin

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]

lemma one_div_cpow_eq_cpow_neg (x s : ℂ) : 1 / x ^ s = x ^ (-s) := by
  convert div_cpow_eq_cpow_neg 1 x s using 1; simp

lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]

lemma div_rpow_neg_eq_rpow_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (-s) / y ^ (-s) = (y / x) ^ s := by
  rw [div_eq_mul_inv, Real.rpow_neg hx, Real.rpow_neg hy, Real.div_rpow hy hx]; field_simp

lemma div_rpow_eq_rpow_div_neg {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ s / y ^ s = (y / x) ^ (-s) := by
  convert div_rpow_neg_eq_rpow_div (s := -s) hx hy using 1; simp only [neg_neg]

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
  -- Step 1.  `(s-p) f s` is bounded on some punctured nbhd `V`.
  have h_event : ∀ᶠ s in 𝓝[≠] p, ‖(s - p) * f s - A‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_nhds :
      ∀ᶠ s in 𝓝 p, s ≠ p → ‖(s - p) * f s - A‖ < 1 := by
    exact (eventually_nhdsWithin_iff).1 h_event
  rcases (eventually_nhds_iff.1 h_event_nhds) with ⟨V₀, hV₀_mem, hV₀_prop⟩
  have h_bound :
      ∀ s, s ∈ V₀ \ {p} → ‖(s - p) * f s‖ ≤ ‖A‖ + 1 := by
    intro s hs
    rcases hs with ⟨hV₀, hsne⟩
    calc ‖(s - p) * f s‖ = ‖((s - p) * f s - A) + A‖ := by
          ring_nf
        _ ≤ ‖(s - p) * f s - A‖ + ‖A‖ := norm_add_le ((s - p) * f s - A) A
        _ ≤ 1 + ‖A‖ := add_le_add_left (le_of_lt (hV₀_mem s hV₀ hsne)) ‖A‖
        _ = ‖A‖ + 1 := add_comm 1 ‖A‖
  have h_bdd :
      BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (V₀ \ {p})) := by
    refine ⟨‖A‖ + 1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h_bound s hs
  -- From now on work inside `W = V₀ ∩ U`,   still a nbhd of `p`.
  set W : Set ℂ := V₀ ∩ U with hW_def
  have hW_mem : (W : Set ℂ) ∈ 𝓝 p := inter_mem (IsOpen.mem_nhds hV₀_prop.1 hV₀_prop.2) hU
  have h_subset_V₀ : (W \ {p}) ⊆ (V₀ \ {p}) := by
    intro z hz; exact ⟨hz.1.1, hz.2⟩
  have h_prod_holo : HolomorphicOn (fun z ↦ (z - p) * f z) (W \ {p}) := by
    have h_id : HolomorphicOn (fun z : ℂ ↦ z - p) (W \ {p}) :=
      Differentiable.differentiableOn (Differentiable.sub_const differentiable_fun_id p)
    have hfW : HolomorphicOn f (W \ {p}) := by
      apply hf.mono
      exact Set.sdiff_subset_sdiff_left inter_subset_right
    simpa using! h_id.mul hfW
  have h_bdd_W : BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (W \ {p})) :=
    h_bdd.mono (image_mono h_subset_V₀)
  -- Step 2.  Extend the product across `p`; obtain holomorphic `g`.
  obtain ⟨g, hg_holo, hg_eq⟩ :=
    existsDifferentiableOn_of_bddAbove hW_mem h_prod_holo h_bdd_W
  have h_event_eq :
      (fun z ↦ g z) =ᶠ[𝓝[≠] p] fun z ↦ (z - p) * f z := by
    have hW_diff_mem : (W \ {p} : Set ℂ) ∈ 𝓝[≠] p :=
      sdiff_mem_nhdsWithin_compl hW_mem {p}
    exact (hg_eq.eventuallyEq_of_mem hW_diff_mem).symm
  have h_tendsto_gA : Tendsto g (𝓝[≠] p) (𝓝 A) :=
      h_limit.congr' (id (EventuallyEq.symm h_event_eq))
  have hpW : p ∈ W := by
    exact mem_of_mem_nhds hW_mem
  have h_cont_g : ContinuousAt g p := by
    apply (hg_holo.continuousOn.continuousWithinAt hpW).continuousAt hW_mem
  have h_tendsto_gp : Tendsto g (𝓝[≠] p) (𝓝 (g p)) :=
    h_cont_g.tendsto.mono_left inf_le_left
  have g_p_eq : g p = A :=
    tendsto_nhds_unique' (NormedField.nhdsNE_neBot p) h_tendsto_gp h_tendsto_gA
  let q : ℂ → ℂ := fun z ↦ (g z - A) / (z - p)
  have h_deriv : HasDerivAt g (deriv g p) p := by
    exact DifferentiableOn.hasDerivAt hg_holo hW_mem
  have h_q_limit : Tendsto q (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    unfold slope at h_deriv
    simp only [vsub_eq_sub, smul_eq_mul, inv_mul_eq_div, g_p_eq] at h_deriv
    exact h_deriv
  have h_event_q : ∀ᶠ z in 𝓝[≠] p, ‖q z - deriv g p‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_q_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_q_nhds : ∀ᶠ z in 𝓝 p, z ≠ p → ‖q z - deriv g p‖ < 1 := by
    simpa using (eventually_nhdsWithin_iff).1 h_event_q
  rcases (eventually_nhds_iff.1 h_event_q_nhds) with
    ⟨V₁, hV₁_mem, hV₁_prop⟩
  have h_q_bound :
      ∀ z, z ∈ V₁ \ {p} → ‖q z‖ ≤ ‖deriv g p‖ + 1 := by
    intro z hz
    rcases hz with ⟨hV₁, hz_ne⟩
    calc ‖q z‖ = ‖(q z - deriv g p) + (deriv g p)‖ := by
          ring_nf
        _ ≤ ‖q z - deriv g p‖ + ‖deriv g p‖ := norm_add_le (q z - deriv g p) (deriv g p)
        _ ≤ 1 + ‖deriv g p‖  := add_le_add_left (le_of_lt (hV₁_mem z hV₁ hz_ne)) ‖deriv g p‖
        _ = ‖deriv g p‖ + 1 := add_comm 1 ‖deriv g p‖
  -- Step 4.  Relate `f` to `q` and pass the bound.
  have h_eq_diff :
      EqOn (fun z ↦ f z - A * (z - p)⁻¹) q (W \ {p}) := by
    intro z hz
    simp only
    have hz_ne : (z - p) ≠ 0 := sub_ne_zero.mpr hz.2
    have hgz : g z = (z - p) * f z := by
      exact id (EqOn.symm hg_eq) hz
    simp only [hgz, q]
    field_simp
  apply IsBigO_to_BddAbove
  rw [isBigO_iff]
  use ‖deriv g p‖ + 1
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [IsOpen.mem_nhds hV₁_prop.1 hV₁_prop.2, hW_mem] with z hV₁ hW z_ne_p
  specialize h_eq_diff ⟨ hW, z_ne_p⟩
  simp only [Pi.sub_apply, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary,
    mul_one] at h_eq_diff ⊢
  rw [h_eq_diff]
  exact h_q_bound _ ⟨hV₁, z_ne_p⟩

theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz

theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt

theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  have zeta_holc : HolomorphicOn ζ (univ \ {1}) := by
    intro y hy
    exact DifferentiableAt.differentiableWithinAt <| differentiableAt_riemannZeta hy.2
  convert ResidueOfTendsTo univ_mem zeta_holc riemannZeta_residue_one using 6
  simp

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too
theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  intro x hx
  apply EventuallyEq.deriv_eq
  filter_upwards [IsOpen.mem_nhds (hU_open.sdiff isClosed_singleton) hx] with t ht using h_eq ht

/- New two theorems to be proven -/

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have U_in_filter : U ∈ 𝓝 p := by
    exact IsOpen.mem_nhds hU hp
  have T := (analyticOn_iff_differentiableOn hU).mpr hf
  have T2 : ContDiffOn ℂ 1 f U :=
      DifferentiableOn.contDiffOn hf hU
  have T3 : ContinuousOn (fun x ↦ ((deriv f) x)) U := by
    apply T2.continuousOn_deriv_of_isOpen hU (by simp)
  have T4 := T3.continuousAt U_in_filter
  have T5 : (deriv f) =O[𝓝 p] (1 : ℂ → ℂ) :=
    T4.norm.isBoundedUnder_le.isBigO_one ℂ
  exact Asymptotics.IsBigO.mono T5 inf_le_left

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_mul hg (by fun_prop)]
  simp

lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  rw [deriv_fun_inv'' (by fun_prop) (by grind)]
  simp
  field

-- Alternative cleaner proof using more direct approach
theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  have h1 : DifferentiableAt ℂ (fun z => (z - p)⁻¹) x := by
    fun_prop (disch := grind)
  rw [deriv_sub hf (h1.const_mul A), deriv_const_mul A h1, deriv_inv_sub hp]
  ring

theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by

  -- Step 1: Rewrite f as the sum of two parts
  have h_decomp : ∀ s, f s = (f s - A * (s - p)⁻¹) + A * (s - p)⁻¹ := by
    intro s
    ring
  -- Get a bound for the first summand
  obtain ⟨M, hM⟩ := f_near_p
  -- Step 2: The second summand A * (s - p)⁻¹ goes to ∞ as s → p
  -- We need to find a neighborhood where |A * (s - p)⁻¹| > M + 1
  have A_norm_pos : 0 < ‖A‖ := norm_pos_iff.mpr A_ne_zero
  -- Choose δ such that for |s - p| < δ, we have |A * (s - p)⁻¹| > M + 1
  let δ := ‖A‖ / (‖M‖ + 1)
  have δ_pos : 0 < δ := by
    refine div_pos A_norm_pos (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)
  -- Find an open neighborhood V contained in both U and the δ-ball around p
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ : ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ Metric.ball p δ := by
    -- rw [mem_nhds_iff] at U_in_nhds
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp U_in_nhds
    let V := W ∩ Metric.ball p δ
    have VNp : V ∈ 𝓝 p := (𝓝 p).inter_mem (IsOpen.mem_nhds hW_open hW_mem)
      (Metric.ball_mem_nhds p δ_pos)
    exact ⟨V, IsOpen.inter hW_open Metric.isOpen_ball, mem_of_mem_nhds VNp,
      inter_subset_inter_left _ hW_sub⟩
  use V, mem_nhds_iff.mpr ⟨V, subset_refl V, hV_open, hV_mem⟩, hV_open
  -- Show f ≠ 0 on V
  intro s hs
  have hs_in_U : s ∈ U := hV_sub hs.1 |>.1
  have hs_near_p : dist s p < δ := hV_sub hs.1 |>.2
  have hs_ne_p : s ≠ p := hs.2
  -- Step 3: Therefore the sum of the two terms has large norm
  rw [h_decomp s]
  -- The first summand is bounded
  have bound_first : ‖f s - A * (s - p)⁻¹‖ ≤ M := by
    apply hM
    exact ⟨s, ⟨hs_in_U, hs_ne_p⟩, rfl⟩
  -- The second summand has large norm
  have large_second : ‖M‖ + 1 < ‖A * (s - p)⁻¹‖ := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne_p))]
    rw [mul_comm, ← lt_div_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)]
    rw [dist_eq_norm_sub] at hs_near_p
    exact hs_near_p
  -- Step 4: Therefore the sum is nonzero near p
  by_contra h_zero
  -- If f s = 0, then the two summands are negatives of each other
  rw [add_eq_zero_iff_eq_neg] at h_zero
  rw [h_zero, norm_neg] at bound_first
  -- But this contradicts our bounds
  have : ‖M‖ + 1 < ‖M‖ := (lt_of_lt_of_le (lt_of_lt_of_le large_second bound_first)
    (Real.le_norm_self M))
  norm_num at this

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by

  have simpleHolo : HolomorphicOn (fun s ↦ A / (s - p)) (U \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by rw [sub_ne_zero]; exact hx
    · rintro s ⟨_, hs⟩ ; exact hs

  have f_minus_pole_is_holomorphic : HolomorphicOn (f - (fun s ↦ A * (s - p)⁻¹)) (U \ {p}) := by
    exact (DifferentiableOn.sub_iff_right holc).mpr simpleHolo

  let ⟨g, ⟨g_is_holomorphic, g_is_f_minus_pole⟩⟩ := existsDifferentiableOn_of_bddAbove
    U_in_nhds f_minus_pole_is_holomorphic f_near_p

      /- TODO: Assert that the derivatives match too -/

  let h := (fun _ ↦ A) + g * (fun (s : ℂ) ↦ (s - p))

  have linear_is_holomorphic : HolomorphicOn (fun (s : ℂ ) ↦ (s - p)) U := by
    exact DifferentiableOn.sub_const differentiableOn_id p

  have h_is_holomorphic : HolomorphicOn h U := by
    have T := DifferentiableOn.mul g_is_holomorphic linear_is_holomorphic
    exact DifferentiableOn.const_add A T

  have h_continuous : ContinuousOn h U :=
    by exact DifferentiableOn.continuousOn h_is_holomorphic

  have deriv_h_identity : ∀x ∈ (U \ {p}), (deriv h) x = f x + (deriv f x) * (x - p) := by
    intro x x_in_u_not_p
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff x_in_u_not_p
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2

    have weird : U ∈ 𝓝 x := by
      exact IsOpen.mem_nhds (U_is_open) (x_in_u)

    rw [derivative_const_plus_product, ← g_is_f_minus_pole x_in_u_not_p,
      ← deriv_eqOn_of_eqOn_punctured _ _ U p U_is_open g_is_f_minus_pole x_in_u_not_p,
      deriv_f_minus_A_inv_sub_clean]
    · simp only [Pi.sub_apply]
      have := sub_ne_zero_of_ne x_not_p
      field_simp
      ring
    · apply holc.differentiableAt
      exact Filter.inter_mem weird <| compl_singleton_mem_nhds x_not_p
    · exact x_not_p
    · exact g_is_holomorphic.differentiableAt weird
  have h_identity : ∀x ∈ (U \ {p}), h x = (f x) * (x - p)  := by
    intro x x_in_u_not_p
    have hyp_x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2
    simp only [h, Pi.add_apply, Pi.mul_apply]
    rw [← g_is_f_minus_pole x_in_u_not_p]
    simp only [Pi.sub_apply]
    field [sub_ne_zero.mpr hyp_x_not_p]
  have log_deriv_f_plus_pole_equal_log_deriv_h :
      EqOn (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) ((deriv h) * h⁻¹) (U \ {p}) := by
    simp only [Set.mem_sdiff, mem_singleton_iff, ne_eq, and_imp, Function.comp_apply, Pi.sub_apply,
      DifferentiableOn.sub_iff_right, differentiableOn_const, DifferentiableOn.fun_sub_iff_left,
      holc] at *
    intro x hyp_x
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp hyp_x).2
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff hyp_x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    rw [deriv_h_identity _ x_in_u x_not_p, h_identity _ x_in_u x_not_p]

    /- This is just an identity at this point -/
    field [sub_ne_zero.mpr x_not_p, non_zero x (x_in_u) x_not_p]
  have h_inv_bounded :
      h⁻¹ =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have : ContinuousAt h⁻¹ p := by
      apply ContinuousOn.continuousAt h_continuous U_in_nhds |>.inv₀
      simp [h, A_ne_zero]
    exact Asymptotics.IsBigO.mono (this.norm.isBoundedUnder_le.isBigO_one ℂ) inf_le_left

  have h_deriv_bounded :
        (deriv h) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
          analytic_deriv_bounded_near_point h U_is_open
            (by exact mem_of_mem_nhds U_in_nhds) h_is_holomorphic

  have h_log_deriv_bounded :
    ((deriv h) * h⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
      have T := Asymptotics.IsBigO.mul h_deriv_bounded h_inv_bounded
      exact IsBigO.of_const_mul_right T

  have u_not_p_in_filter : U \ {p} ∈ 𝓝[≠] p := by
    exact sdiff_mem_nhdsWithin_compl U_in_nhds {p}
  have T := Set.EqOn.eventuallyEq_of_mem log_deriv_f_plus_pole_equal_log_deriv_h u_not_p_in_filter
  exact EventuallyEq.trans_isBigO T h_log_deriv_bounded

theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    by
      let ⟨U', ⟨a,b,c⟩⟩ := mem_nhds_iff.mp U_in_nhds
      have W : (U' \ {p}) ⊆ U' := by
        exact Set.sdiff_subset

      have T : (U' \ {p}) ⊆ (U \ {p}) := by
        exact Set.sdiff_subset_sdiff a (subset_refl _)

      refine logDerivResidue' b ?_ ?_ (IsOpen.mem_nhds b c) A_ne_zero ?_
      · intro x hyp_x
        exact non_zero x <| T hyp_x
      · exact DifferentiableOn.mono holc T
      · exact (f_near_p.mono (image_mono (Set.sdiff_subset_sdiff a (subset_refl _))))

lemma BddAbove_to_IsBigO {f : ℂ → ℂ} {p : ℂ}
    {U : Set ℂ} (hU : U ∈ 𝓝 p) (bdd : BddAbove (norm ∘ f '' (U \ {p}))) :
    f =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
  dsimp [BddAbove, upperBounds] at bdd
  rcases bdd with ⟨C, hC⟩

  have h : ∀ x ∈ U \ {p}, ‖f x‖ ≤ C := by
    intro x hx
    have fx_is_norm : ‖f x‖ ∈ norm ∘ f ''(U \ {p}) := by
      exact ⟨x, hx, rfl⟩
    exact hC fx_is_norm

  rw [Asymptotics.isBigO_iff]
  use C
  rw [eventually_nhdsWithin_iff]
  simp only [Set.mem_sdiff, mem_singleton_iff, and_imp, mem_compl_iff, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one] at h ⊢
  filter_upwards [hU] using h

theorem logDerivResidue'' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by
  apply IsBigO_to_BddAbove
  exact logDerivResidue non_zero holc U_in_nhds A_ne_zero f_near_p

theorem ResidueMult {f g : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (g_holc : HolomorphicOn g U) (U_in_nhds : U ∈ 𝓝 p) {A : ℂ}
    (f_near_p : (f - (fun s ↦ A * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    (f * g - (fun s ↦ A * g p * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  -- Add and subtract a term
  have : (f * g - fun s ↦ A * g p * (s - p)⁻¹)
      = (f - A • fun s ↦ (s - p)⁻¹) * g + fun s ↦ (A * (g s - g p) / (s - p)) := by
    ext; simp; ring
  -- Apply to goal
  rw[this]
  have p_in_U : p ∈ U := mem_of_mem_nhds U_in_nhds
  refine Asymptotics.IsBigO.add ?_ ?_
  · rw[← mul_one (1 : ℂ → ℂ)]
    refine Asymptotics.IsBigO.mul f_near_p ?_
    -- Show g is bounded near p
    have g_cont : ContinuousAt g p := by
      -- g is holomorphic on U, p ∈ U, so g is continuous at p
      exact (g_holc.continuousOn.continuousWithinAt p_in_U).continuousAt U_in_nhds
    -- Use continuity to get boundedness
    have := g_cont.norm.isBoundedUnder_le.isBigO_one ℂ
    exact IsBigO.mono this inf_le_left
  · -- Show that (fun s ↦ A * (g s - g p) / (s - p)) =O[𝓝[≠] p] 1

    suffices (fun s ↦ A * ((s - p)⁻¹ * (g s - g p))) =O[𝓝[≠] p] 1 by
      convert! this using 2
      rw[div_eq_mul_inv]
      ring
    apply Asymptotics.IsBigO.const_mul_left

    -- g is differentiable at p since it's holomorphic on U
    have g_diff : HasDerivAt g (deriv g p) p :=
        (DifferentiableOn.differentiableAt g_holc U_in_nhds).hasDerivAt

    rw [hasDerivAt_iff_isLittleO] at g_diff
    apply Asymptotics.IsLittleO.isBigO at g_diff
    have : (fun x' ↦ deriv g p * (x' - p)) =O[𝓝 p] fun x' ↦ x' - p := by
      apply Asymptotics.IsBigO.const_mul_left
      exact Asymptotics.isBigO_refl (fun x ↦ x - p) (𝓝 p)
    have h1 := g_diff.add this
    have h2 : (fun x ↦ g x - g p) =O[𝓝 p] fun x' ↦ x' - p := by
      convert! h1 using 2
      simp
      ring
    refine (Asymptotics.isBigO_mul_iff_isBigO_div ?_).mpr ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx
      exact inv_ne_zero (sub_ne_zero.mpr hx)
    · simp only [div_inv_eq_mul]
      refine Asymptotics.IsBigO.mono ?_ inf_le_left
      simpa

theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  obtain ⟨U,U_in_nhds, hU⟩ := riemannZetaResidue
  have hU' : BddAbove (norm ∘ (ζ - fun s ↦ 1 * (s - 1)⁻¹) '' (U \ {1})) := by
    simp only [Function.comp_apply, Pi.sub_apply, one_mul] at hU ⊢
    exact hU
  obtain ⟨V,V_in_nhds, V_is_open, hV⟩ := nonZeroOfBddAbove U_in_nhds one_ne_zero hU'
  let W := V ∩ interior U
  have hW : ∀ s ∈ W \ {1}, ζ s ≠ 0 := by
    intro s hs
    have s_in_V_diff : s ∈ V \ {1} := ⟨hs.1.1, hs.2⟩
    exact hV s s_in_V_diff
  have ζ_holc: HolomorphicOn ζ (W \ {1}) := by
    intro y hy
    simp only [Set.mem_sdiff, mem_singleton_iff] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy.2
  have W_in_nhds : W ∈ 𝓝 1 := by
    refine inter_mem V_in_nhds ?_
    exact interior_mem_nhds.mpr U_in_nhds
  have := logDerivResidue'' hW ζ_holc W_in_nhds one_ne_zero
  have HW : BddAbove (norm ∘ (ζ - fun s ↦ (s - 1)⁻¹) '' (W \ {1})) := by
    obtain ⟨c, hc⟩ := bddAbove_def.mp hU
    apply bddAbove_def.mpr
    use c
    rintro y ⟨x, x_in_W, fxy⟩
    apply hc
    exact ⟨x, ⟨interior_subset x_in_W.1.2, x_in_W.2⟩, fxy⟩
  simp only [one_mul] at this
  have aux: ∀ a, ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by
    intro a
    calc ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖
         = ‖-((deriv ζ a / ζ a) + (a - 1)⁻¹)‖ := by ring_nf
       _ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by rw [norm_neg]
  simp only [Function.comp_apply, Pi.sub_apply] at hU
  simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, aux]
  apply this HW

theorem riemannZetaLogDerivResidueBigO :
    (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨U, hU, bdd⟩ := riemannZetaLogDerivResidue
  convert BddAbove_to_IsBigO hU bdd using 2
  rw [neg_div]

noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring

-- move near `Real.differentiableAt_rpow_const_of_ne`
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])

lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]

lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring

lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]

lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])

lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf

lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx

set_option backward.isDefEq.respectTransparency false in
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf
