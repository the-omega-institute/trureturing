/- GID: D5/S3/Zeros/GRH/Lib/Analytic/Landau/PolarLandau
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Analytic/Landau/PolarLandau
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Analytic.Landau.PolarLandau. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Analytic/Landau/PolarLandau.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.NumberTheory.QuadFieldSplitting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Landau's lemma on Dirichlet integrals of one sign. The form here allows real
simple poles of non-negative residue. It concludes that no pole lies right of the exponent of the
one-sided bound. Source: Montgomery and Vaughan, Multiplicative Number Theory I, 2007, Lemma 15.1
(Widder, The Laplace Transform, 1941, II Thm 5b).

This file: Landau's lemma for one-sided bounds; Laplace transforms of
powers; logarithmic derivatives of
L-functions. -/

open ArithmeticFunction DirichletCharacter Complex Set Filter MeasureTheory Metric ProbabilityTheory
  Nat Topology ComplexOrder AnalyticOnNhd Real Calc


variable {N} (χ : DirichletCharacter ℂ N) (d : ℕ) [Fact d.Prime]

/-- For a Dirichlet character χ mod N, a prime d and every integer n, the character `quadTwist` χ d
mod Nd takes at n the value χ(n)·(n/d), where (n/d) is the Legendre symbol. -/
lemma quadTwist_apply (n : ℤ) : quadTwist χ d n = χ n * legendreSym d n :=
  show _ = _ * (chiK d).ringHomComp (algebraMap ..) n by  grind [quadTwist, MulChar.mul_apply,
  changeLevel_eq_cast_of_dvd', apply_eq_zero_iff, IsCoprime.mul_right]

/-- For a Dirichlet character χ mod N and an odd prime d coprime to N, the twist of χ by the
Legendre symbol (·/d), a character mod Nd, is not principal. -/
lemma quadTwist_ne_one (hd : d ≠ 2) (h : N.Coprime d) : quadTwist χ d ≠ 1 :=
  (quadraticChar_exists_neg_one (ZMod.ringChar_zmod_n d ▸ hd)).elim fun a _ e ↦ (chineseRemainder
  h 1 a.val).rec fun n _ ↦ by obtain := quadTwist_apply χ d n, (quadTwist χ d).mul_apply 1 n
                              simp_all [legendreSym, ← ZMod.natCast_eq_natCast_iff, neg_eq_self]

/-- E is measurable, O(e^v) on v ≥ 0; ∫₀^∞ E(v)e^{(1−s)v} dv continues from re s > 2 to a
meromorphic Φ with (s − 1)Φ(s) analytic on re s ≥ 1 and at most simple poles, of residue r(ρ), in re
ρ > 0. As (s − 1)Φ(s) takes the value 0 at s = 1, this allows no pole of Φ at 1. -/
def IsPolar (E : ℝ → ℝ) (r : ℂ → ℂ) := Measurable E ∧ ∃ C Φ, Meromorphic Φ ∧ (∀ v ≥ 0, |E v| ≤ C *
  v.exp) ∧ (∀ s, 2 < re s → Φ s = ∫ v in Ioi 0, E v * ((1 - s) * v).exp) ∧ AnalyticOnNhd ℂ (fun s ↦
  (s - 1) * Φ s) {s | 1 ≤ s.re} ∧ ∀ ρ, 0 < ρ.re → (𝓝[≠] ρ).Tendsto (fun z ↦ (z - ρ) * Φ z) (𝓝 (r ρ))

variable {E : ℝ → ℝ} [NeZero N] {s : ℂ}

lemma integrableOn_laplace_of_abs_le {C} (m : Measurable E) (h : ∀ v ≥ 0, |E v| ≤ C * v.exp) (hs :
  2 < s.re) : IntegrableOn (fun v ↦ E v * ((1 - s) * v).exp) (Ioi 0) := ((integrableOn_exp_mul_Ioi
  (sub_neg.2 hs) 0).const_mul C).mono' (by fun_prop) (ae_restrict_of_forall_mem (by simp) (by
  simp_intro ..; grw [h, mul_assoc, ← Real.exp_add] <;> grind))

/-- Laplace transform of a power: for complex s with re s > 0 and every natural number k, ∫₀^∞
t^k e^{−st} dt = k!/s^{k+1}. -/
lemma laplace_pow (h : (-s).re < 0) k : ∫ t : ℝ in Ioi 0, t ^ k * exp (-s * t) = k ! / s ^ (k + 1)
  := (iteratedDeriv_complexMGF (interior_maximal (@integrableOn_exp_mul_Ioi · · 0) isOpen_Iio h) _ ▸
  EqOn.iteratedDeriv_of_isOpen (@integral_exp_mul_complex_Ioi · · 0) (isOpen_re_lt 0) k h).trans (by
 simp [neg_div, iteratedDeriv_eq_iterate, zpow_sub₀ (h.ne ∘ congr rfl), neg_pow s, pow_succ, field])

@[fun_prop] lemma analyticAt_entireL s : AnalyticAt ℂ (entireL χ) s := Differentiable.analyticAt (by
  grind [entireL, differentiable_LFunctionTrivChar₁, differentiable_LFunction]) s

lemma entireL_ne_zero (hs : 1 ≤ s.re) : entireL χ s ≠ 0 := by
  rw [entireL]; grind [LFunction_ne_zero_of_one_le_re, LFunctionTrivChar₁_apply_one_ne_zero]

lemma LSeriesHasSum_mul_vonMangoldt (hs : 1 < s.re) :
  LSeriesHasSum (fun n ↦ χ n * Λ n) s (ite (χ = 1) 1 0 / (s - 1) - logDeriv (entireL χ) s) :=
  LSeriesHasSum_iff.2 ⟨χ.LSeriesSummable_twist_vonMangoldt hs, by erw [entireL,
  logDeriv_apply, LSeries_twist_vonMangoldt_eq] <;> grind [LFunction_ne_zero_of_one_le_re, one_re,
  deriv_LFunctionTrivChar₁_apply_of_ne_one, LFunction_eq_LSeries, deriv_LFunction_eq_deriv_LSeries]⟩

lemma tendsto_sub_mul_logDeriv_entireL : (analyticOrderNatAt (entireL χ) s = 0 ↔ entireL χ s ≠ 0) ∧
  Tendsto (fun z ↦ (z - s) * logDeriv (entireL χ) z) (𝓝[≠] s) (𝓝 (analyticOrderNatAt (entireL χ)
  s + 0)) := have ⟨g, a, b, e⟩ := (analyticAt_entireL ..).analyticOrderAt_ne_top.1 (entireL_ne_zero
    χ le_rfl congr($((analyticOrderAt_eq_top_iff_eq_zero s (by fun_prop)).1 ·) 1))
  ⟨by simp [e.eq_of_nhds, b], .congr' (mem_inf_principal.2 (by
    filter_upwards [e.deriv, e, a.continuousAt.eventually_ne b, a.eventually_analyticAt]
    cases analyticOrderNatAt (entireL χ) s <;> simp +contextual (disch := fun_prop) [logDeriv,
      field]
    grind)) (.const_add _ (.trans_eq (tendsto_inf_left (.mul (.sub_const le_rfl s)
  (a.deriv.div a b).continuousAt)) (by simp)))⟩

/-- Removable singularity: if s ↦ (s − a)Ψ(s), with value 0 at a, is analytic on the disc of
radius ε about z, a ≠ z, and a, σ lie in that disc, then the Taylor series of Ψ at z
converges at σ. -/
lemma summable_taylor_of_removable {Ψ ε} {a z : ℂ} σ (D :
  AnalyticOnNhd ℂ (fun z ↦ (z - a) * Ψ z) (ball z ε)) (u : z ≠ a ∧ a ∈ ball z ε ∧ σ ∈ ball z ε) :
  Summable fun k ↦ (k ! : ℂ)⁻¹ • (σ - z) ^ k • iteratedDeriv k Ψ z := (hasSum_taylorSeries_on_ball
  ((differentiableOn_dslope (isOpen_ball.mem_nhds u.2.1)).2 D.differentiableOn) u.2.2
  ).summable.congr (by erw [(eqOn_dslope_sub_smul ..).iteratedDeriv_of_isOpen isOpen_ne · u.1])

/-- Landau's lemma. Let E satisfy `IsPolar` with residues r, and let β > 0. If re r(x) ≥ 0 for
all real x > β and E(v) ≤ e^{(β−1)v} for large v, then r(ρ) = 0 whenever re ρ > β.

Known result: Landau's lemma on Dirichlet integrals of one sign. -/
lemma IsPolar.landau {r} (h : IsPolar E r) {β : ℝ} (hβ : 0 < β) (hr : ∀ x, β < x → 0 ≤ (r x).re)
    (hw : ∀ᶠ v in atTop, E v ≤ ((β - 1) * v).exp) {ρ} (hρ : β < ρ.re) : r ρ = 0 := by
  obtain ⟨⟨m, C, Φ, M, hC, e, -, h⟩, Y, hY⟩ := h, eventually_atTop.1 hw
  let K := 1 ⊔ |C| * Y.exp ^ 2
  let μ := (volume.restrict (Ioi 0)).withDensity fun v ↦ (K * (β * v).exp - E v * v.exp).toNNReal
  let S := integrableExpSet (-|·|) μ; let Ψ s := K / (s - β) - Φ s
  have e s (u : 2 < s.re) (w : β - s.re < 0) : s.re ∈ S ∧ complexMGF (-|·|) μ s = Ψ s := by
    obtain ⟨i, j⟩ := (@integrableOn_exp_mul_complex_Ioi (β - s) w 0).const_mul K,
      integrableOn_laplace_of_abs_le m hC u
    refine ⟨((integrable_withDensity_iff_integrable_coe_smul (by fun_prop)).2 ((i.sub j).congr ?q)
      ).norm.congr (by simp), (integral_withDensity_eq_integral_smul (by fun_prop) _).trans (
      integral_congr_ae ?q ▸ by simp [integral_sub i j, integral_exp_mul_complex_Ioi, w]; grind)⟩
    filter_upwards [ae_restrict_mem (by simp)] with v u
    rw [coe_toNNReal, abs_of_pos u]
    simp [sub_mul, mul_assoc, ← Complex.exp_add]; rfl
    cases le_total Y v <;> [grw [hY, sub_mul, Real.exp_sub]; grw [le_of_abs_le (hC ..),
      ← one_le_exp]] <;> simp [field, *, u.out.le] <;> bound
  have H ρ u := ((ContinuousWithinAt.tendsto (by fun_prop (disch := aesop))).sub (h ρ
    (hβ.trans u))).congr fun z ↦ (.symm (mul_sub ..) : _ = _ * Ψ z)
  obtain ⟨a, ha⟩ := exists_isLUB (Sᶜ.insert_nonempty β) ⟨2 + β, (by grind [e ⟨·, 0⟩])⟩
  obtain ⟨A, T⟩ := interior_maximal (fun x ↦ (·.not_ge.imp_symm (ha.1 <| .inr ·))) isOpen_Ioi,
    ((hasDerivAt_id' a).ofReal_comp.tendsto_nhdsNE one_ne_zero).mono_left (nhdsGT_le_nhdsNE a)
  obtain ⟨N : Meromorphic Ψ, G⟩ := fun _ ↦ by fun_prop, analyticOnNhd_complexMGF.mono (@A ·.re)
  have I {ρ} hρ := eventuallyEq_iff_sub.2 <| meromorphicOrderAt_eq_top_iff.1 <| ((
   N.meromorphicOn.fun_sub G.meromorphicOn).meromorphicOrderAt_ne_top_of_isPreconnected (x := ρ)
   (convex_halfSpace_re_gt a).isPreconnected hρ (by grind : a < re ⟨a ⊔ β + 3, 0⟩)).mtr <|
   meromorphicOrderAt_eq_top_iff.2 (mem_nhdsWithin.2 ⟨_, isOpen_re_gt (2 + β), by clear hr; grind⟩)
  obtain rfl | p := (ha.1 (.inl rfl)).eq_or_lt
  simpa using tendsto_nhds_unique ((H ρ hρ).congr' (I hρ).mul_left)
    (tendsto_inf_left (.mul (.sub_const le_rfl ρ) (G _ hρ).continuousAt))
  have J := (T.eventually (N a).eventually_analyticAt).mp (mem_inf_of_right
    fun z u B ↦ (B.frequently_eq_iff_eventually_eq (G _ u)).1 (I u).frequently)
  obtain ⟨ε, o, D⟩ := (MeromorphicAt.analyticAt (by fun_prop) (continuousWithinAt_compl_self.1
    ((H a p).trans_eq congr(𝓝 $((ge_of_tendsto ((H a p).comp T) (J.mp (mem_inf_of_right fun z u B ↦
    by simp [B.self_of_nhds, complexMGF_ofReal, mul_nonneg, u.out.le, mgf_nonneg]))).eq_of_not_lt'
    (·.1.not_ge (by simp_all))))))).exists_ball_analyticOnNhd
  obtain ⟨z, J, w, g⟩ := (J.and (Ioo_mem_nhdsGT (by bound : a < ε / 2 + a))).exists
  obtain ⟨⟨σ, n, v⟩, _⟩ := ha.exists_between (max_lt p (sub_left_lt_of_lt_add g)),
    integrable_pow_mul_exp_of_mem_interior_integrableExpSet (A w)
  use n.elim (by order) <| absurd ⟨by fun_prop, (((lintegral_tsum (by fun_prop)).trans (tsum_congr
   fun k ↦ ?_)).trans_lt
    ((summable_taylor_of_removable σ (D.mono (ball_half_subset ↑z ?_)) ?_).mapL reCLM
   ).tsum_ofReal_lt_top).trans_le' <| lintegral_mono fun y ↦ ((NormedSpace.exp_series_hasSum_exp'
   (𝕂 := ℝ) ((σ - z) * -|y|)).mul_right (z * -|y|).exp).tsum_eq.trans ?_ ▸ enorm_tsum_le_tsum_enorm⟩
  rw [EventuallyEq.iteratedDeriv_eq k J, iteratedDeriv_complexMGF]
  simp_rw [← integral_smul, smul_eq_mul, ← ofReal_natCast, mul_pow, mul_assoc]
  rw_mod_cast [← ofReal_integral_norm_eq_lintegral_enorm (by fun_prop)]
  all_goals simp [← mul_pow, ← mul_assoc, ← neg_mul, dist_eq_norm, ← ofReal_sub,
    ← exp_eq_exp_ℝ, ← Real.exp_add]; clear e H; grind
