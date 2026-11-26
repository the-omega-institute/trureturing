import GRH.Lib.General.Analysis.OstrowskiTaussky
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of real and complex analysis (textbook or folklore).

This file: Holomorphic implies analytic in several variables; analyticity of parameter integrals.
Cauchy estimate, holomorphy of parametric integrals, Mellin integrals on a strip. -/

open MeasureTheory Metric ContinuousMap Module Real Finset AbstractMeasure Complex Set
variable {E F K} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {p : E}
  [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace K] [CompactSpace K] {f : E → K → ℂ}
  {_ : MeasurableSpace K} [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

lemma strongIntegral_eval (f : C(K, ℂ)) : strongIntegral μ (evalCLM ℂ) f = ∫ k, f k ∂μ :=
  strongIntegral_apply _ _ (·.memLp μ ℂ |>.integrable le_rfl) f

/-- f : E → K → ℂ agrees near a with a map from E to the Banach space C(K, ℂ) that is analytic
at a. -/
def IsAnalyticFamily (f : E → K → ℂ) a := ∃ g : _ → C(K, ℂ), AnalyticAt ℂ g a ∧ ∀ᶠ x in nhds a,
  g x = f x

omit [FiniteDimensional ℂ E] in
lemma IsAnalyticFamily.analyticAt_integral : IsAnalyticFamily f p → AnalyticAt ℂ (∫ k,
  f · k ∂μ) p := fun ⟨_, a, b⟩ ↦ (((strongIntegral μ (evalCLM ℂ)).analyticAt _).comp a).congr
  (b.mono (by grind [strongIntegral_eval]))

variable [R1Space K]

set_option synthInstance.maxHeartbeats 200000 in
/-- Let K be compact and R1, E finite-dimensional. If, for all x near p and all k, f is jointly
continuous at (x, k) and f(·, k) is complex differentiable at x, then f is analytic at p as a map to
C(K, ℂ). -/
lemma isAnalyticFamily_of_differentiable (hf : ∀ᶠ x in nhds p, ∀ k, ContinuousAt f.uncurry (x, k) ∧
    DifferentiableAt ℂ (f · k) x) : IsAnalyticFamily f p := by
  induction' _ : finrank ℂ E with n i generalizing E K
  use .const _ ⟨f p, .of_at ?_⟩ <;> simp_all [finrank_zero_iff_forall_zero] <;> fun_prop
  have e : E ≃L[ℂ] ℂ × ULift (Fin n → ℂ) := .ofFinrankEq (by simpa [add_comm])
  choose r o s using (nhds_basis_closedBall.1 _).1 (e.symm_map_nhds_eq _ ▸ hf)
  let u (w : ℂ) : C(K × sphere (e p).1 r, ℂ) := .mk (·.2) - w • 1
  have U {w} (_ : dist w (e p).1 < r) := (u w).isUnit_iff_forall_isUnit.2 (by
    simp [u]; grind [dist_eq_norm])
  refine (i (f := fun x q ↦ u (e p).1 q * .I * f (e.symm (q.2, x)) q.1 / (2 * π * .I)) (.mono
    (ball_mem_nhds _ o) fun x h k ↦ (s (max_le k.2.2.le h.le) _).imp (by fun_prop) (by fun_prop))
    (by simp)).elim fun H ⟨a, g⟩ ↦ ⟨_, ((contractSndCLM (strongIntegral ((volume.restrict (.Icc 0
    (2 * π))).map (⟨_, circleMap_mem_sphere _ o.le ·⟩)) (evalCLM ℂ))).analyticAt _).comp (((((
    analyticOnNhd_inverse _ (U (by simpa))).comp (by fun_prop)).comp analyticAt_fst).mul (a.comp
    analyticAt_snd)).comp (e.analyticAt _)), .mono (e.continuousAt (prod_mem_nhds (ball_mem_nhds _
    o) (g.and (ball_mem_nhds _ o)))) fun y ⟨w, g, x⟩ ↦ ?_⟩
  ext; erw [strongIntegral_eval, integral_map] <;> try fun_prop
  simpa [circleIntegral_def_Icc, g, u, integral_div, mul_left_comm, field, mul_div,
    eq_inv_of_mul_eq_one_left congr($(Ring.inverse_mul_cancel _ (U w)) _)] using
    DifferentiableOn.circleIntegral_sub_inv_smul (fun z h ↦ (@s (z, _) (max_le h x.le)
    _).2.comp_differentiableWithinAt z (by fun_prop)) w

/-- If ι: K → F is continuous, K compact and R1, and Θ is analytic at (p, ι k) for every k,
then x ↦ Θ(x, ι ·) is analytic at p as a map to C(K, ℂ). -/
lemma IsAnalyticFamily.of_analyticAt {ι : K → F} (c : Continuous ι) Θ (h : ∀ k,
  AnalyticAt ℂ Θ (p, ι k)) : IsAnalyticFamily (Θ ⟨·, ι ·⟩) p :=
  isAnalyticFamily_of_differentiable ((isCompact_univ.eventually_forall_mem (·, ι ·) _
  fun k _ ↦ (h k).eventually_analyticAt).mono (by simp; refine fun _ _ _ ↦ ⟨?_, ?_⟩ <;> fun_prop))

/-- A map between finite-dimensional complex normed spaces that is complex differentiable at
every point near p is analytic at p. -/
lemma analyticAt_of_eventually_differentiable [FiniteDimensional ℂ F] {f : E → F} (h : ∀ᶠ z in nhds
  p, DifferentiableAt ℂ f z) : AnalyticAt ℂ f p := let e := (finBasis ℂ F).equivFunL; by simpa using
    ((e.symm.analyticAt _).fun_comp (.pi fun i ↦
    (isAnalyticFamily_of_differentiable (f := fun y _ ↦ e (f y) i) (h.mono fun _ h _ ↦
    fun _ ↦ by use ?_ <;> fun_prop h.continuousAt)).analyticAt_integral (.dirac ())))

/-- A complex polynomial P in finitely many variables is differentiable at every x, with
derivative v ↦ ∑ᵢ (∂P/∂Xᵢ)(x)·vᵢ, given by the formal partial derivatives. -/
@[fun_prop] lemma hasFDerivAt_mvPolynomial_eval {ι} [Fintype ι] (P : MvPolynomial ι ℂ) x :
  HasFDerivAt (𝕜 := ℂ) (P.eval ·) (∑ i, (P.pderiv i).eval x • .proj i) x := by apply
  P.induction_on <;> simp [add_smul, mul_smul, ← smul_sum, apply_ite] <;> fun_prop

variable {E F : _} {X} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace
  ℂ F] [MeasurableSpace X] {μ : Measure X}

/-- A map P between complex normed spaces that is complex differentiable at 0 and satisfies
P(2w) = 2P(w) for all w equals its derivative at 0, so is ℂ-linear. -/
lemma eq_fderiv_of_double (P : E → F) (hP : DifferentiableAt ℂ P 0) (h : ∀ w, P (w + w) = P w +
    P w) w : P w = fderiv ℂ P 0 w := tendsto_const_nhds_iff.1 ((hP.hasFDerivAt.lim w (c := (2 ^ ·))
    (l := .atTop) (by simp [tendsto_pow_atTop_atTop_of_one_lt])).congr (Nat.rec
    (by simpa using h 0) (by norm_num [← h, pow_add, mul_smul, smul_sub, two_smul, ← add_smul])))

/-- Schwarz lemma in Lipschitz form: if f is complex differentiable and of norm at most B on the
open ball of radius r about c, then ‖f(z) − f(c)‖ ≤ (2B/r)·‖z − c‖ for z in that ball. -/
lemma norm_sub_le_of_holomorphic_bdd {f : E → F} {c r B} (h : ∀ w ∈ ball c r, DifferentiableAt ℂ f
  w ∧ ‖f w‖ ≤ B) z (hz : z ∈ ball c r) : ‖f z - f c‖ ≤ (B + B) / r * ‖z - c‖ := by
  simpa [dist_eq_norm] using dist_le_div_mul_dist_of_mapsTo_ball (h · · |>.1.differentiableWithinAt)
    (by simp_all [MapsTo, dist_eq_norm, norm_sub_le_of_le, pos_of_mem_ball hz]) hz

/-- Complex differentiation under the integral sign: if each f(w, ·) is a.e. strongly measurable
and, for w near z and all x, f(·, x) is differentiable at w with ‖f(w, x)‖ ≤ g(x), g
integrable, then ∫ f(w, x) dμ is differentiable at z. -/
lemma eventually_differentiableAt_integral {f : E → X → F} {z g} [FiniteDimensional ℂ E] (i :
  Integrable g μ) (m : ∀ w, AEStronglyMeasurable (f w) μ) (h : ∀ᶠ w in nhds z, ∀ x,
  DifferentiableAt ℂ (f · x) w ∧ ‖f w x‖ ≤ g x) : ∀ᶠ w in nhds z, DifferentiableAt ℂ (∫ x,
  f · x ∂μ) w := h.eventually_nhds.mono fun z k ↦ have ⟨_, o, h⟩ := eventually_nhds_iff_ball.1 k
  have d := .of_forall (k.self_of_nhds · |>.1.hasFDerivAt)
  ⟨_, (hasFDerivAt_integral_of_dominated_loc_of_lip' (ball_mem_nhds z o) (by tauto) (by simp_all
    [i.mono']) ((((finBasis ℂ E).equivFunL.arrowCongr 1).trans (.piRing _)).isHomeomorph.isEmbedding
  |>.aestronglyMeasurable_comp_iff.1 (.of_eval fun _ ↦ memLp_zero_iff_aestronglyMeasurable.2
  (aestronglyMeasurable_of_tendsto_ae _ (by
  fun_prop) (d.mono fun _ d ↦ (d.hasLineDerivAt _).tendsto_slope_zero)) : MemLp _ 0
    _).aestronglyMeasurable
  )
  (.of_forall fun x ↦ norm_sub_le_of_holomorphic_bdd (h · · x)) (by fun_prop) d).2⟩

/-- Let N > 0 be measurable, T·N^t integrable and the integral of |T|·N^s finite. Then ∫ T·N^z dμ
converges absolutely and is continuous for real z in [s, t], and is real-analytic on (s, t). -/
lemma mellin_analytic_on_strip {T : X → ℂ} {N} {s t : ℝ} (p : ∀ a, 0 < N a) (n : Measurable N) :
    let F z a := T a * (N a ^ z : ℝ); HasFiniteIntegral (F s) μ → Integrable (F t) μ →
    (∀ z ∈ Set.Icc s t, Integrable (F z) μ) ∧ ContinuousOn (∫ a, F · a ∂μ) (Set.Icc s t) ∧
    AnalyticOnNhd ℝ (∫ a, F · a ∂μ) (Set.Ioo s t) := by
  push_cast [Real.rpow_def_of_pos, p]; intro h k
  have m := by simpa [← Complex.exp_add, mul_assoc, mul_sub] using fun z ↦
    k.1.fun_mul (n.log.complex_ofReal.mul_const (z - t)).cexp.aestronglyMeasurable
  have I := (k.prodMk ⟨m s, h⟩).norm
  exact (fun b ↦ have J z h := .of_forall (b z h · |>.2)
    ⟨(I.mono' (m _) <| J · ·), continuousOn_of_dominated (by tauto) J I (.of_forall (by fun_prop)),
    fun z h ↦ (analyticAt_of_eventually_differentiable (eventually_differentiableAt_integral I m
      (.mono (continuous_re.tendsto _ (by simpa)) b))).restrictScalars.comp (ofRealCLM.analyticAt
      z)⟩) fun _ _ a ↦ ⟨by fun_prop, by simp_all [← Real.rpow_def_of_pos]; bound [le_total 1 (N a)]⟩
