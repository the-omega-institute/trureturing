import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Rigidity.CasimirBound
import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Holomorphic.MinorEquivariance
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Highest coefficient and reproducing property of the holomorphic discrete series.
The statement here is for products of U(p,q), and the bounded domain is replaced by functions on the
group that extend holomorphically to G times a Borel subgroup. For large gap the discrete series
coefficient equals a product of principal minors. Source: Harish-Chandra, Representations of
semisimple Lie groups IV-VI, Amer. J. Math. 77 (1955), 78 (1956); A. Knapp (1986).

This file: Coefficients of highest vectors extend holomorphically to G·B; mean value over circle. -/
seal Finset.univ Finset.sum Finset.prod


open Matrix Finset Complex Topology Circle Filter MeasureTheory Metric ComplexConjugate
  Norms.L2Operator ContinuousLinearMap U
variable {n Φ} [Fintype n] [Fintype Φ] (ε ε' : n → ℤˣ) (o : n → ℤ)
attribute [local simp] norm_coe prod_eq_zero_iff mul_mem Pi.mul_def IsBorelMatrix.mul mul_zpow
  diagonal_mem_blockDiagAlg IsBorelMatrix
attribute [local simp low] diagChar diagTorus mem_blockDiagAlg BlockTriangular.eq_1

/-- The complex-linear map on matrices keeping the entries (i,j) with o_j < o_i and ε_i = ε_j
and replacing all other entries by zero. -/
@[simp] noncomputable abbrev lowerMask := entryMask fun i j ↦ o j < o i ∧ ε i = ε j

/-- The real-linear map X ↦ N − JN*J on complex matrices, J = diag ε, N = `lowerMask` ε' o X plus c
times the diagonal of X (default c = ½). -/
noncomputable def lowerLiePart (c : ℂ := 2⁻¹) := (1 - mulLeftRight ℝ _ (signMatrix ε) (signMatrix
  ε) * starL' (A := Matrix n n ℂ) ℝ) * (lowerMask ε' o + c • entryMask Eq).restrictScalars ℝ

lemma lowerLiePart_mem_unitaryLie c Z : lowerLiePart ε ε' o c Z ∈ unitaryLie (signMatrix ε) :=
  ext (by simp [lowerLiePart, signMatrix]; ring; norm_cast; simp)

lemma exists_borel_chart (L : _ →L[ℝ] _) {E} (hE : HasStrictFDerivAt E (.id ℝ _) 0) (m : ∀ Z,
  E (L Z) ∈ blockDiagAlg ε ∧ lowerMask ε o (L Z) = lowerMask ε o Z) (z : E 0 = 1 := by simp) : ∃ ψ,
  (HasFDerivAt ψ (.id ℝ _) 1 ∧ ψ 1 = 0)
  ∧ ∀ᶠ y in 𝓝 1, y ∈ blockDiagAlg ε → letI a := E (L (ψ y)); letI b := 1 + (1 - L) (ψ y)
    IsBorelMatrix o b ∧ (a ∈ blockDiagAlg ε ∧ b ∈ blockDiagAlg ε) ∧ y = a * b := by
  have h := (((L.map_zero ▸ hE).comp 0 L.hasStrictFDerivAt).mul' (.const_add 1 (1 -
    L).hasStrictFDerivAt)).congr_fderiv (by aesop : _ = (1 : _ ≃L[ℝ] _).toContinuousLinearMap)
  use ?_, by simpa [z] using! And.intro h.to_localInverse.hasFDerivAt h.localInverse_apply_image
  filter_upwards [h.eventually_right_inverse.filter_mono (by aesop), Units.nhds 1] with y
  generalize h.localInverse _ _ _ y = x; rintro rfl d k; have :=
    mul_mem (blockDiagAlg.inv_mem (m x).1) k
  simp_all [isUnit_iff_isUnit_det, funext_iff]; grind

variable {ε ε' o M X} [AddCommGroup M] [Module ℂ M] {u ρ x : Φ → _} {F w P g}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (ho : o.Injective)

/-- Let D be a continuous family of ℂ-linear maps from E to a Banach space X. If t ↦ f(tY) has
derivative D(tY)Y at every real t, for all Y, then f is complex differentiable at 0 with
derivative D(0). -/
lemma hasFDerivAt_of_rays {E} [NormedAddCommGroup E] [NormedSpace ℂ E] f (D : E → E →L[ℂ] X)
    (hD : Continuous D) (h : ∀ Y t, HasDerivAt (fun t : ℝ ↦ f (t • Y)) (D (t • Y) Y) t) :
    HasFDerivAt f (D 0) 0 := by simpa [curveIntegral_segment, AffineMap.lineMap, fun Y ↦
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ h Y t) (Continuous.intervalIntegrable
    (by fun_prop) 0 1)] using HasFDerivAt.curveIntegral_segment_source (a := 0) hD

@[fun_prop] lemma continuous_weightMinors {X w} [TopologicalSpace X] {f : X → Matrix n n ℂ} (hf :
  Continuous f) (h : ∀ a, (f a).det ≠ 0) : Continuous (weightMinors w <| f ·) :=
  .of_at (by fun_prop (disch := tauto))

@[simp] lemma kTypeNormSq_pos (w : HCParam ε) : 0 < w.kTypeNormSq :=
  integral_pos_of_integrable_nonneg_nonzero (x := 1)
  (by fun_prop (disch := simp)) integrable_of_compactSpace (by simp_intro _) (by simp)

@[simp] lemma isBorelMatrix_diagonal (s : Circle) : IsBorelMatrix o (diagonal (s ^ o ·)) := by simp

lemma exists_analytic_path (hε : ε' = 1 ∨ ε' = ε) g (hg : ↑g ∈ blockDiagAlg ε') : ∃ c : ℝ → USign ε,
  c 0 = 1 ∧ c 1 = g ∧ (∀ t, AnalyticAt ℝ (c · |>.1.1) t) ∧ ∀ t,
  ↑(c t) ∈ blockDiagAlg ε' := have := @NormedSpace.exp_analytic
  by obtain ⟨rfl | rfl, X, Y, _⟩ := hε,
    exists_eq_expU_mul_expU g <;> [use fun t ↦ expU (t • X) * expU (t •
    Y); (cases exists_expU_eq_maxCompactU ⟨g, mem_maxCompactU.2 hg⟩; use (expU <| · • ‹_›))] <;>
    simp_all [mem_blockDiagAlg_iff_commute, Commute.exp_right, Commute.smul_right] <;> fun_prop

lemma IsHolOfWeight.continuous : IsHolOfWeight ε o u F → Continuous F := fun ⟨_, f⟩ ↦ by
  choose a e using by simpa using (f · 1)
  exact ((AnalyticOnNhd.continuousOn fun _ ↦ id).comp_continuous (by fun_prop) a).congr e

lemma IsHolOfWeight.apply_mul_diagTorus (hF : IsHolOfWeight ε o u F) h t :
  F (h * fun _ ↦ diagTorus ε t) = (∏ τ, ∏ i, (t i).1 ^ u τ i) * F h :=
  hF.elim fun _ f ↦ by rcases f h fun _ ↦ diagTorus ε t, f (h * fun _ ↦ diagTorus ε t) 1; simp_all

include ho

lemma isHolOfWeight_weightMinors a (hw : ∀ τ, IsKDominant ε' o (u τ)) (ha : a.det ≠ 0 := by simp) :
  IsHolOfWeight ε o u (fun g ↦ ∏ τ, weightMinors (u τ) (a * g τ)) ε' := ⟨∏ τ, (weightMinors (u τ) <|
  a * proj (R := ℂ) τ ·), fun h b T k ↦ ⟨by fun_prop (disch := aesop), by simp_all [← mul_assoc,
  (hw _).weightMinors_mul_borel ho, field, -IsBorelMatrix]⟩⟩

lemma IsBorelMatrix.exists_eq_diagonal_exp {t : USign ε} (h : IsBorelMatrix o t) : ∃ θ : n → ℝ, t =
  diagonal (cexp <| θ · * I) := ⟨fun i ↦ (t.1 i i).arg, by ext i j; grind [diagonal_apply,
  ofReal_one, norm_mul_exp_arg_mul_I, norm_nonneg, @h.1 i j, by simpa [signMatrix, h.diag_ne_zero,
  field, inv_mat] using (And.intro congr(‖$(h.inv_apply_diag ho i)‖) (@h.inv.1 j i))]⟩

/-- Let o be injective, x_τ of weight u_τ and killed by the E_ab with ε'_a = ε'_b, o_a < o_b,
c_τ continuous coefficient maps, ℓ a bounded multilinear form. Then h ↦ ℓ((c_τ(h_τ)x_τ)_τ)
is holomorphic of weight u (`IsHolOfWeight`, for ε'). -/
lemma HCParam.IsKHighest.isHolOfWeight_coeffMap {c : Φ → USign ε → M →ₗ[ℂ] X} (hx : ∀ τ,
  (toHCParam ε' (-o)).IsKHighest (ρ τ) (u τ) (x τ)) (hd : ∀ τ, (ρ τ).IsCoeffMap (c τ)) (ℓ :
  ContinuousMultilinearMap ℂ _ ℂ) (hc : ∀ τ y, Continuous (c τ · y)
  := by dsimp; fun_prop) : IsHolOfWeight ε o u (fun h ↦ ℓ fun τ ↦ c τ (h τ) (x τ)) ε' := by
  have hD τ Y (_ : Y ∈ blockDiagAlg ε' ∧ Y.BlockTriangular o) : ρ τ Y (x τ) = (∑ a, u τ a * Y a a) •
    x τ := by simp [(ρ τ).apply_eq_sum Y, sum_smul]; rcongr a; rw [sum_eq_single a] <;>
    simp_all [IsKHighest]; module; grind
  let P x := {(h, b) : USign ε × _ | IsBorelMatrix o b ∧
    (↑h ∈ blockDiagAlg ε' ∧ b ∈ blockDiagAlg ε') ∧ blockDiagPart ε' x = h * b}
  choose G hG using fun τ y ↦ ((P y).pairwise_eq_iff_exists_eq fun (h, b) ↦ diagChar (u τ) b • c τ h
      (x τ)).1 fun (h', _) ⟨q, _, f⟩ (h, _) ⟨p, _, e⟩ _ ↦ by
    obtain ⟨t, rfl⟩ := mul_left_surjective h h'; simp [e, mul_assoc] at f
    have ⟨θ, z⟩ := (by simpa [q.2, f, -IsBorelMatrix] using p.mul q.inv :).exists_eq_diagonal_exp ho
    let Y : unitaryLie (signMatrix ε) :=
      ⟨diagonal (θ · * I), by simp [unitaryLie, signMatrix, mul_comm]⟩
    have d {c} s := ((hasDerivAt_mul_const c).const_sub c).cexp.comp_ofReal.smul (hd τ h Y (x τ) s)
    have := is_const_of_deriv_eq_zero (d · |>.differentiableAt) (d · |>.deriv.trans (by
      simp [*, Y]; module)) 1 0
    simp_all [exp_sum, exp_int_mul, show expU Y = t by
      ext : 2; simp [*, Y, exp_diagonal, exp_eq_exp_ℂ]]; module
  obtain ⟨V, ψ, ⟨d, z⟩, r⟩ := lowerLiePart_mem_unitaryLie ε ε' o 0,
    exists_borel_chart ε' o (lowerLiePart ε ε' o 0) hasStrictFDerivAt_exp_zero
    fun Z ↦ by use mem_blockDiagAlg_iff_commute.2 (.exp_right (ext ?_)) <;> simp [lowerLiePart,
    signMatrix] <;> grind
  have K τ y := fun (⟨(h, b), p, m, f⟩ : (P y).Nonempty) ↦
    let A := blockDiagPart ε' ∘L mulLeftRight ℂ _ h.1.1⁻¹ b⁻¹
    have a : A y = 1 := by simp_all [A, -mem_blockDiagAlg]
    And.imp_left ((a ▸ (z ▸ DifferentiableAt.smul (c := fun Z ↦ diagChar (u τ) ((1 + Z) ⊙ b))
    (by simp; fun_prop (disch := simp)) (hasFDerivAt_of_rays (fun Z ↦ c τ (h * expU ⟨_, V Z⟩) (x τ))
      (fun Z ↦ (c τ (h * expU ⟨_, V Z⟩) ∘ₗ (ρ τ).ρ.flip (x τ)).toContinuousLinearMap ∘L lowerMask ε'
    o) (by simp [continuous_clm_apply]; fun_prop)
      (by simpa (disch := simp; lia) [lowerLiePart, hD τ (_ * _), signMatrix] using!
      (hd τ h ⟨_, V ·⟩ (x τ)))).differentiableAt).comp 1 ⟨1, .of_isLittleO d.isLittleO⟩
    ).comp y A.differentiableAt).congr_of_eventuallyEq (eventually_and.1 (.mono (A.cont.tendsto' y 1
    a r) fun y r ↦ have ⟨t, k, e⟩ := r (blockDiagPart_mem _)
      have q : (h * expU ⟨_, V _⟩, _) ∈ P y := ⟨t.mul p, k.imp (mul_mem m.1) (mul_mem · m.2),
        by simpa [A, m, p.2, mul_assoc] using congr(h * $e * b)⟩
      ⟨(hG τ _ _ q).symm.trans (by simp [↓t.mul_apply_diag ho p, lowerLiePart, signMatrix, a]),
        Exists.intro _ q⟩))
  use (ℓ fun τ ↦ G τ <| · τ), fun h b c k ↦ have q τ : (_, _) ∈ P _ := ⟨c τ, k τ, by simp [k]⟩
    ⟨analyticAt_of_eventually_differentiable (nhds_pi.le ((eventually_pi fun τ ↦
      (K τ _ ⟨_, q τ⟩).2.mono (K τ · · |>.1)).mono fun y d ↦ ℓ.analyticAt.differentiableAt.comp y
      (by fun_prop))), by simp [← hG _ _ _ (q _), ℓ.map_smul_univ]⟩

/-- For o injective and P true near 1, each block diagonal x near 1 has diag(s^o)x =
A(s)diag(s^o)b on |s| = 1, with A entire, A(0) = 1, P(A(s)) on |s| ≤ 1, b block diagonal,
invertible, triangular for o, m_w(x) = ∏ b_ii^{w_i} for K-dominant w. -/
lemma eventually_exists_torus_entire_factor (hw : IsKDominant ε o w) (hP : P ∈ 𝓝 1) : ∀ᶠ x in 𝓝 1,
  x ∈ blockDiagAlg ε → ∃ A : ℂ → _, ∃ b ∈ blockDiagAlg ε, IsBorelMatrix o b ∧
  (∀ s, AnalyticAt ℂ A s) ∧ A 0 = 1 ∧ (∀ s ∈ closedBall 0 |1|, A s ∈ P) ∧ weightMinors w
  x = diagChar w b ∧ ∀ s : Circle, letI d := diagonal (s.1 ^ o ·); d * x = A s * (d * b) := by
  let A Z s := 1 + of fun i j ↦ s ^ (o i - o j).toNat * lowerMask ε o Z i j
  have ⟨ψ, ⟨d, z⟩, r⟩ :=
    exists_borel_chart ε o ((lowerMask ε o).restrictScalars ℝ) (hasStrictFDerivAt_sub_const (-1))
    (by simp; grind); filter_upwards [r, d.continuousAt ((isCompact_closedBall 0
    |1|).eventually_forall_mem A P fun s _ ↦ by convert hP; aesop)] with x r p hx
  have ⟨b, ⟨a, c⟩, e⟩ := r hx; refine ⟨_, _, c, b, Differentiable.analyticAt (differentiable_pi.2
    (by simp [A, differentiable_pi, -entryMask])), ext (by simp [A]; lia),
    p, ?_, ?_⟩ <;> nth_rw 1 [e]
  simpa [↓hw.weightMinors_oppBorel_mul ho b.2 a
    (by rw [IsBorelMatrix, det_eq_prod_diag_of_blockTriangular (neg_injective.comp ho)] <;> simp <;>
    bound)] using hw.weightMinors_mul_borel ho (IsHermInvolution.det_ne_zero 1) c b
  simp_intro s [← mul_assoc]; congr 1 with; simp [A, ← zpow_natCast]
  grind [zpow_sub₀, coe_ne_zero, zpow_ne_zero]

/-- Circle mean: let ε' be 1 or ε, o injective, u_τ dominant and g_τ block diagonal for ε', F
satisfy `IsHolOfWeight` for u, ε', q analytic on the closed disc. The mean over |s| = 1 of
F(diag(s^o)g) ∏ s^{−o_i u_{τ,i}} q(s) is q(0) ∏_τ m_{u_τ}(g_τ) F(1). -/
lemma IsHolOfWeight.circle_mean_weightMinors (hF : IsHolOfWeight ε o u F ε') (hw : ∀ τ,
  IsKDominant ε' o (u τ)) (hg : ∀ τ, ↑(g τ) ∈ blockDiagAlg ε') q
  (hq : AnalyticOnNhd ℂ q (closedBall 0 |1|)) (hε : ε' = 1 ∨ ε' = ε := by simp) :
  ∫ θ : UnitAddCircle, (letI s := θ.toCircle; F ((fun _ ↦ diagTorus ε (s ^ o ·)) * g) *
    ((∏ τ, ∏ i, (s.1 ^ o i) ^ u τ i)⁻¹ * q s.1)) = q 0 * (∏ τ, weightMinors (u τ) (g τ)) * F 1 := by
  choose c z e m hc using (exists_analytic_path hε _ <| hg ·)
  obtain ⟨rfl, _, F', f⟩ := funext e, (hq ·), hF
  have H s t := f (diagTorus ε (s ^ o ·) * c · t)
  choose y a e using by simpa [*] using And.intro (f 1 1) (H · · 1)
  have ⟨_, V, d, v⟩ := mem_pi'.1 (nhds_pi.ge y.1.eventually_analyticAt)
  simp [← e]; refine congrFun (AnalyticOnNhd.eq_of_eventuallyEq (fun t _ ↦
    ((IsAnalyticFamily.of_analyticAt (ι := fun θ ↦ (_, _, _)) ?_ (fun (a, b, c, z) ↦
    F' (b * a) * (c * q z)) ?_).analyticAt_integral _).restrictScalars.comp (.pi (m · t)))
    (fun t _ ↦ (?_ : AnalyticAt ℂ (fun a ↦ q 0 * (∏ τ, weightMinors (u τ) (proj (R := ℂ) τ a))
    * F 1) _).restrictScalars.comp (.pi (m · t))) (.mono (.all fun τ ↦
    (z τ ▸ (m τ 0).continuousAt.tendsto) (eventually_exists_torus_entire_factor ho (hw τ) (d τ)))
    fun t h ↦ ?_)) 1 <;> try fun_prop (disch := simp)
  choose A b k tb dA _ _ _ _ using (h · (hc _ _))
  have j s := (H s t _ (tb · |> (isBorelMatrix_diagonal s).mul |>.inv) (by simp [hc, k])).2
  simp [-Matrix.mul_inv_rev, (tb _).2, IsBorelMatrix.inv_apply_diag ho, ↓e,
    -IsBorelMatrix, *] at j ⊢; have := (tb · |>.diag_ne_zero ho)
  convert integral_toCircle (hq.const_smul (R := ℂ).mul fun s h ↦ .comp (v (by tauto)) (.pi
    (dA · s))).differentiableOn using 3 <;> simp [field, *]

lemma IsHolOfWeight.integral_mul_conj_weightMinors {w : HCParam ε} (hw : IsKDominant ε o w) (hF :
  IsHolOfWeight ε o (fun () ↦ w) F ε) (c : Continuous F := by simp; fun_prop (disch := simp_all)) :
  ∫ k, F (fun _ ↦ k) * conj (weightMinors w k.1) ∂haarK ε = w.kTypeNormSq * F 1 :=
  (integral_eq_of_circle_mean (fun θ ↦ map_mul_left_eq_self _ (diagTorusK
  (_ ^ o ·))) integrable_of_compactSpace fun k ↦ by simpa [← coe_inv_eq_conj] using
  (hF.circle_mean_weightMinors ho (by simpa) (by simp [← mem_maxCompactU]) _
  analyticOnNhd_const)).trans (by simp [← integral_complex_ofReal, conj_mul'])
