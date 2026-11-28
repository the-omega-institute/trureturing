/- GID: D5/S3/Zeros/GRH/New/Exchange/OneSquare
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/OneSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.OneSquare. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/OneSquare.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.SiegelWeil.RallisInner.SharpData
import D5.S3.Zeros.GRH.New.Exchange.ExchangeTheorem
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Lift then descent is proportional to descent then lift. Between forms on two unitary groups,
passing up through a larger group or down through a smaller one by theta lifts agrees on matched
ramified data, up to the L-value constant of the exchange theorem and a possibly zero factor free of
the twist, and this moves lifts past each other in chains. The seesaw principle and a rank-one
exchange of periods are known. Related work: Kudla, Seesaw dual reductive pairs, 1984; Chan, Period
identities of CM forms on quaternion algebras, 2020; He, Compositions of theta correspondences,
2005.

This file: Up-then-down and down-then-up theta lifts agree on partner data up to L-values. -/

attribute [-simp] Space.θ_apply


open MeasureTheory Matrix Fintype Space WeilData
variable {E n n' n₁ n₂} [Field E] [CMType E] [Fintype n] [Fintype n'] [Fintype n₁]
  [Fintype n₂] {s s' s₁ s₂} (A' : Space E n s) {A : Space E n' s'} {U₁ : Space E n₁ s₁}
  {U₂ : Space E n₂ s₂}

lemma integral_integral_sum_eq {c G : n → ℂ} {F : n →
  _} : let μ := U₁.quotMeasure.prod U₂.quotMeasure
  (∀ i, c i ≠ 0 → Integrable (F i) (μ.prod A.quotMeasure) ∧ integral (μ.prod A.quotMeasure) (F i) =
    G i) → ∫ x, ∫ y, ∑ i, c i • F i (x, y) ∂A.quotMeasure ∂μ = ∑ i, c i • G i := fun _ ↦ by
  rw [integral_integral, integral_finsetSum] <;> (try apply integrable_finsetSum) <;>
    congr! <;> by_cases c ‹_› = 0 <;> simp [Integrable.const_mul, *]

lemma apply_eq_mul_of_formRep_one {e e₁ e₂ f w} {y : A.Form e} {c c' C : ℂ} {u d l : _ →ₗ[ℂ] _} (h :
  y = c • u (U₁.formRep e₁ 1 f)) (h' : U₂.formRep e₂ 1 w = c' • d y) (H : c' * c = C) :
  l w = C * l (d (u f)) := by simp_all [smul_smul]

lemma exists_integrable_kernel_bound {y y'} (r : y ∈ U₁.rapidFunctions) (r' :
  y' ∈ U₂.rapidFunctions) {b₁ b₂ : AutChar E} {K : fockSpace s → _ → _ → ℂ} (h : ∃ B N C, ∀ v g z,
  weightedNorm N v ≠ ⊤ → ‖K v g z‖ * A.height z ^ 0 ≤ C * (weightedNorm N v).toReal * (U₁.sum
  U₂).height g ^ B) (hK : ∀ v, Continuous ↿(K v) := by fun_prop) : ∃ N C, ∀ v, weightedNorm N
  v ≠ ⊤ → let F q := y q.1.1 * y' q.1.2 * (b₁.1 q.1.1.det * b₂.1 q.1.2.det)⁻¹.1 * K v (.sum q.1) q.2
  Integrable F ((U₁.quotMeasure.prod U₂.quotMeasure).prod A.quotMeasure) ∧ ∀ q, ‖F q‖ ≤
    C * (weightedNorm N v).toReal := by
  obtain ⟨⟨⟨⟩, r⟩, ⟨⟨⟩, r'⟩, B, N, C, h⟩ := r, r', by simpa using h
  obtain ⟨⟨a, r⟩, b, r'⟩ := r B, r' B
  use N, |C| * |a| * b, fun v hv ↦ (⟨.of_bound (by fun_prop) _ (.of_forall ‹_›), ·⟩) fun _ ↦ ?_
  grw [norm_mul, h, le_abs_self C, height_sum_le, ← r', ← le_abs_self a, ← r] <;>
    simp [le_of_lt, mul_pow, field, *]

variable [WeilData E] (A U₁ U₂)
attribute [local simp] modKernel pairTheta pairWeil_apply

/-- One square. Let rk A = rk A′ + 2e, q = q(U₁) + q(U₂) = q(A) + q(A′) negative signs,
2q + 2 ≤ n = rk U₁ + rk U₂ ≤ 2μ + 2q, ν tame of weight μ, and the four products of characters equal
ν⁻¹υ^⌊n/2⌋ (`rankTwist`).
Send f from U₁ to U₂ along edges, through A (lift, descent) or A′ (descent, lift), with
point data at the blocks of x or y. For every functional l the resulting functions of x and y
satisfy `SquareLaw` with constant κ/c (κ may be 0), c ≠ 0, |c|² = C·`lValueProd`, with C, κ uniform
in the
family.

Lift then descent is proportional to descent then lift. -/
lemma one_square {k₁ k₂ d k Φ₁ Φ₂ k' Φ₁' Φ₂' I} {a b ν 𝔪 χ : ∀ _ : I, _} (h₂ : IsEdgeFamily b k₂ k d
  Φ₂) (h₁ : IsEdgeFamily a k₁ k (!d) Φ₁) (h₃ : IsEdgeFamily a k' k₂ (!d) Φ₂') (h₄ : IsEdgeFamily b
  k' k₁ d Φ₁') σ (hs : negCount (s₁ ⊕ᵥ s₂) = negCount s' + negCount s) e (he : card n' =
  card n + 2 * e) (hn : 2 * negCount (s₁ ⊕ᵥ s₂) + 2 ≤ card (n₁ ⊕ n₂)) {μ : _ → ℤ} (hμ : ∀ v, card
  (n₁ ⊕ n₂) ≤ 2 * μ v + 2 * negCount (s₁ ⊕ᵥ s₂)) (ht : ∀ i, IsTameFor (𝔪 i) (ν i) μ (χ i)) (hE :
  ∀ i {p q} [Fintype p] [Fintype q], card p + card q = card n₁ + card n₂ → a i p * b i q = rankTwist
  (ν i)⁻¹ (n₁ ⊕ n₂)) : let u i x := modDescent _ A (b i) Φ₂ (Pi.single x.toCols₂ 1) _ _ ∘ₗ modLift
                         U₁ A (a i) Φ₁ (Pi.single x.toCols₁ 1) _ (k !d)
  let v i y := modLift A' U₂ (a i) Φ₂' (Pi.single y.toRows₂ 1) _ (k₂ !d) ∘ₗ
    modDescent _ _ (b i) Φ₁' (Pi.single y.toRows₁ 1) (k₁ !d) (k' !d)
  ∃ C κ, ∀ i, ∃ c ≠ 0, ‖c‖ ^ 2 = C * lValueProd (𝔪 i).places (ν i) e ∧
    ∀ f (l : _ →ₗ[ℂ] ℂ), SquareLaw (χ i) σ (κ / c) (l <| u i · f) (l <| v i · f) := by
  intro u v; obtain ⟨C, _, h₀, H⟩ :=
    exchange_theorem (U₁.sum U₂) A A' σ hs he hn hμ (weightedNorm_polyVector_ne_top · _)
  choose N D hi hF using fun j : (_ × U₂.Form (k₂ d)) × Σ i, {x // HasLeftInv (R :=
    (𝔪 i).ResRing) xᵀ} ↦ exists_integrable_kernel_bound (h₁.1.form_mem_rapidFunctions j.1.1)
    (h₂.1.form_mem_rapidFunctions j.1.2) (pairTheta_decay_of_onto _ A (rankTwist _ (n₁ ⊕ n₂)) 1
    (evalAt _) (𝔪 _).disjoint_places_star ((𝔪 _).isSchwartzBruhat_liftFn
    (Pi.single j.2.2.1 1 ∘ vecToMat)) (fun _ c ↦ (isPrimitiveMatrix_of_liftFn_ne_zero _ (by
    simpa using fun _ ↦ (· ▸ j.2.2.2)) (ht _).1.some.2 c).2.imp (by tauto)) 0)
  obtain ⟨⟨P, hP⟩, hp, S⟩ := exists_tendsto_weightedNorm h₀, (hi · _ <|
    weightedNorm_polyVector_ne_top _ ·), mem_rename_range_mul _ _
  refine ⟨C, ((LinearMap.toSpanSingleton ℂ _ fun j ↦ ∫ g, j.1.2 g * u _ j.2.2.1 j.1.1 g
    ∂U₂.quotMeasure).range.closed_of_finiteDimensional.isSeqClosed (fun n ↦ ?_) (tendsto_pi_nhds.2
    fun j ↦ tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' (((hP _).eventually_ne bot_ne_top).mono
    fun n h ↦ integral_sub (hp j (P n)) (by tauto) ▸ norm_integral_le_of_norm_le_const <| .of_forall
    (hF j _ h · |>.trans_eq' <| by rw [norm_sub_rev]; simp [mul_sub])) ((((ENNReal.tendsto_toReal
    bot_ne_top).comp (hP _)).const_smul_zero (D j)).zero_smul_const _)))).imp fun κ hκ i ↦ ?_⟩
  refine Submodule.mul_induction_on (S ?x (P n)) ?_ fun P Q ↦ (Set.mem_of_eq_of_mem
    (by ext; simpa [mul_add] using integral_add (hp ..) (hp ..)) <| add_mem · ·)
  swap; rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩
  obtain ⟨⟨α, e₁⟩, β, e₂⟩ := h₁.exists_lift_eq_realConv P, h₂.exists_lift_eq_realConv Q
  have e F (F' : A.Form _) := by
    simpa [petersson, realConv, ← integral_conj] using (conjForm (eq_star_of_eq_star (h₂.2.1 d).2)
      F).2.petersson_realConv_realConv (h₁.2.1 _).1 F'.2 (star α).integrable β.integrable
  refine ⟨_, funext fun _ ↦ ((integral_prod_symm _ (hp ..)).trans (.trans ?_ ((e ..).trans (congrArg
    _ (h₂.isArrow_modDatum.elim (·.integral_mul_formLift_swap · ..)))))).symm⟩
  simp_rw [← realConv.eq_1, ← e₁, ← e₂, lift, ← integral_prod_mul]
  congr! 4; erw [← modKernel, (?_ : Pi.single _ _ = _), ← hE _ rfl,
    modKernel_sum_left]; simp [field]
  grind [fromCols_toCols]
  simp
  obtain ⟨⟨c, c₀, c₁, H⟩, e, o, t⟩ := H _ _ _ (ht i), (mul_comm ..).trans (hE i (add_comm ..)), by
    simpa using card_congr σ,
    (((ht i).inv.mul (hasWeight_upsilonU1_pow _)).inv (ν := rankTwist _ (n₁ ⊕ n₂)))
  use c, c₀, c₁, fun f l ↦ ⟨fun u x ↦ apply_eq_mul_of_formRep_one
    (h₁.isArrow_modDatum.1.formRep_formLift_of_eq_smul (pairWeil_modDatum_single 1 _) _)
    (h₂.isArrow_modDatum.2.formRep_formLift_of_eq_smul (pairWeil_modDatum_single 1 (liftMod u)⁻¹) _)
    (by simpa [← hE i rfl, ← map_inv] using t.apply_det (liftMod u)), fun u x ↦
    apply_eq_mul_of_formRep_one
    (h₄.isArrow_modDatum.2.formRep_formLift_of_eq_smul (pairWeil_modDatum_single (liftMod u) 1) _)
    (h₃.isArrow_modDatum.1.formRep_formLift_of_eq_smul (pairWeil_modDatum_single _ 1) _)
    (by simpa [← e] using t.apply_det (liftMod u)), fun Φ Ψ hP ↦ ?_⟩
  simp only [← smul_eq_mul, ← map_smul, ← map_sum]
  refine congrArg l (ext_inner_left ℂ fun z ↦ ?_); let f' := conjForm (d.not_not ▸ (h₂.1 _).2) z
  obtain ⟨L, R, K⟩ := fun x ↦ integral_integral_sum_eq fun y hy ↦ (⟨·, integral_prod_symm _ ‹_›⟩)
    ((exists_integrable_kernel_bound (h₁.1.form_mem_rapidFunctions f) (h₂.1.form_mem_rapidFunctions
    f') (pairTheta_modDatum_decay A' _ x x (Ψ := Pi.single y 1) (ht i).1 (by simpa using ⟨_,
    (hP.2 y hy).choose_spec.2 ▸ invFirstRows_mul_firstCols ..⟩) 0)).choose_spec.choose_spec _
    (weightedNorm_polyVector_ne_top _ _)).1, integral_integral_sum_eq fun x hx ↦ by
    simpa +instances only using (fun j ↦ (⟨hi j _ (h₀ _), congr($hκ j).symm⟩ : _ ∧ _ = κ * _)) ⟨(f,
      f'), i, x, (hP.1 x hx).choose_spec.2 ▸ hasLeftInv_invLastRows_transpose ..⟩, by
    simpa only [thetaIntegral, pairTheta, modDatum_eq_sum _ _ Φ, modDatum_eq_sum _ _ Ψ, map_sum,
      map_smul] using H Φ Ψ hP
  simp only [← mul_smul_comm, ← Finset.mul_sum, pairTheta, mul_left_comm _ c, ← modDatum.eq_1, K,
    integral_const_mul] at *
  simp [inner_smul_right, inner_sum, field]
  erw [← R, L, mul_comm]; congr!
  erw [(?_ : Pi.single _ _ = _), ← e, inner_eq_petersson, petersson,
    h₃.isArrow_modDatum.1.coe_formLift, ThetaKernel.integral_lift_eq_integral_descent _
    (h₃.1.form_mem_rapidFunctions _) (h₂.1.form_mem_rapidFunctions f')]; simp_rw
    [h₄.isArrow_modDatum.2.coe_formLift, lift, ← integral_prod_mul]
  congr! 4; nth_rw 1 [← pairTheta, ← modKernel, modKernel_sum_right, e,
    ← hE i (o ▸ add_comm ..).symm]
  simp [e, ← hE i o, field]
  clear * -; grind [fromRows_toRows]
