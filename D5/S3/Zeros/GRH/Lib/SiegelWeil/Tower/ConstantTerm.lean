/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/Tower/ConstantTerm
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/Tower/ConstantTerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.Tower.ConstantTerm. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/Tower/ConstantTerm.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.ThetaIntegralLaws
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Tower property: constant term of a theta lift along an isotropic line (known result;
see Lib.SiegelWeil.Tower.LargeSideConstantTerm).

This file: Constant term of a theta integral along an isotropic line, unfolded over orbits. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section


open Matrix MeasureTheory Measure Units MulAction Space Splitting Submodule Pointwise Function Equiv
  WeilData
variable {E} [Field E] [CMType E] [WeilData E] {n n' r r'} [Fintype n] [Fintype n'] [Fintype r]
  [Fintype r'] {s s' t t'} {W : Space E n s} {W' : Space E n' s'} {V : Space E r t}
  {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit) (a b : AutChar E)

/-- The product of the invariant probability measures on 𝔸ⁿ/Eⁿ and 𝔸/E; integrating along
`lineRadical` against it gives the constant term along an isotropic line. -/
abbrev radicalMeasure := (ratMatrices E n Unit).qms.prod (ratMatrices E Unit Unit).qms

/-- The contribution of a rational vector x of V to the constant term along the line of A: the
mean of its term over the radical if x is isotropic, else 0. -/
def constTermAt x f := if xᴴ * V.J * x = 0 then ⨍ y,
  A.thetaTerm V 1 1 f (lineRadical A (y, 0)) x 1 ∂(ratMatrices ..).qms else 0

attribute [-instance] locallyCompact_of_proper DiscreteUniformity.instDiscreteTopology
attribute [local simp] Splitting.thetaTerm sourceTerm_radicalElt star_eq_conjTranspose lineLevi
  radicalElt_mul_kAdelic radicalElt_inv

lemma constTermAt_eq_integral x f : constTermAt A x f = ∫ q,
  A.thetaTerm V a b f (lineRadical A q) x 1 ∂radicalMeasure := by
  erw [constTermAt, ← mul_boole, ← isDualFamily_ratMatrices.quotMean_eq_ite,
    ← average_quotMeasure_eq_quotMean _ volume (isDualFamily_ratMatrices.1 _), ← integral_prod_mul]
  simp [↓gram_at_point_eq_map, ← mul_assoc, ← map_mul, -coe_units_inv]
  simp [trace, entrywise, mul_comm]

lemma hasSum_constTermAt {f} : HasSum (fun x ↦ constTermAt A (replicateCol _ x) f)
    (∫ q, pairTheta _ V a b f (lineRadical A q, 1) ∂radicalMeasure) := by
  simp_rw [constTermAt_eq_integral A a b, Splitting.thetaTerm]
  exact (piCongrRight fun _ ↦ funUnique ..).hasSum_iff.1 (hasSum_integral_of_dominated_convergence _
    (by fun_prop)
    (by simpa [↓sourceTerm_radicalElt, ↓sourceTerm_eq_mixedTerm] using fun _ ↦ .of_forall fun _ ↦
    norm_apply_le ..) (.of_forall fun _ ↦ ((summable_norm_mixedTerm ..).mul_left _).comp_injective
    uncurry_injective) (by simp) (.of_forall fun _ ↦ hasSum_theta_sourceTerm ..))

lemma constTermAt_zero f : constTermAt A 0 f = θ _ (A.sourceTerm V 0 f) := by simp [constTermAt]

open MatMul

lemma constTermAt_smul_k {ξ} (h : ξ ≠ 0) {f} : constTermAt A (ξ • X.k) f =
  θ _ (lineTerm A X true (toAdele ξ) f) := by
  let φ : Matrix n Unit (𝔸 E) →+ _ := .mk' (toAdele ξ • matToVec ·ᴴ) (by simp)
  have h₀ y : y ∈ ratMatrices .. → φ y ∈ _root_.ratVectors .. := .imp' (ξ • matToVec ·ᴴ) (by aesop)
  erw [Splitting.zeroTerm_apply, ← quotMean_comp _ φ (isContPeriodic_along_k ..) h₀
    (⟨conjTranspose <| toAdele ξ⁻¹ • vecToMat ·, _⟩) _, ← average_quotMeasure_eq_quotMean _ volume
    ⟨_, by grind -ring -linarith [(isContPeriodic_along_k ..).2]⟩, constTermAt] <;>
  simp [X.k.map_smulₛₗ _ toAdele, φ, kAdelic, ↓homTarget_kAdelic, smul_smul, ← map_mul, h,
    kronecker_mulVec_eq_matToVec, dualFrame, -transpose_mul] <;> fun_prop [matToVec]

/-- If the theta kernel of f is `IsTargetBounded`, the constant term at g, along the isotropic line
of A, of its theta integral over [U(V)] is the integral over h of the sum over rational x of the
terms `constTermAt` of ω(g,h)f. -/
lemma integral_thetaIntegral_lineRadical {f} (h : IsTargetBounded _ V f) g : ∫ q,
  thetaIntegral _ V a b f (lineRadical A q * g) ∂radicalMeasure = ∫ h, ∑' x, constTermAt A
  (replicateCol _ x) (pairWeil _ V a b (g, h) f) ∂V.quotMeasure := h.elim fun _ ⟨_, h⟩ ↦ by
  choose _ k _ _ o e using exists_isCompact_rat_mul_radicalElt_mem A
  simpa [(hasSum_constTermAt A a b).tsum_eq, ← pairTheta_mul] using! integral_integral_swap
    (.of_bound (by fun_prop) _ (.of_forall fun _ ↦ (h ..).trans ((exists_mul_height_pow_le
    (k.image_auto (· * g)) _).choose_spec _ _ (o ..) ⟨_, e .., mul_assoc ..⟩)))

/-- Unfolding: for some real c ≠ 0, if the term x = 0 vanishes, ∫_{[U(V′)]} Σ_x `constTermAt`
x (ω(g,h)f) dh is c times the integral of |t|^(rk V+1) Σ_{ξ∈E^×} θ(`lineTerm`) over
ideles mod E^×, [U(V)] and the maximal compact subgroup, when this integrand is integrable.

Known result: Tower property: constant term of a theta lift along an isotropic line. -/
lemma exists_unfold_constant_term : ∃ c ≠ (0 : ℝ), ∀ a b f g, let F h := pairWeil _ V' a b (g, h) f
  let T β ξ (p : _ × maxCompact E t') := θ _ (lineTerm A X β ξ (F (lineLevi X p.1 * p.2)))
  let Θ p := (ideleAbs p.1.1 ^ (Fintype.card r + 1) : ℝ) * ∑' ξ : Eˣ, T true ↑ξ p
  let ν := (((principalAdeleUnits E).qms haar).prod V.quotMeasure).prod haar
  (∀ h, constTermAt A 0 (F h) = 0) → Integrable Θ ν →
    ∫ h, ∑' x, constTermAt A (replicateCol _ x) (F h) ∂V'.quotMeasure = c * integral ν Θ := by
  have m : ∀ g, (g ∈ V'.Γ ∧ ∃ ξ : Eˣ, X.ActsOnFrame g (scalar _ ↑ξ)) ↔
    g ∈ (stabilizer _ (E ∙ X.k.col ())).map
    V'.ratEmbed := by simpa [Units.smul_def, -Prod.forall, ← ext_iff, smul_span, funext_iff,
    ← ratEmbed_mulVec_vecAtPoint, -Subtype.exists, comm.trans span_singleton_eq_span_singleton,
    Unique.forall_iff, mul_comm (toAdele _), ← comm.trans V'.vecAtPoint_injective.eq_iff,
    Subgroup.smul_def] using! Set.ext_iff.1 Set.image_preimage_eq_range_inter.symm
  let P b : selfAdjoint (Matrix Unit Unit (𝔸 E)) := ⟨_, .add_star_self (toAdele (2⁻¹ : E) • b)⟩
  let η (p : _ × selfAdjoint _) := X.radicalElt p.1 p.2.1
  have ρ c b : X.radicalElt c b ∈ Set.range η := ⟨(c, P b), G.ext_mat (by
    simp [η, P, radicalElt]; match_scalars <;> grind)⟩
  obtain ⟨_, h, _, κ, K⟩ := Surjective.countable (inferInstance : IsNoetherian E (r' → E)).1,
    LeftInverse.isClosedEmbedding (f := fun g ↦
    (-X.iCoord * g.mat * X.lAdelic, P (-toAdele (j : E) • X.kCoord * g.mat * X.lAdelic))) (g :=
    η) (by rintro ⟨_, _, b⟩; simp [η, P, radicalElt, IsHermitian.eq b]; match_scalars
    <;> grind) (by fun_prop) (by fun_prop), exists_isCompact_rat_mul_radicalElt_mem X
   -- the radical and its Haar measure
  let N := Subgroup.ofDiv (.range η) .of_subtype (by
    rintro _ ⟨_, rfl⟩ _ ⟨_, rfl⟩; erw [radicalElt_inv, radicalElt_mul]; apply ρ)
  let e : _ ≃ₜ N := h.toHomeomorph
  have : IsHaarMeasure ((volume.prod addHaar).map e) := by
    refine' { IsFiniteMeasureOnCompacts.map _ e, e.2.isOpenPosMeasure_map e.surjective with .. }
    refine fun ⟨_, x, rfl⟩ ↦ ((e.measurable.measurePreserving _).of_semiconj
      ((measurePreserving_add_left _ x.1).skew_product (g := fun c b ↦
      x.2 + P (toAdele (j : E) • x.1ᴴ * stdForm E t * c) + b) (Continuous.measurable ?_) ?_) (by
      intro; ext1; show η _ = _ * η _; apply G.ext_mat; simp [η, P, radicalElt]; clear * -
      match_scalars <;> grind) ?_).2 <;> first | fun_prop | simp [map_add_left_eq_self]
  refine (integral_orbitMeasure_iwasawa (ideleAbs ·.1 ^ (Fintype.card r + 1)) volume
    (haar.prod volume) haar (lineLevi X) h.2 (by fun_prop) (by simp)
    (by simp [G.continuous_iff, Splitting.levi]; fun_prop) (X.iwasawa · |>.elim fun _ ⟨hk, a, _, _,
    _, _, p, h⟩ ↦ ⟨⟨_, ρ ..⟩, (a.det⁻¹, p), ⟨_, hk⟩⁻¹, eq_mul_inv_of_mul_eq (h.trans congr(_ *
    X.levi $(by ext <;> simp)))⟩) (fun p f o ↦ (e.measurableEmbedding |>.lintegral_map _).trans
    (congr(∫⁻ _, f $(mul_inv_eq_of_eq_mul (levi_conj_radicalElt ..)) ∂_).trans
    (((MeasurePreserving.prod ⟨Continuous.measurable (by fun_prop), volume_map_mul_mul_adele _
    (star _)⟩ ⟨by fun_prop, map_conjugate_selfAdjoint addHaar⟩).lintegral_comp
    (o.comp h.measurable)).trans ?_))) (fun (a, g) ⟨_, e⟩ ↦ by simpa [Splitting.levi, η, radicalElt,
    ← G.isClosedEmbedding_mat.1.2.eq_iff, ← ext_iff] using congr((X.kCoord * ($e).mat * X.kAdelic,
    X.iCoord * ($e).mat * X.iAdelic)).symm) ((principalAdeleUnits E).subtype_injective.prodMap
    Subtype.val_injective) (((principalAdeleUnits E).qms haar).prod V.quotMeasure) (fun f h ↦ ?_)
    (fun ⟨⟨_, ξ, rfl⟩, _, h⟩ ↦ (m _).1 ⟨congr(X.levi ($(by ext : 2; simp), _) ∈ _).mp (X.levi_mem_Γ
    (.scalar _ ξ⁻¹) h), ξ⁻¹, by exact levi_mul_kAdelic ..⟩) (m · |>.2 · |>.elim fun ⟨M, e⟩ ⟨ξ, h⟩ ↦
    (X.exists_eq_radicalElt_mul_levi h).elim fun c ⟨b, t, p, o, u, v⟩ ↦ ⟨(⟨_, ξ, rfl⟩,
    ⟨p, V.mem_Γ_iff_range.2 (mem_ratMatrices.1 ⟨V.J⁻¹ * X.iᴴ * V'.J * M.1.1 * X.i, by simp [← e,
    iCoord, v, iAdelic, mat_ratEmbed, V'.map_J, map_J_inv, Space.ratMap]⟩)⟩⁻¹), by
    simp [← Prod.inv_mk, (ext u : t = .scalar _ (ξ.map _)), o]; apply ρ⟩) ⟨_, κ.preimage_val h.2,
    fun ⟨_, _, rfl⟩ ↦ (K ..).elim fun _ ⟨_, a, b⟩ ↦ ⟨⟨_, ρ ..⟩,
    (m (radicalElt ..)).1 ⟨a, 1, by simp⟩, b⟩⟩).imp fun c ↦ .imp_right fun H a b f g o i ↦ ?_
  · simp [ideleAbs_eq_one_of_mem_unitary (x := p.2.toUnitary.1.det) p.2.det.2, pow_succ',
      prod_smul_left, prod_smul_right, mul_assoc, e.measurableEmbedding.lintegral_map]; rfl
  · rw [lintegral_prod, ← lintegral_orbitMeasure_lintegral (ν := @count (principalAdeleUnits E) _),
      lintegral_prod]
    congr!; simp (disch := fun_prop) [↓lintegral_count, lintegral_tsum,
      ← lintegral_orbitMeasure_lintegral (ν := @count V.Γ _)]; rfl; repeat fun_prop
  let k y h := ∑' x : (E ∙ ·) ⁻¹' {y}, constTermAt A (replicateCol _ x.1) (pairWeil _ _ a b (g,
    h) f)
  have ek : k (E ∙ X.k.col ()) = _ := funext fun h ↦ (((ofInjective _ ((smul_left_injective _ (mt
    (congrArg (_ * replicateCol _ ·)) (X.gram_lk.trans_ne (by simp)))).comp val_injective)).trans
    (subtypeEquivRight fun _ ↦ span_singleton_eq_span_singleton.symm.trans comm)).tsum_eq
    _).symm.trans (tsum_congr (constTermAt_smul_k A X ·.ne_zero))
  have hk γ y h : k (γ • y) (V'.ratEmbed γ * h) = k y h := (((toPerm γ).subtypeEquiv fun x ↦ .trans
    (smul_left_cancel_iff γ).symm (by erw [smul_span]; simp)).tsum_eq _).symm.trans (tsum_congr fun
    x ↦ by simpa [constTermAt_eq_integral A a b,
    rep_apply_apply] using! congr(integral _ fun _ ↦ $(thetaTerm_ratEmbed_mul ..)))
  have km y : Measurable (k y) :=
    .tsum fun _ ↦ by simpa [constTermAt_eq_integral A a b, -sourceTerm_radicalElt] using
    (Continuous.stronglyMeasurable (by fun_prop)).integral_prod_left.measurable
  refine (integral_tsum_orbit V'.ratEmbed_injective (by rfl) km hk rfl fun _ ↦ .rfl).elim
    fun f O ↦ (H _ (km _) (fun n e h ↦ ?_) f (ek ▸ i)).elim fun p q ↦ .trans (congrArg _ (funext fun
    h ↦ ((hasSum_subtype_iff_of_support_subset fun y hy ↦ ?_).2 ((hasSum_constTermAt A a
    b).summable.hasSum.tsum_fiberwise _)).tsum_eq.symm)) (ek ▸ q ▸ (O (.inr p)).2.1)
  obtain ⟨⟨⟨⟩, rfl⟩, p, q, r⟩ := e, A.sourceTerm_levi V' (a / upsilonU1) b 1 1 n,
    (X.homTarget_zeroTerm_pairWeil W · (b / upsilonU1) n 1 1 · · 1),
    map_mul (pairWeil W' V' a b) (1, n) (g, h)
  clear * - p q r ek; simp_all [lineTerm, radicalElt_mul_iAdelic, η]
  obtain ⟨⟨x, rfl⟩, hx⟩ := not_forall.1 (hy <| tsum_congr · |>.trans tsum_zero)
  exact (V'.witt (.of_ne_zero (x := x) (hx <| · ▸ o _)) ⟨_, X.gram_lk⟩ (X.gram_kk ▸ by_contra
    (hx <| ite_eq_right ·))).imp fun _ e ↦ (map_span ..).trans (by simp [← e]; rfl)
