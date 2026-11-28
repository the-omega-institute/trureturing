/- GID: D5/S3/Zeros/GRH/Lib/Shimura/ComplexTheta/PeriodVanishing
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/ComplexTheta/PeriodVanishing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.ComplexTheta.PeriodVanishing. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/ComplexTheta/PeriodVanishing.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.SiegelWeil.SingularForms.SingularForms
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.FourierCoefficient
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Fourier coefficients of theta lifts as periods over stabilisers. Here one
non-degenerate coefficient of a theta lift to a split unitary group is unfolded once by Witt's
theorem. Hence a form on the definite U(n) orthogonal to the theta kernels of the split space has
zero period over the complementary unitary group. Source: P. Walls, The theta correspondence,
periods of automorphic forms and special values of standard automorphic L-functions, arXiv
1501.01565 (2015), Prop. 2.1.1; S. Rallis, On the Howe duality conjecture, Compositio Math. 51
(1984) 333–399.

This file: Vanishing theta descent to the split group forces zero period over the stabiliser. -/

open ContinuousMap Subgroup AddChar G Gf MatMul Matrix MeasureTheory Space WeilData Splitting

attribute [local simp ←] Circle.coe_inv_eq_conj conjTranspose_mul ext_iff add_mul map_add map_mul

attribute [local simp] IsIntMatrix Matrix.mul_apply val_scaleIdele_snd inclMatrix ite_mem mul_add
  mul_assoc sq matToVec

/-- Let Y on U(I_n), n = n₁ + n₂, be continuous, left invariant under rational points, fixed by
the part of K₀ = `Kf` above T ∪ T̄, and satisfy `DescentsVanish` for ℍ^{n₁}, υ^{n₁}, T. Then the
period ∫Y(h₁u)du over [U(I_{n₂})] vanishes for every h₁ in the first block.

Known result: Fourier coefficients of theta lifts as periods over stabilisers. -/
lemma period_eq_zero {E n n₁ n₂} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n₁]
    [Fintype n₂] {T Y} (c : Continuous Y) (hY : (stdSpace E n).Γ.FixesLeft Y) (hK : HasLevel Y
    (Kf E n ⊓ supportedOn n T)) (o : n₁ ⊕ n₂ ≃ n) hs (h :
  DescentsVanish (hypSpace E n₁) (stdSpace ..) (1 * upsilonU1 ^ Fintype.card
  n₁) T Y) h₁ : ∫ u, Y (blockEmb (s₁ := 1) (e := o) hs (h₁, u)) ∂(stdSpace ..).quotMeasure = 0 := by
  set V := stdSpace E n
  let i := (blockEmb hs).comp (.inr _ (G E _))
  let t h := h⁻¹ * blockEmb hs (h₁, 1)
  have j := isClosedEmbedding_blockEmb (E := E) hs
  have : Continuous i := j.continuous.comp (.prodMk_right 1)
  have iΓ : (stdSpace ..).Γ = V.Γ.comap i := Subgroup.ext (by simp [i, V])
  let y := (inclMatrix E (o ∘ .inl)).map toAdele
  have hm g : mat (E := E) (blockEmb hs g) * y =
    y * g.1.mat := by simp [reindex_equiv o, blockEmb, y]
  have fy {g} : g ∈ i.range ↔ g.mat * y = y := ⟨(·.choose_spec ▸ by simp [i, hm]), fun h ↦
    ((U.mem_range_sum stdForm_sum (g := (reindex o.symm hs g).toUnitary).2 (by simp)).2 (by
    simpa [reindex_equiv o, y] using! h)).imp' toUnitary.symm fun a e ↦
    (reindex _ hs).symm_apply_eq.2 (ext_mat (by simpa using! congr(($e).1.1)))⟩
  let η (d : G E (1 : n → _)) := d.mat * y
  let Φ h := ‖vacuumFn ((scaleIdele E).1 • matToVec (η h))‖ ^ 2
  let e g u :=
    stdAddChar E (invDifferentIdele E * ((1 - idemAdele T.conjClosure) * u ⬝ᵥ matToVec (η g)))
  obtain ⟨hr, ce : Continuous e, _ : Continuous Φ⟩ :=
    isRapid_of_isCocompact c hY V.exists_isCompact_of_definite, by
    fun_prop [matToVec], (isVacuum_vacuumFn (s := 1).cont.comp (by fun_prop [matToVec])).norm.pow 2
  have h u : let F g := e (t g) u * Φ (t g) • Y g; let q := ((stdSpace ..).Γ.map i).qms
      Integrable F q ∧ integral q F = 0 := ?_
  let B g := ∫ h, Y (i h * (t 1 * g⁻¹)) ∂(stdSpace ..).quotMeasure
  have cB : Continuous B := hr.bounded.elim fun C b ↦ continuous_of_dominated (by fun_prop) (by
    simp [b]) (integrable_const C) (.of_forall (by fun_prop))
  have fx {a b} (e : η a = η b) : B b = B a := (fy.2 ((mul_smul _ a y).trans (inv_smul_eq_iff.2
    e))).elim fun v h ↦ by simpa +zetaDelta [← mul_inv_eq_of_eq_mul h, ← mul_assoc] using
    ((stdSpace ..).integral_comp_mul_right v (by simp +contextual [map_mul, *]) (F :=
    (Y <| i · * (t 1 * a⁻¹)))).1
  by_contra p0
  have ⟨φ, f, z⟩ := CompletelyRegularSpace.exists_BCNN (((isCompact_univ.prod isCompact_Kf).diff
    ((Complex.isOpen_re_gt 0).preimage (cB.div_const (B 1)))).image ce).isClosed (x := e 1) ?_
  have H φ := (h 0).1.bdd_mul (by fun_prop) (.of_forall (norm_coe_le_norm φ <| e <| t ·))
  have L := strongIntegral_apply _ (fun g ↦ .smulRight (evalCLM (M := ℂ) ℂ (e (t g))) _) H
  have z₁ := ContinuousLinearMap.ext_on (g := 0) (stone_weierstrass_span ⟨⟨{φ | ∃ u, ∀ g,
    φ (e g) = e g u}, fun ⟨u, _⟩ ⟨v, _⟩ ↦ ⟨u + v, by simp [*, e, map_add_eq_mul]⟩⟩, 0, by simp [e]⟩
    (fun φ ⟨u, h⟩ ↦ ⟨-u, by simp [e, *, map_neg_eq_inv]⟩) fun x y c ↦ by ext u; exact (c (.mk (· u))
    (by tauto))) fun φ ⟨u, hu⟩ ↦ (L φ).trans (by simp [hu, ← (h u).2, e])
  refine (exists_integral_stages_eq_mul _ _ volume Measure.count (i.comp (.snd Unit _)) (j.comp
    (.prodMap ⟨.of_subsingleton 1, by simp⟩ .id)) ((fun g ↦ φ (e g) * Φ g * (B g / B 1)) ∘ t) (by
    simp_intro h [mul_nonneg_iff_pos_imp_nonneg, Φ]; by_contra! ⟨a, b, l⟩
    have ⟨d, hd, ed⟩ := (fun x ↦ witt_Ohat_of_orthonormal (X :=
      inclMatrix _ (o ∘ .inl)) x ((U.gram_invariant (t h).2 ..).trans x))
      (by simp) (by simp) (by simpa [vacuumFn, η, y] using b)
    have k : η ((t h).1, d) = η (t h) := by simp [η, y, Prod.ext_iff] at ed ⊢; tauto
    exact a.ne' (z _ ⟨(_, d), ⟨⟨⟨⟩, hd⟩, (fx k ▸ l).not_gt⟩, by simp [e, k]⟩))
    ((Continuous.tendsto (by fun_prop) (t 1)).eventually_ne (by simp [-Complex.norm_exp, B, t, i,
    f, p0, Φ, vacuumFn, η, y]))).elim fun R ⟨r, q⟩ ↦ mul_ne_zero r p0 ((z₁ ▸ L (.mk (φ ·)) :).trans
    (q _ (by fun_prop) (Set.forall_mem_image.2 ?_) (H (.mk (φ ·))) _ fun g ↦ ⟨1, ?_⟩)).symm <;>
    simp +contextual [Φ, e, η, t, ← map_inv, i, hm, hY, V]
  simp [B, t, i, p0]
  rintro ⟨d, ⟨⟨-, hd⟩, h : ¬0 < (B d / _).re⟩, a⟩
  simp [p0, t, i, ↓← fx (b := (1, _)) (show η d = η (closurePart T d) from Matrix.ext fun p q ↦
    (invDifferentIdele E).mul_right_inj.1
    (sub_eq_zero.1 (eq_zero_of_forall_stdAddChar_eq_one fun u ↦ by
    erw [← div_eq_one.2 (congrFun a (Pi.single (p, q) u)), ← map_sub_eq_div]; simp [η, y]
    split <;> ring_nf))), B,
    ← hK _ ⟨componentOn_mem_Kf hd, componentOn_mem_supportedOn⟩ (_ * (_ * (1, _)))] at h
  let A := hyperbolicSplitting E n₁
  have ⟨c', c0, hc⟩ := isAdapted_homSource A V (h :=
    ⟨isOrthoIntegral_hypSpace.2.of_eq_submatrix_mul (id ⊕ᵥ Empty.elim) .one (by
    simp [lAdelic, kAdelic, A, hyperbolicSplitting])⟩).mixedTerm_omega_vacElem
  simpa [-mulVec_smul, ↓sourceTerm_levi, sourceTerm_eq_adapted_mixedTerm, by simpa [V] using hc, η,
    t, hm, e, Φ, V, c0, centreCoeff, invDifferentIdele, star_mulVec, dotProduct_mulVec,
    pairWeil_apply, integrable_const_mul_iff, mul_left_comm _ c',
    adelicHeis, vacElem_apply_eq_prod_lineTheta, Finset.univ_eq_empty, Splitting.thetaTerm,
    Subsingleton.eq_one (G.onHom (1, _)), funext_iff] using!
    A.centreCoeff_eq_integral_stabilizer (IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
    _ ⟨_, fun h ↦ by simp_rw [enorm_mul, ENNReal.tsum_mul_right]; grw [(exists_tsum_thetaTerm_le
    ..).choose_spec.choose_spec, ← ofReal_norm, ← ENNReal.ofReal_mul' (by simp), mul_right_comm,
    mul_assoc, (hr _).choose_spec]; rfl⟩) ⟨1, by simp [V]⟩ (by
    erw [iΓ, map_comap_eq, inf_comm, ← map_comap_eq]
    simp [↓fy, mat_ratEmbed, V, y, ← (@toAdele E ..).injective.eq_iff]) c hY (x₀ :=
    inclMatrix E (o ∘ .inl)).2.imp_right congr(A.centreCoeff _ $(h (ϱ _ (((A.homSource V).kAdelic *
    (adaptedHomBasis n₁ V).1) *ᵥ (scaleIdele E).1 • star ((1 - idemAdele T.conjClosure) • u))
    (vacElem _)) (by simp +contextual)) (A.levi (scaleIdele E • h₁.toUnitary, 1))).symm.trans
