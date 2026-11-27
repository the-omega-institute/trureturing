/- GID: D5/S3/Zeros/GRH/New/Curve/FrameSections
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Curve/FrameSections
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Curve.FrameSections. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/FrameSections.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Curve.TightFrameExists
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Tight frames and an integral standard theta function. The lattice of the standard theta function
has tight frames (substitutes for an orthonormal basis) of every large length, Fourier inversion
relates the function to products of theta functions of the CM curve, the scaled function has
integral torsion values with bounded conjugates, and jet bounds pass to its translates. Eutactic
stars, the isogeny formula for theta functions and integrality via torsion values are known. Related
work: Conway–Sloane, Low-dimensional lattices V, 1989; Finis, Divisibility of anticyclotomic
L-functions and theta functions with CM (Lemma 3.1), 2006; Mumford, On the equations defining
abelian varieties I, 1966.

Set-up for this proof: dictionaries between two encodings of the same objects.

This file: The jet series of a Weil vector is the Taylor series of its theta function. Curve theta
products along tight frames: translates, jets, integral values, relation to the vacuum. -/

open Finset CMLattice Complex ComplexConjugate Fintype MeasureTheory MvPowerSeries NormedSpace
  NumberField Space WeilData

/-- For V with all signs 1 and f in the finite part, the Taylor series at 0 of u ↦ Θ_f(u·a·v) is
obtained from T_a f by substituting v_i·u for each variable z_i. -/
lemma Space.taylor_line_eq_subst_jetSeries {E n} [Field E] [CMType E] [WeilData E] [Fintype n] {V :
  Space E n 1} {f} (hf : f ∈ V.finitePart) a v : taylorAtZero (entireTheta f <| a • · • v) =
  (V.jetSeries a f).subst (linearSeries fun _ ↦ v ·) := by
  ext k
  let L := a • ∑ p, innerSLFlip ℂ (v p) ∘SL .proj p
  rcases (hasFPowerSeriesAt_iff (p := .ofScalars ℂ _) (z₀ := 0).2
    (.of_forall fun t ↦ by simpa [mul_pow, mul_assoc, div_eq_inv_mul, mul_left_comm] using
    hasSum_integral_of_dominated_convergence (μ := realMeasure _) _ (by fun_prop [realVac]) (fun _ ↦
    .of_forall (by simp; grw [L.le_opNorm ·, norm_apply_le])) (by simp [Summable.mul_right,
    expSeries_div_summable]) (by simpa [tsum_mul_right, exp_eq_tsum_div, Real.exp_eq_exp_ℝ,
    mul_assoc] using (integrable_exp_mul_realVac (_ * _)).mul_const _) (.of_forall fun w ↦
    .mul_right
    (realVac w * f (realVec w)) (expSeries_div_hasSum_exp (t * L w))))).choose_spec.factorial_smul 1
    k, (jet_subst_linearSeries (.replicateCol _ v) (.X () ^ k) (V.jetSeries a f)).symm
  simp_all [entireTheta_eq_integral, L, mul_sum, linSubst, MvPolynomial.X_pow_eq_monomial, ↓map_pow,
    mul_assoc, ↓theta_integrated,
    holCoord_eq, iteratedDeriv, mul_left_comm, exp_eq_exp_ℂ, linearSeries]

variable {P s} {E : Type} {n} [Fintype n] {ε} (V : Space (Parameters.E P s) n ε) [i : V.IsStd]

lemma Space.eq_zero_of_jetSeries_eq_zero [Field E] [CMType E] [WeilData E] {V : Space E n 1} {f}
  (hf : f ∈ V.finitePart) {a} (ha : a ≠ 0) (h : V.jetSeries a f = 0) : f = 0 := eq_zero_of_realVec
  fun y ↦ by simpa [entireTheta, realVac, *] using congr($(eq_of_taylorAtZero_eq (g := 0) (by
  fun_prop (disch := aesop)) (by simp) ((taylor_line_eq_subst_jetSeries hf a y).trans
  (h ▸ (subst_coe 0).trans (by aesop)))) a⁻¹)

/-- Let all signs be +, f ∈ 𝒲_f, G_i entire, and Θ_f(cz) = ∏G_i(μ_{c,i}·z) for all c, z. Then
θ(f) = ∏G_i(0), and for every c the series T_c f is the product of the Taylor series of the
G_i at the linear forms μ_{c,i}·z. -/
lemma Space.jetSeries_eq_prod [Field E] [CMType E] [WeilData E] {V : Space E n 1} {f} (hf :
  f ∈ V.finitePart) {I} [Fintype I] {G : I → _} {μ : ℂ → I → _} (hG : ∀ i, Differentiable ℂ (G i))
  (h : ∀ c z, entireTheta f (c • z) = ∏ i, G i (μ c i ⬝ᵥ z)) : V.θ f = ∏ i, G i 0 ∧ ∀ c,
  V.jetSeries c f = ∏ i, (taylorAtZero (G i)).subst (linearSeries (μ c i)) :=
  ⟨by simpa [entireTheta, realVac] using h 0 0, fun c ↦ by
  ext α
  have H {v S} (f := fun _ ↦ ()) : (truncFinset ℂ _ S).eval v = (rename f (rescale v S)).coeff
    (α.mapDomain f)
  simp [truncFinset, coeff_rename, MvPolynomial.eval_monomial]; ac_rfl
  rw [← coeff_truncFinset_of_mem, MvPolynomial.funext fun v ↦ (H.trans ?_).trans H.symm,
    coeff_truncFinset_of_mem] <;> simp
  have := (taylor_line_eq_subst_jetSeries hf c v).symm
  simp_all [← coe_substAlgHom, PowerSeries.subst, substAlgHom_comp_substAlgHom_apply, mul_comm _
    (_ ⬝ᵥ v), linearSeries, -substAlgHom_apply, substAlgHom_X, rename_eq_subst, rescale_eq_subst]
  congr; induction @univ I _ using cons_induction <;> simp (disch := fun_prop) [*, ↓prod_cons,
    smul_smul, ← sum_smul, PowerSeries.rescale_eq_subst]
  tauto⟩

attribute [local simp] Parameters.areaScale WeilData.j dotProduct funext_iff mul_assoc
  thetaShift_prod

lemma Parameters.latticeModule_cmCurve : P.cmCurve.latticeModule =
  QuadField.scaledIdeal _ (P.Ω₀, 1) := by grind [Ω₀, cmCurve]

/-- The period Ω₀ lies in the lattice of the CM datum 𝓔 (`Parameters.cmCurve`). -/
lemma Parameters.omega₀_mem_cmCurve_lattice : ↑P.Ω₀ ∈ P.cmCurve.Λ :=
  (latticeModule_cmCurve ▸ QuadField.mem_scaledIdeal).2 (by simp)

@[simp] lemma Parameters.norm_map_psi₀ {F R} [NormedField R] [FunLike F ℂ R] [MonoidHomClass F ℂ R]
  (ι : F) z : ‖ι (stdLattice.psi₀ (P.E s) z)‖ = 1 :=
  ((ι : _ →* R).isOfFinOrder (isOfFinOrder_ψf _)).norm_eq_one

/-- For V standard, (w, m) a tight frame of length M, δδ̄ = N ≠ 0, a ∈ Λ, area(C) =
|a|²M√d/(2N): a product of degree-m_i monomials at (a/δ̄)w_i†z_k comes from some F ∈ 𝒲_f,
compatibly with rational translations (theta values, Taylor series), integral-valued, with data
`Space.VacuumExpansion`.

Tight frames and an integral standard theta function. -/
lemma Parameters.exists_finitePart_of_isTightFrame {M N : ℕ} {I} [Fintype I] {w m} (δ : 𝓞 P.K) (h0 :
  N ≠ 0) (hN : δ * conj (δ : ℂ) = N) (hw : IsTightFrame w m M) (x : I × n → _) (hx : ∀ i,
  CMLattice.monomialDeg (x i) = m i.1) ⦃C : CMLattice P.d⦄ ⦃a⦄
  (ha : a ∈ C.Λ) (hA : C.area = ‖a‖ ^ 2 / N * M * √P.d / 2) : ∃ F ∈ V.finitePart,
  (∀ γ, let G i := C.twistedTranslate (m i.1) (a / conj ↑δ * -∑ τ,
    Φ τ (γ i.2) * conj (Φ τ (w i.1))) (C.monomialSection (x i))
  V.θ (V.ϱ (finVec (finiteImage γ)) F) = ∏ i, G i 0 ∧ ∀ c, V.jetSeries c (V.ϱ (finVec (finiteImage
    γ)) F) = ∏ i, (taylorAtZero (G i)).subst (linearSeries fun y ↦ if y.2 = i.2 then a / conj ↑δ /
    P.areaScale * c * conj (Φ y.1 (w i.1)) else 0)) ∧ (∀ p [Fact p.Prime] [PadicPlace p] x, ‖ιₚ
  (F (finVec x))‖ ≤ 1) ∧ Nonempty (V.VacuumExpansion (algebraMap P.K _ δ) N F) := by
  generalize e : a / _ = b
  obtain ⟨⟨⟩, ⟨⟩⟩ := (div_eq_iff (by grind [Nat.cast_ne_zero])).1 e, i.1
  exact have hl i {y} h := mul_comm _ (b * _) ▸ C.5 (herm_mem_quadInt y h (hw.1 i)) ha
    let A (i : I × n) : _ →L[ℂ] ℂ := ∑ τ, (b / P.areaScale * conj (Φ τ (w i.1))) • .proj (τ, i.2)
    have B u v : (∑ i, (m i.1 • C.hermitianForm).pullForm (A i)) u v = star u ⬝ᵥ v := by
      have := by simpa [*] using (area_pos C.1).ne'
      convert congr(∑ k, ∑ σ, ∑ τ, conj (u (τ, k)) * v (σ, k) / M * $(hw.2 τ σ)) <;>
        simp [A, *, mul_pow, ← mul_conj', mul_sum, sum_prod_type_right, @sum_comm I]
      congr! 4
      simp [← ofReal_pow √_, field, Real.pi_nonneg, *]
    have R γ i : A i (realImage γ) = b * ∑ τ, Φ τ (γ i.2) * conj (Φ τ (w i.1)) := by
      simp [A, mul_sum, realImage, realCoord, val_scaleIdele_fst, Real.sqrt_div_self]
      have := NeZero.ne P.d; congr; simp [field, *]
    (V.exists_entireTheta_eq (b := conj (quadGen P.d) • 1) (S := ∏ i, C.monomialSection (x i) ∘ A i)
      (by simp [traceOne, quadGen, map_ofNat]) B (by exact coe_mem_Ô (algebraMap _ _ δ)) h0 ((Φ
      1).injective (by simpa)) (by rw [prod_fn]; fun_prop) fun γ hγ ↦ by simp [R, normalizedShift,
      riemannForm_pullForm, ← mul_sum, canonicalMultiplier, multiplier_eq_canonicalMultiplier,
      by simpa using (hl · <| hγ ·), ← Complex.exp_sum, hx _ ▸ thetaShift_of_mem
      (monomialSection_mem ..), ← Complex.exp_nsmul, mul_left_comm (m _ : ℂ)]).imp fun F ⟨hF, _,
      D⟩ ↦ (fun H ↦ ⟨hF, H, fun _ _ _ x ↦ (exists_finiteImage_approx hF x).elim fun γ e ↦
      (exists_forall_mul_mem_Ô (finiteImage γ)).elim fun M h ↦ by
    grw [← θ_ϱ, ← e.2, (H γ).1, map_prod, norm_prod, Finset.prod_le_one₀ (by simp) fun i _ ↦ ?_]
    grw [← hx, ← mul_zero 0, C.norm_translate_le_naiveHeight_pow (N := 0) _ _ (N * M) _ _
      (C.norm_monomialSection_le _)] <;> simp [*]
    simpa [← hN, mul_left_comm b, ← mul_sum] using! C.latticeModule.smul_mem δ (@hl _ (M * _) (by
      simpa [finiteImage, mul_left_comm] using h.2 _)), D⟩) fun γ ↦
      jetSeries_eq_prod (rho_finVec_mem_finitePart _ hF) (by fun_prop) (by
      simp [entireTheta_translate_finiteImage _ V B, *]; simp [A, sum_prod_type, mul_sum]; grind)
