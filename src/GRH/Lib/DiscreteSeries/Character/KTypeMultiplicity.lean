import GRH.Lib.DiscreteSeries.Character.LaurentAlternants
import GRH.Lib.GLn.SchurModule.SchurOrthogonality
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Weyl character and dimension formulas for U(n) and products of unitary groups. The
character formula is stated for Schur modules of products of general linear groups at elements with
distinct eigenvalues, then carried by Schur's lemma to characters of U(p)×U(q) defined as means of
products of principal minors. The dimension is obtained as a limit at 1. Source: H. Weyl, The
Classical Groups (1939), ch. VII; Fulton and Harris, Representation Theory (1991), Lectures 24-25.

Part of: Discrete series character on the compact Cartan by orbital integrals; formal degree (known
result; see Lib.DiscreteSeries.Character.FormalDegree).

This file: Weyl character and denominator formulas for U(p)×U(q); conjugacy into the torus. K-type
multiplicities of discrete series: integer, one at lowest type, supported in cone. -/

open Finset Complex Equiv HCParam Matrix
variable {n} [Fintype n] {ε} {l ν : @HCParam n ε} (k : maxCompactU ε)

/-- The continuous class function χ_ν(g) = c_ν⁻¹ ∫_K m_ν(y⁻¹gy) dy on K = U(diag ε) ∩ U(n), with
c_ν = ∫_K |m_ν|². -/
noncomputable def HCParam.kTypeChar (ν : HCParam ε) : C(maxCompactU ε, ℂ) := ⟨fun g ↦
  (∫ y, weightMinors ν (y⁻¹ * g * y).1 ∂haarK ε) /
  ν.kTypeNormSq, (haarK ε).restrict_univ ▸ (continuous_parametric_integral_of_continuous
  (by fun_prop (disch := simp)) isCompact_univ).div_const _⟩

attribute [local simp] kTypeChar BlockTriangular blockDiagonal'_apply toBilin'_apply'
  toSquareBlock_def Orbital.torusEval Units.smul_def blockHom mem_maxCompactU mem_blockDiagAlg
  weylRep diagTorus zpow_add₀

lemma Orbital.exists_maxCompactU_of_blocks [DecidableEq ℤˣ] (g : ∀ _, Matrix _ _ ℂ) (h : ∀ τ,
  (g τ)ᴴ * g τ = 1) : let e := sigmaFiberEquiv ε
  ∃ y : maxCompactU ε, y = reindex e e (blockDiagonal' g) ∧ y.1.1.1.toSquareBlock ε = g := by
  intro e; set y := reindex e e _; have m : y ∈ blockDiagAlg ε := by aesop
  use ⟨U.of IsHermInvolution.isUnit y ?_, mem_maxCompactU.2 m⟩, rfl,
    (by aesop : (y.submatrix e e).blockDiag' = _)
  simp [↓Commute.right_comm (m _ rfl), y, ← blockDiagonal'_mul, h, ← Pi.one_def]

/-- Weyl's character formula for K. For l injective, ν K-dominant for the order −l, χ_ν =
`HCParam.kTypeChar` on the diagonal torus is a Laurent polynomial and ∏(x_a−x_b)·χ_ν(x) = Σ_{w∈W_K}
sgn(w) x^{(ν+δ)∘w}; product over ε_a = ε_b, l_b < l_a, δ_a counting such b.

Known result: Weyl character and dimension formulas for U(n) and products of unitary groups. -/
lemma Orbital.weyl_character_kTypeChar (hl : l.Injective) (hν : IsKDominant ε (-l) ν) :
  (∃ P, ∀ x, ν.kTypeChar (diagTorusK x) = torusEval x P) ∧ ∀ x, torusEval x (l.rootProd Eq) *
  ν.kTypeChar (diagTorusK x) = torusEval x (alternant ε (ν + l.lowerCount Eq)) := by
  let := Classical.decEq ℤˣ; let m τ := {i // ε i = τ}
  choose q hq using (exists_equiv_fin_lt_iff (n := m ·) hl.injOn.injective)
  let p τ := (q τ).symm.trans Fin.revPerm
  let g τ := ((List.ofFn (ν <| q τ ·.rev)).getD · 0)
  let κ τ k := (g τ (k - 1) - g τ k).toNat; let e τ := g τ 0 - diagramWeight (rankAt m) κ (τ, 0)
  have h τ : ∀ i, ν i.1 = e τ + diagramWeight (rankAt m) κ (τ, p τ i) :=
    (reindex_equiv (p τ).symm).1.2 fun ⟨k, o⟩ ↦ by
    simp [p, IsKDominant] at *
    induction k with grind [hq τ (.rev ⟨_, o⟩) (.rev ⟨_ - 1, tsub_lt_of_lt o⟩)]
  let b : maxCompactU ε →* ∀ τ, GL (m τ) ℂ := .pi (blockHom ε · |>.comp (.mk' (⟨·,
    fun _ ↦ by aesop⟩) (by tauto))); let R := (weylRep κ e).comp b
  have ⟨v, w, M⟩ : ∃ v w, ∀ k, w ⬝ᵥ R k *ᵥ v = weightMinors ν k := ⟨_, _, fun k ↦ by
    erw [← dotProduct_mulVec (weylEval m κ _), weylRep_coeff_eq_prod_weightMinors p,
      weightMinors_eq_det_zpow_mul_prod (by simp) _ _ (neg_sum_abs_le_and_le_sum_abs _)]
    simp_rw [← h, weightMinors_eq_det_zpow_mul_prod (b k _).det_ne_zero _ _
      (neg_sum_abs_le_and_le_sum_abs ν ·), principalMinor_eq_det]
    rw [prod_mul_distrib, prod_zpow, prod_comm]; clear * -
    congr! <;> rw [BlockTriangular.det_fintype (b := ε)] <;> aesop (add 1% congr)⟩
  have : Continuous (R ·) := by
    simp [R, b]; fun_prop (disch := try exact (.inl <| b · _ |>.det_ne_zero))
  have ⟨B, hB, hL⟩ := exists_intertwining_mean (haarK ε) R R (vecMulVec v w)
  obtain ⟨a, d, z, ⟨⟩⟩ := fun k ↦ hL (traceLinearMap .. ∘ₗ .mulRight ℂ (R k)), hL ((toBilin'.1.flip
    w).flip v), scalar_of_commute_schur
    (exists_maxCompactU_of_blocks · · |>.elim fun y e ↦ by simpa [R, ← e] using! hB y)
  simp [mul_vecMulVec, vecMulVec_mul, vecMulVec_mulVec, ← dotProduct_mulVec, ← map_mul,
    weightMinors_unitary_inv, M, dotProduct_comm (_ *ᵥ _), conj_mul',
    ← smul_one_eq_diagonal, by simpa using M 1, -mem_maxCompactU] at a d
  simp [a, ← (mod_cast d : ν.kTypeNormSq = z), ne_of_gt, R, b, diagonal_apply, Subtype.val_inj,
    ← diagonal.eq_1, ← prod_zpow, -UnitsInt.univ, rootProd, ↓torusEval_alternant]
  use ⟨∑ i : WeylIndexFam m κ, ∏ τ, ∏ a, .single (Pi.single a.1
    (e τ + tableauWeight i τ a)) 1, by simp [mul_sum, schur_diagonal, -UnitsInt.univ]⟩, fun x ↦ ?_
  have F τ j : ({b | τ = _ ∧ l b < l (q τ j)} : Finset n) = (Iio j).map (q τ).asEmbedding :=
    ext (by simp [← hq, reindex_equiv (q τ).symm, m]; tauto)
  rw [← Fintype.prod_fiberwise ε, Fintype.prod_congr, mul_rotate', weyl_character q,
    ← prod_mul_distrib, BlockTriangular.det_fintype (by simp; order)]; simp_rw
    [det_classical, ← fun τ ↦ det_submatrix_equiv_self (R := ℂ) (q τ), reindex_equiv (q _),
    ← det_mul_column]
  rcongr; simp [(q _ _).2, lowerCount, F, h, pow_add, p, field]
  simpa [reindex_equiv (q _), (q _ _).2, F, m, (det_classical _).symm.trans (det_vandermonde _)]
    using fun _ ↦ prod_comm' (by simp)

/-- Weyl's denominator formula for K: for l injective, the product of x_a − x_b over ε_a = ε_b,
l_b < l_a, is the sum of sgn(w) x^{δ∘w} over permutations w preserving ε, where δ_a counts
such b. -/
lemma Orbital.weyl_denominator (h : l.Injective) : l.rootProd Eq = alternant ε (l.lowerCount Eq) :=
  eq_of_torusEval_eq (by simpa [kTypeNormSq, Pi.zero_def, ↓zero_add] using
  (weyl_character_kTypeChar h (ν := 0) (by tauto)).2)

lemma Orbital.exists_conj_diagTorusK : ∃ y x, y * diagTorusK x * y⁻¹ =
  k := have ⟨X, e, _⟩ := exists_expU_eq_maxCompactU k
  have h t : ((-Complex.I • X.1).toSquareBlock ε t).IsHermitian := by
    ext ⟨i⟩ ⟨j⟩; simpa [*, signMatrix, add_eq_zero_iff_eq_neg, field] using congr($(X.2) i j)
  (exists_maxCompactU_of_blocks _ (h · |>.eigenvectorUnitary.2.1)).imp fun _ m ↦ ⟨.exp ∘ _, by
    symm; ext : 3; simp [← e, exp_eq_exp_ℂ, ← Pi.exp_def, ← exp_diagonal, ← Matrix.exp_conj]
    convert congr(NormedSpace.exp (Complex.I • (blockDiagonal'
      $(funext (h · |>.spectral_theorem))).reindexRingEquiv ℂ (sigmaFiberEquiv _)))
    simp_all [← ext_iff, sigmaFiberEquiv]; grind [Subtype.heq_iff_coe_eq, I_sq]
    simp [m, ↓maxCompactU.coe_inv, map_mul, ← diagonal_mul_diagonal, ← smul_eq_mul_diagonal]; rfl⟩

open ComplexConjugate GlModule InnerProductSpace MeasureTheory Norms.L2Operator

attribute [local simp] IsKHighest inner_sub_left mul_assoc ne_of_gt rep_apply_apply

variable {n : Type} [Fintype n] {ε : _} {ν : @HCParam n ε} {A} {l : HCParam ε}

lemma Orbital.integral_mul_conj_kTypeChar {f : maxCompactU ε → _} (hf :
  Continuous f := by fun_prop) : ∫ k, f k * conj (ν.kTypeChar k) ∂haarK ε = ∫ y, (∫ k, conj
  (weightMinors ν k.1) * f (y * k * y⁻¹) ∂haarK ε) / ν.kTypeNormSq ∂haarK ε := by simpa [kTypeChar,
  ← integral_conj, integral_div, mul_div, mul_comm] using (integral_skew_product (fun y ↦
  ((measurePreserving_mul_left _ y⁻¹).mul_right _ y).2) (integrable_of_compactSpace (f :=
  (fun y k ↦ f (y * k * y⁻¹) * conj (weightMinors ν k)).uncurry))).2

lemma Orbital.integral_conj_kTypeChar : ∫ k, 1 * conj (ν.kTypeChar k) ∂haarK ε = ite (ν = 0) 1 0 :=
  .trans integral_mul_conj_kTypeChar (by
  split_ifs with h <;> simp [*, kTypeNormSq, Pi.zero_def, integral_conj]
  contrapose! h; exact AddMonoidAlgebra.single_left_injective h
    (eq_of_torusEval_eq fun t ↦ by simpa [torusEval, diagTorus,
    h] using (integral_mul_left_eq_self (μ := haarK ε) (weightMinors ν ·) (diagTorusK t))))

/-- Multiplicity of a K-type. Let l = 2λ have gap 500n³+A, n ≥ 1, ν be K-dominant. Then g ↦ ∫_K
χ̄_ν(k)ψ_λ(g⁻¹kg)dk is integrable, and deg_λ times its integral is some m∈ℕ; m = 1 for ν =
Λ = `HCParam.lowestKType` l, and m ≠ 0 forces ν−Λ∈`HCParam.rootCone` l. -/
lemma Orbital.exists_kType_multiplicity [Nonempty n] [hg : l.HasLargeGap A] (hν :
  IsKDominant ε (-l) ν) : let R (g : USign ε) := (∫ k : maxCompactU ε, l.dsCoeff
    (g⁻¹ * k * g :) * conj (ν.kTypeChar k) ∂haarK ε); Integrable R ∧ ∃ m : ℕ, l.formalDegree *
    ∫ g, R g = m ∧ (ν = l.lowestKType → m = 1) ∧ (m ≠ 0 → ν - l.lowestKType ∈ l.rootCone) := by
  obtain ⟨⟨d, k, j⟩, _, hw, hi, s, hs⟩ := hg.toL2_spec, (@isUnitaryRep_rightRegularL2 _ _ ε).1,
    isKHighest_dsGenerator hg, hg.isUnitaryCasimirGe_dsAction.1,
    exists_nat_ge (l.casimirKValue ν - l.casimirKValue l.lowestKType : ℝ)
  have := hw.finite_filtration hi; let W := l.dsAction.filtration ε dsGenerator
  let V := .ofLinearComb {v | l.IsKHighest dsAction ν v} ⟨0, by simp⟩ (by
    simp +contextual [smul_smul, mul_comm]) ⊓ W s; let b := stdOrthonormalBasis ℂ V
  -- `key x`: `ν.kTypeNormSq⁻¹ * ∫ k, conj (weightMinors ν k) * l.dsCoeff (x * k * x⁻¹) = ∑ i, |b i
  -- x| ^ 2`
  have key x := by
    let T := innerSL ℂ (hg.toL2 dsGenerator) ∘L rightRegularL2 x
    let φ := strongIntegral (haarK ε) fun k ↦ conj (weightMinors ν k) • T ∘L rightRegularL2 k
    have F : ∀ w, φ w = _ :=
      strongIntegral_apply _ _ fun _ ↦ by simpa using integrable_of_compactSpace
    let z t := ((φ.1 ∘ₗ hg.toL2).domRestrict (W t)).adjoint 1
    have H {s t y} hy (o : s ≤ t) : ⟪(z t).1, y⟫_ℂ = φ (hg.toL2 y) :=
      (LinearMap.adjoint_inner_left _ (⟨y, filtration_mono o hy⟩ : W t) 1).trans (by simp)
    have hZ t : l.IsKHighest _ ν (z t).1 := .of_E_eq_smul fun f c e h ↦
      Subtype.mk.inj (ext_inner_right ℂ (x :=
      ⟨_, E_mem_filtration (z t).2 e⟩) (y := (_ : ℂ) • z t) fun ⟨y, hy⟩ ↦ by
      let Φ b := ∫ k, weightMinors ν (b * k⁻¹) * y.1.1 (x * k) ∂haarK ε
      have a : HasFDerivAt Φ _ 1 := (IsAnalyticFamily.analyticAt_integral _
        (by apply IsAnalyticFamily.of_analyticAt (.prodMk ..) (fun (b, p, q) ↦
        weightMinors ν (b * p) * q) <;> fun_prop (disch := simp))).differentiableAt.hasFDerivAt
      have u (j : maxCompactU ε) : φ (rightRegularL2 j (hg.toL2 y)) = Φ j := .trans (by simp [F,
        ← weightMinors_unitary_inv, T, -map_mul, k]) (integral_mul_right_eq_self _ j)
      simpa +contextual [hi.1 f, e, H (E_mem_filtration hy e.symm), ↓inner_smul_left, H hy,
        @eq_comm _ c, apply_ite conj, by simpa using u 1] using (fderiv_eq_on_blockDiagAlg a
        (φ.1 ∘ₗ hg.toL2 ∘ₗ dsAction.ρ.flip y) (fun Y h ↦ by simpa [u ⟨_, h _⟩] using
        ((d Y y).map_clm φ).deriv) (by clear * - e; grind [mem_blockDiagAlg])
        ).symm.trans <| fderiv_eq_of_borel_equivariant ε a (o := -l) (by simpa) e.symm id (by
        simp +contextual [Φ, hν.weightMinors_oppBorel_mul hg.neg.1]))
    simpa [← congr(hg.toL2 $(b.sum_repr' ⟨_, hZ s, (z s).2⟩)), H (b _).2.2, ← mul_sum, F, T,
      -map_mul, ↓fun i ↦
      (F _).trans ((b i).2.1.integral_conj_weightMinors_smul isUnitaryRep_rightRegularL2 d hν T), k,
      ← inner_conj_symm (rightRegularL2 x _), ← inv_mul_eq_iff_eq_mul₀, by
      simpa using isUnitaryRep_rightRegularL2.form_apply_eq_form_inv_apply x⁻¹]
      using hw.coeffMap_eq_zero hi (d.isCoeffMap (φ - innerSL ℂ (hg.toL2 (z s)))) (fun g a ↦
      (φ - _).le_opNorm_of_le (by simp [rightRegularL2]; rfl)) (fun t a
      o ↦ by simpa [H o] using! (congrArg conj (mem_orthogonal_filtration_of_casimirK s hi hw
      (z (s ⊔ t) - z s) (by simp [(hZ _).casimirK_eq_smul,
      smul_sub]) hs (by simp +contextual [Submodule.mem_orthogonal', @H s]) t a o))) x⁻¹
  have I y := by simpa [Pi.mul_def] using (hg.memLp y).integrable_mul (hg.memLp y).star
  have M := by simpa [← mul_sum, ← integral_finsetSum, I, show ∀ a, ‖hg.toL2 (b a)‖ = 1 from
    b.norm_eq_one] using congr(∑ i, $(j (b i) (b i) 1))
  intro R; exact (funext fun g ↦ .trans integral_mul_conj_kTypeChar (by simp [← key,
    div_eq_inv_mul]) : R = _).symm.rec ((integral_skew_product
    (Measure.map_mul_right_inv_eq_self _ ·.1⁻¹) ((integrable_finsetSum ⊤ fun j _ ↦
    I (b j)).comp_snd (haarK ε))).imp_right fun t ↦ ⟨_, .trans (by simp [↓t]) M.symm,
    have N q x := by simpa [↓dsCoeff_inv] using integral_conj_weightMinors_mul_dsCoeff hg x x⁻¹ hν q
    ⟨by rintro rfl; simpa [← key, N, by simpa using dsCoeff_schur_orthogonality hg 1 1] using M,
      Function.mtr fun q ↦ by
    simpa [← key, N, q, (mt (by simp [·, rootCone]) q : ν ≠ l.lowestKType)] using M⟩⟩)
