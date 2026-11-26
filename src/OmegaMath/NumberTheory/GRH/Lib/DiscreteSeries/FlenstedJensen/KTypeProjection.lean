import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.FlenstedJensen.PsiBasic
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Flensted-Jensen's function, the coefficient of the lowest K-type of a discrete
series. It is treated for U(p,q) and parameters with a gap, with the integrand written by principal
minors and a decay bound whose constant does not depend on the parameter. Existence of the discrete
series is not assumed. Source: M. Flensted-Jensen, Discrete series for semisimple symmetric spaces,
Ann. of Math. 111 (1980) 253-311; B. Sun, Matrix coefficients of cohomologically induced
representations, Compositio Math. 143 (2007), Thm 1.1 (arXiv math/0403440); A. Knapp, Representation
Theory of Semisimple Groups (1986), ch. IX.

This file: Lowest K-type occurs once; K-types outside the cone above it do not occur. -/

open Matrix MeasureTheory ComplexConjugate Norms.L2Operator ComplexOrder
attribute [local simp] diagTorus Pi.star_def ne_of_gt weightMinors_unitary_inv

/-- Let l = 2λ be a parameter of some gap, x, b in U(diag ε), ν K-dominant. Then ∫_K
conj(m_ν(k)) ψ_λ(xkb) dk is c_Λ ψ_λ(x)ψ_λ(b), c_Λ = ∫_K |m_Λ|², if ν = Λ, and 0 if ν ≠ Λ and
ν − Λ lies outside `HCParam.rootCone`.

Known result: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series. -/
lemma integral_conj_weightMinors_mul_dsCoeff {n} [Fintype n] {ε l h} (hg : @HasGap n _ ε l h) (x b :
  USign ε) {ν} (hν : IsKDominant ε (-l) ν) (hz : ν = l.lowestKType ∨ ν - l.lowestKType ∉
  l.rootCone) : ∫ k, conj (weightMinors ν k.1) * l.dsCoeff ↑(x * k * b) ∂haarK ε = if ν =
  l.lowestKType then l.lowestKType.kTypeNormSq * (l.dsCoeff x * l.dsCoeff b) else 0 := by
  obtain ⟨o, ho, N, hN, hz⟩ : ∃ o, _ ∧ ∃ N : ℕ, N = o ⬝ᵥ (ν - l.lowestKType) ∧
    (N = 0 ↔ ν = l.lowestKType) := hz.elim (⟨-l, by simp [·]⟩) (not_forall₂.1 · |>.imp fun o h ↦
    ⟨h.1, _, Int.toNat_of_nonneg (by lia), by aesop⟩)
  have oj : o.Injective | i => by have := ho i; grind [HasGap]
  obtain ⟨⟨T, D⟩, c, _, rfl, ca, _⟩ := (by grind [IsKDominant, mt (ho _ _), HasGap, Pi.neg_apply,
    paramAddRho] : (Unit → IsKDominant ε o ν) ∧ IsKDominant 1 (-o) (-paramAddRho l)),
    exists_analytic_path (.inl rfl) b (by simp)
  let S y (k : maxCompactU ε) := k.1.1.1ᴴ * y * k
  obtain ⟨I, p, Z⟩ := neg_injective.comp oj, l.analyticAt_dsCoeff,
    isCompact_univ.eventually_forall_mem (x₀ := 1) (fun y k ↦ S ((blockDiagPart ε x)⁻¹ * x) k * y)
    {z | z.IsAccretive} (by simp [S, IsAccretive.setOf_mem_nhds])
  rw [← mul_boole]; generalize (1 : ℝ) = t; revert t
  refine congrFun (AnalyticOnNhd.eq_of_eventuallyEq (fun t _ ↦
    ((IsAnalyticFamily.of_analyticAt (.prodMk ?_ ?_) (fun (b, y, z) ↦
    y * l.dsCoeff (z * b)) fun k ↦ have := p (x * ↑k * c t); ?_).analyticAt_integral
    _).restrictScalars.comp (ca t)) (fun t _ ↦ have := (p (c t)).restrictScalars (𝕜 := ℝ); ?_)
    (.mono ((ca 0).continuousAt (isCompact_univ.eventually_forall_mem S _ fun k _ ↦ (Z.and (.and
    PosDef.one.isAccretive.setOf_mem_nhds (eventually_exists_torus_entire_factor I D
    Z))).filter_mono (by simp [*, S, ← maxCompactU.coe_inv])))
    fun t h ↦ ?_)) <;> try fun_prop (disch := simp)
  choose U W A C tC _ _ P _ e using by simpa [S, -Subtype.forall] using h
  let G (j k : maxCompactU ε) y := weightMinors l.lowestKType (blockDiagPart ε x * j) * conj
    (weightMinors l.lowestKType k) / weightMinors (-paramAddRho l) (S ((blockDiagPart ε x)⁻¹ *
    x) j * y); have : Continuous (fun j k ↦ weightMinors ν (k * j⁻¹).1 * G j k
    (S (c t) k)).uncurry := by unfold G S; fun_prop (disch := simp [U])
  simp only; rw [dsCoeff, dsCoeff_eq_flenstedJensen hg (one_mem _) (by simpa using W 1),
    flenstedJensen, flenstedJensen]; field_simp
  simp_rw [← integral_prod_mul, ← integral_mul_const]
  refine .trans ?_ (((measurePreserving_mul_prod ..).fubini (integrable_of_compactSpace
    this)).2.trans (integral_eq_of_circle_mean (fun θ ↦ map_mul_right_eq_self _ (1,
    diagTorusK (θ.toCircle ^ o ·))) (integrable_of_compactSpace this) fun (j, k) ↦ .trans ?_
    (((isHolOfWeight_weightMinors oj k T).circle_mean_weightMinors oj T (fun _ ↦ mem_maxCompactU.1
    j⁻¹.2) (fun s ↦ s ^ N * G j k (A k s) / diagChar (-paramAddRho l) (C k)) ?_).trans ?_)))
  · congr with k; rw [dsCoeff_eq_flenstedJensen hg (mul_mem (blockDiagPart_mem x) (mem_maxCompactU.1
      k.2)), flenstedJensen] <;> simp [G, S, mul_assoc, ← maxCompactU.coe_inv]
    simpa [S, mul_assoc, ← maxCompactU.coe_inv] using U 1 k
  · congr with θ; set s := θ.toCircle; have :=
      D.weightMinors_mul_borel I (P k s s.norm_coe.le j).det_ne_zero
      (by simp) (((isBorelMatrix_diagonal s).mul (tC k)).mul (isBorelMatrix_diagonal s⁻¹))
    simp at this; rw [mul_assoc, ← (A k s).mul_assoc, ← e] at this
    simp [G, S, mul_assoc, conj_weightMinors, dotProduct, diagChar, hN, ← _root_.zpow_mul,
      ← zpow_sum_of_ne_zero,
      mul_sub, zpow_sub₀, ← s.coe_inv_eq_conj, ← zpow_natCast s.1] at *; simp [*]; field_simp; simp
  simp_intro s r; fun_prop (disch := simp [*, S, -det_mul, IsAccretive.det_ne_zero])
  simp [zero_pow_eq]; grind
