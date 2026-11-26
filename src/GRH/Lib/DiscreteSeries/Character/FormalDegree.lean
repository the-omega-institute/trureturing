import GRH.Lib.DiscreteSeries.Character.SectorBound
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Discrete series character on the compact Cartan by orbital integrals, and the
formal degree. The form here is only for U(p,q) and parameters with large gaps, for the explicit
coefficient of the lowest K-type. It gives the formal degree, and the stable sum of elliptic orbital
integrals as Weyl's character of the compact form, exact in the compact dual measure. Source:
Harish-Chandra, Discrete series for semisimple Lie groups II: explicit determination of the
characters, Acta Math. 116 (1966), Thm 16 (with part I, Acta Math. 113 (1965), Thm 3); Knapp,
Representation Theory of Semisimple Groups (1986), Thm 12.7.

This file: Orbital integral times denominators is an antisymmetric Laurent polynomial confined by
K-types. Orbital integral is Weyl's character minus off-orbit part, which lacks low monomials.
Formal degree equals Weyl's dimension polynomial, and (−1)^{pq} times the sum over permutations of
elliptic orbital integrals equals p!q! times the conjugate of Weyl's character. -/

open Matrix MeasureTheory Finset AddMonoidAlgebra Equiv ConjAct InnerProductSpace ContinuousMap
  CStarRing Norms.L2Operator Fintype Metric Int HCParam

section

attribute [local simp low] Finsupp.sum mul_sum inner_sum inner_smul_left inner_smul_right inner_toLp
  prod_ite integral_apply lift_apply'

variable {n} [Fintype n] {ε} (l : @HCParam n ε)

/-- P is D times a formal series with coefficient 1 at x^a, each of whose exponents occurs in
the alternant `Orbital.alternant` of some μ in a + `HCParam.rootCone` l. -/
def Orbital.IsConeSeriesMultiple a (D P : ℂ[_]) := ∃ t : _ → ℂ, (∀ γ, P.1 γ = D.1.sum fun β c ↦
  c * t (-β + γ)) ∧ t a = 1 ∧ ∀ γ, t γ ≠ 0 → ∃ μ, (alternant ε μ).1 γ ≠ 0 ∧ μ - a ∈ l.rootCone

/-- Let λ have gap 500n³+10n⁵, Θ(x) = deg_λ∫ψ_λ(g⁻¹xg)dg on the torus, V_c = ∏(x_a−x_b) over
positive compact roots, D the (4n²+1)-th power of that over negative noncompact roots. Then
V_cDΘ is a W_K-antisymmetric Laurent polynomial with coefficients D convolved with t, t(Λ+δ)
= 1, t supported on W_K(Λ+δ+`HCParam.rootCone` l), δ_a = #{b : ε_b = ε_a, λ_b < λ_a},
Λ = `HCParam.lowestKType` l. -/
lemma Orbital.exists_laurent_orbital_integral [Nonempty n] (hg :
  l.HasLargeGap (10 * card n ^ 5)) : let δ := l.lowerCount Eq
  let Vc := l.rootProd Eq; let N := 4 * card n ^ 2 + 1; let D := (-l).rootProd Ne ^ N
      ∃ P, IsWeylAntisymm ε P.1 ∧ (∀ x, torusEval x P =
        torusEval x (Vc * D) * (l.formalDegree * ∫ g, l.dsCoeff (g⁻¹ * diagTorus ε x * g :))) ∧
        IsConeSeriesMultiple l (l.lowestKType + δ) D P := by
  intro δ Vc N D; let c (y : maxCompactU ε) := mk (y * diagTorusK · * y⁻¹); let W :=
    {w : Perm n // ε ∘ w = ε}
  let ψ := (mk fun p : _ × maxCompactU ε ↦ l.dsCoeffSmooth.1 (p.1⁻¹ * p.2 * p.1)).curry
  choose s ν hν hs using exists_sign_isKDominant hg.1; choose b v bv using
    exists_conj_diagTorusK (ε := ε)
  have ac {μ} h γ := alternant_coeff_of_isKDominant hg.1 h (hν γ) ▸ hs γ
    (alternant ε (μ + δ)).1 isWeylAntisymm_alternant
  have z {μ} h :=
    alternant_coeff_of_isKDominant hg.1 h h ▸ (ac h (μ + δ)).symm; simp [ite_eq_iff] at z
  let X γ := (s γ : ℂ) • (toHCParam ε (ν γ)).kTypeChar; have : Nonempty W := ⟨1, rfl⟩
  choose Y he hA using fun γ ↦ ((weyl_character_kTypeChar hg.1 (hν γ)).elim fun ⟨P, h⟩ k ↦ ⟨s γ * P,
    fun y x ↦ by simp [X, c, ← h]; exact .inl congr($(.trans (by group) (integral_mul_left_eq_self _
    y⁻¹)) / _), eq_of_torusEval_eq fun x ↦ (hs γ (torusEval x <| alternant ε ·) (by simp +contextual
    [IsWeylAntisymm, torusEval_alternant, ← det_permute', submatrix, funext_iff])).trans
    (by simp [← k, h, field])⟩ : ∃ P, (∀ y x, X γ (c y x) = torusEval x P) ∧ alternant ε γ = Vc * P)
  let e (i : Subtype (IsKDominant ε (-l))) := X (i + δ)
  let Φ p := (coeff p).lift _ ℂ _ X; let L := toLp (E := ℂ) 2 (haarK ε) ℂ
  have hX p x : torusEval x (Vc * p.1.lift _ ℂ _ Y) = ∑ w : W,
    w.1.sign * torusEval (x ∘ w.1) p := by
    simp [← hA, torusEval_alternant, det_apply', Fintype.prod_ite_zero, ← sum_filter]
    simp [torusEval, mul_left_comm]; rw [sum_comm, sum_subtype]; simp [funext_iff]
  have key p q (H : ∀ x, _) y x : Φ p (c y x) = torusEval x q := .trans (by simp [Φ, *])
    congr(torusEval x $(mul_left_cancel₀ (by simpa [*, ·] using ac (hν 0) (ν 0 + δ))
    (eq_of_torusEval_eq fun x ↦ (hX p x).trans (H x))))
  have av p := key (Vc * p) (∑ w : W, ⟨p.1.equivMapDomain (w.1.arrowCongr 1)⟩) (by simp [Vc,
    weyl_denominator hg.1, ← torusEval_comp_perm, (torusEval_comp_eq_mul_iff _).2
    (isWeylAntisymm_alternant _ (_ : W).2), ← mul_assoc, ← cast_mul])
  have pair {d D} (hd : ∀ y x, d (c y x) = torusEval x D) γ ψ : ⟪L (X γ), L (d * ψ)⟫_ℂ =
      D.1.sum fun β a ↦ a * ⟪L (X (-β + γ)), L ψ⟫_ℂ := by
    let S : ℂ[n → ℤ] := D.1.sum fun β a ↦ .single (-β) (star a)
    have hS x : torusEval x S =
      star (torusEval x D) := by simp [S, torusEval, ← Circle.coe_inv_eq_conj]
    trans ⟪L (Φ (S * .single γ 1)), L ψ⟫_ℂ; simp [L]; congr with k
    erw [← bv k, key _ (S * Y γ) fun x ↦ ?_, hd, he]
    simp [*, field]; simp [mul_left_comm Vc, by simpa using hX (.single γ 1), hS,
      apply_comp_perm_of_conj_invariant _ (_ :
      W).2 hd]; ac_rfl; simp [Φ, S, sum_mul, sum_inner, -Finsupp.lift_apply]; simp [-Finsupp.sum]
  have xe γ μ : ⟪L (X γ), L (X μ)⟫_ℂ = (alternant ε μ).1 γ := by
    simpa [hA μ, ↓mul_comm Vc, X, L, Vc, weyl_denominator hg.1, coeff_mul_apply_left, δ,
      zero_add δ ▸ ac (by tauto), ← @integral_conj_kTypeChar _ _ ε] using pair (he μ) γ 1
  have o : Orthonormal ℂ (L ∘ e) := by simp +contextual [orthonormal_iff_ite, e, xe, ac, z]
  have hd y x : _ = torusEval x D := (av ((card W : ℂ)⁻¹ • D) y x).trans (by
    simp [D, ↓map_sum, ↓← torusEval_comp_perm,
      torusEval_rootProd_noncompact_comp hg.neg.1 (_ : W).2]); generalize Φ _ = d at hd
  have hI : Integrable (d * ψ ·) := .mono' (.const_mul (integral_decay_le _ .monoidHom_id (c := 2 *
    N) (by omega) 1).1 (2 ^ (#(oppositePairs ε) * N * 2))) (by fun_prop) (.of_forall fun x ↦
    (norm_le_of_nonempty _).2 fun k ↦ by
    let u := (b k)⁻¹ * x; let g := u⁻¹ * diagTorus ε (v k) * u
    let φ := (MulSemiringAction.toAlgHom ℂ (Matrix n n ℂ) (toConjAct u.1⁻¹)).comp (diagonalAlgHom ℂ)
    have p s : ‖φ (∏ i ∈ s, ((v k · : n → ℂ) - (v k i).1 • 1))‖ ≤ (‖g.1.1‖ + ‖g.1.1‖) ^ #s := by
      induction s using cons_induction <;> simp [*, show φ _ = g by rfl, pow_succ',
        norm_mul_le_of_le, norm_sub_le_of_le, U.one_le_norm]
    erw [← bv k, norm_mul, hd]; simp [D, ψ, pow_mul,
      torusEval_rootProd_noncompact hg.neg.1, -norm_prod]
    grw [show _ * _ = g.1.1 by simp [g, u, mul_assoc], norm_dsCoeff_le_pow hg (c := #(oppositePairs
      ε) * N), (le_div_iff₀' (by simp)).2 (?_ : ‖principalMinor (φ _) (ε · = 1)‖ ≥
      (‖u.1.1‖ / 2) ^ 2 * ‖_‖), norm_principalMinor_le_pow, Fintype.card_subtype, p {i | ε i ≠ 1}]
    · simp [div_pow, field, oppositePairs, u, norm_mem_unitary_mul, Unitary.mem_iff, star,
        ← maxCompactU.coe_inv, conjTranspose_nonsing_inv]; ring; rfl
    · grw [sq_le_norm_det_blockDiagPart]; erw [norm_det_blockDiagPart 1, principalMinor_mul,
        principalMinor_mul, U.principalMinor_coe_inv] <;> simp [principalMinor_eq_det,
        oppositePairs, prod_product, ← diagonal_one, sub_ite, diagonal_apply,
        prod_eq_zero_iff] <;> clear * - <;> grind
    grw [card_le_univ]; simp [N, field]; nlinarith [one_le_cast_card n])
  let h := l.formalDegree • ∫ g, d * ψ g
  have hh y x : h (c y x) = h (c 1 x) := by
    simp [h, *, ← integral_mul_left_eq_self (ψ · (c y x)) y.1]
    simp [c, ψ, mul_assoc]
  choose hm m hm' _ _ using (by simpa using exists_kType_multiplicity <| hν ·); let t γ : ℂ :=
    s γ * m γ
  have ha γ : ⟪L (X γ), L h⟫_ℂ = D.1.sum fun β c ↦ c * t (-β + γ) := by
    simp [h, inner_smul_right_eq_smul, ← by simpa [pair hd] using
      (innerSL ℂ (L (X γ)) ∘L L).integral_comp_comm hI]; simp [X, L, t, ψ, ← hm',
      mul_left_comm (l.formalDegree : ℂ), integral_finsetSum, ((hm _).const_mul _).const_mul]
  have ⟨Z, hZ⟩ : ∃ Z, mapRingHom _ (castRingHom ℂ) Z = D := ⟨(∏ a, ∏ b ∈ _,
    (.single (Pi.single a 1) 1 - .single (Pi.single b 1) 1)) ^ N, by simp; rfl⟩
  let a := Finsupp.ofSupportFinite (⟪L <| e ·, L h⟫_ℂ) (((o.inner_products_summable (L h)
    ).tendsto_cofinite_zero.eventually_lt_const one_pos).subset fun i ↦ by
    simp [e, ha, ← hZ, t]; exact_mod_cast one_le_abs)
  let A := innerSLFlip ℂ (L (h - a.lift _ ℂ _ e)) ∘SL L
  have k i : A (e i) = 0 := by simpa [A] using! (o.inner_right_finsupp a i).symm.trans
                                 (inner_sum ..)
  have eq := toLp_injective _ (L.sub_mem_ker_iff.1 (inner_self_eq_zero.1 (sub_mem ((mem_of_closed'
    A.isClosed_ker).2 fun r q ↦ (denseRange_torusEval.exists_dist_lt (h.comp (c 1)) q).elim fun p
    o ↦ ⟨Φ (Vc * (card W : ℝ)⁻¹ • p), by clear * - k z hν; simp_all [Φ, X, e], (dist_lt_iff q).2 (by
    erw [← bv ·, av, hh, dist_comm]; simp_rw [map_sum, ← torusEval_comp_perm,
      AlgHom.map_smul_of_tower]; exact (convex_ball ..).sum_mem (by simp) (by simp) fun w _ ↦
      apply_comp_perm_of_conj_invariant _ w.2 hh ▸ mem_ball'.2 ((dist_lt_iff q).1 o _))⟩)
    (by simp [k]))))
  refine ⟨a.lift _ ℂ _ (alternant ε <| ·.1 + δ), by simp +contextual [IsWeylAntisymm,
    isWeylAntisymm_alternant _, mul_left_comm (a _)], fun x ↦ ?_, t, by simp [↓← ha,
    e, *], by simp [t, hg.isKDominant_lowestKType, *],
    fun γ ↦ .intro (ν γ + δ) ∘ by simp +contextual [t, ↓ac, *]⟩; trans torusEval x Vc * h (c 1 x)
  simp [e, *]; ac_rfl; simp [h, hI, hd]; simp [c, ψ, field]

open Complex ComplexOrder Filter

attribute [local simp] prod_eq_zero_iff Finsupp.sum IsHermInvolution.det_ne_zero
  IsAccretive.det_ne_zero integral_div mul_zpow
  zpow_add₀ _root_.zpow_mul zpow_sub₀ zpow_sum_of_ne_zero

variable {n : Type} [Fintype n] {ε : n → _} {l : HCParam ε} {h : ℕ}

/-- For l = 2λ and J = diag ε, the Haar integral of m_{−(λ−ρ)}(k*Jk) / m_{−(λ+ρ)}(k*Ak) over the
k in U(n) outside the set `openOrbit` ε l; m is `weightMinors`. -/
noncomputable def Orbital.offOrbitIntegral (l : HCParam ε) A := ∫ k in {k :
  USign 1 | k.1.1 ∈ openOrbit ε l}ᶜ, weightMinors (-l.compactForm.lowestKType)
  (k.1.1ᴴ * signMatrix ε * k) / weightMinors (-paramAddRho l) (k.1.1ᴴ * A * k)

/-- For λ of gap h some σ, |σ| = 1, has σ∫_G ψ_λ(g⁻¹xg)dg = cχ(x) − `Orbital.offOrbitIntegral`(Jx)
for all torus points x with Jx accretive; J = diag ε, χ = `HCParam.kTypeChar` of λ−ρ for U(n), c =
∫_{U(n)}|m_{λ−ρ}|². -/
lemma Orbital.orbital_eq_char_sub_offOrbitIntegral (hg : l.HasGap h) : ∃ σ, ‖σ‖ = 1 ∧
  ∀ x, let A := signMatrix ε * diagTorus ε x; A.IsAccretive → σ * ∫ g,
    l.dsCoeff (g⁻¹ * diagTorus ε x * g :) = l.compactForm.lowestKType.kTypeNormSq *
    l.compactForm.lowestKType.kTypeChar (diagTorusK x) - offOrbitIntegral l A :=
  have K := by simpa [lowestKType_neg hg.signs_one] using hg.signs_one.neg.isKDominant_lowestKType
  ⟨weightMinors (-l.compactForm.lowestKType - l.lowestKType)
    (signMatrix ε), by simp [signMatrix], by
  intro x A hA
  have ⟨i, O⟩ := integral_haar_eq_integral_openOrbit hg.1 ε (F := fun y ↦ weightMinors
    (-l.compactForm.lowestKType) (yᴴ * signMatrix ε * y) / weightMinors (-paramAddRho l) (yᴴ
    * A * y)) (fun y b hb ↦ by simp [← mul_assoc _ y.1, mul_assoc bᴴ, hb.2, hb.diag_ne_zero hg.1,
    lowestKType, twoRho, *, IsKDominant.weightMinors_oppBorel_mul (ε := 1) hg.1,
    IsKDominant.weightMinors_mul_borel (ε := 1) hg.1, hg.isKDominant_neg_paramAddRho, diagChar,
    field,
    show IsBorelMatrix (-l) bᴴ by simp_all [IsBorelMatrix, BlockTriangular], ↓← conj_mul']) ?_
  rw [← ((maxCompactU 1).subtype.measurePreserving (by fun_prop) (μ := haarK 1) (fun _ ↦ by
    simp [mem_maxCompactU]) (by simp)).hasLaw.integral_comp (integrable_of_compactSpace ?_).1] at O
  erw [← integral_const_mul, ContinuousMap.coe_mk, congrArg (integral _) (funext fun y :
    @maxCompactU n _ 1 ↦ (?_ : _ = l.compactForm.flenstedJensen (y⁻¹ * (signMatrix ε)⁻¹ * y)
    (y⁻¹ * A * y))), integral_div, integral_integral
    (integrable_of_compactSpace ?_), ← (((measurePreserving_mul_prod_inv ..).comp
    Measure.measurePreserving_swap).fubini (integrable_of_compactSpace ?_)).2]
  any_goals fun_prop (disch := simp (disch := simp [*]) [maxCompactU.coe_inv])
  convert! (integral_skew_product (map_mul_right_eq_self _ ·.1) (integrable_of_compactSpace (ν :=
    haarK ε) (f := (ofReal <| ‖weightMinors l.lowestKType ·‖ ^ 2 /
    l.lowestKType.kTypeNormSq)).mul_prod i)).2 with _ g
  rw [dsCoeff_eq_flenstedJensen hg (mem_blockDiagAlg_iff_commute.2 rfl), flenstedJensen,
    ← integral_div, ← integral_const_mul]; congr with k
  simp [↓mem_U.1 (g * k).2, U.inv_mat, ↓A, mul_assoc, signMatrix, field, mul_conj']
  simpa [mul_assoc, U.inv_mat, A] using hA.conjTranspose_mul_mul (k := g)
  have H a h :=
    (isHolOfWeight_weightMinors hg.1 a⁻¹ (fun _ ↦ K) h).integral_mul_conj_weightMinors hg.1
  simp_all [-ofReal_pow, integral_complex_ofReal, offOrbitIntegral, weightMinors_unitary_inv,
    kTypeNormSq, mul_assoc,
    ↓← maxCompactU.coe_inv, weightMinors_neg, mul_div_cancel₀, ← mul_div (ofReal _), ne_of_gt]
  rw [← dsCoeff_of_mem_maxCompactU hg.signs_one, dsCoeff_eq_flenstedJensen
    hg.signs_one] <;> congr 1 <;> simp [A, diagTorus, mul_assoc, mem_maxCompactU,
    maxCompactU.coe_inv]
  simpa [A, diagTorus, mul_assoc, maxCompactU.coe_inv] using hA.conjTranspose_mul_mul (k := y)⟩

attribute [local fun_prop] AnalyticAt.fun_zpow

/-- Let λ have gap h∈ℕ, Laurent polynomials P(x) = Q(x)·`Orbital.offOrbitIntegral`(Jx) at torus
points with Jx accretive, o_i < o_j whenever λ_j < λ_i. If k < ⟨o,λ+ρ+β⟩+h for all exponents β of Q,
then P has no exponent γ with ⟨o,γ⟩ ≤ k. -/
lemma Orbital.coeff_eq_zero_of_low_level (hg : l.HasGap h) {P Q} (hP : ∀ x,
    let A := signMatrix ε * diagTorus ε x; A.IsAccretive → torusEval x P =
      torusEval x Q * offOrbitIntegral l A) {o} (ho : ∀ i j, l j < l i → o i
  < o j) γ (hk : ∀ β, Q.1 β ≠ 0 → o ⬝ᵥ γ < o ⬝ᵥ paramAddRho l + o ⬝ᵥ β + h) : P.1 γ = 0 := by
  by_contra; have ⟨β, m, H⟩ := P.1.support.exists_min_image (o ⬝ᵥ ·) ⟨γ, by simpa⟩
  let S e (R : ℂ[_]) m z t := ∑ γ ∈ R.1.support, R.1 γ * weightMinors γ (signMatrix ε) *
    t ^ (o ⬝ᵥ γ - (o ⬝ᵥ β - m)) * z ^ (e ⬝ᵥ γ); have z : 0 < circleMap 0 1 0 := by simp [circleMap]
  refine absurd (_root_.linearIndependent_iff'.1 ((linearIndependent_monoidHom (Multiplicative
    _) ℂ).comp (fun γ ↦ ⟨⟨fun e ↦ 2⁻¹ ^ (e.toAdd ⬝ᵥ γ), by simp⟩, by simp⟩) fun a b h ↦
    funext fun i ↦ by simpa using congr(‖$h (.ofAdd (Pi.single i 1))‖)) _ _ (funext fun e : n → ℤ ↦
    (Finset.sum_apply ..).trans (?_ : S e P 0 _ 0 = 0)) β m) (by simp_all [signMatrix])
  have ⟨C, _⟩ := Finite.exists_le (2 * |e ·|); let L := o ⬝ᵥ paramAddRho l + h
  have ⟨r, _, hr⟩ := ((isOpen_openOrbit_and_lintegral_le hg.1 ε
    1).1.isClosed_compl.isCompact.eventually_forall_of_forall_eventually (P := fun r k ↦ ∃ i j, ε
    i ≠ ε j ∧ r * ‖weightMinors (-l.compactForm.lowestKType) (k.1.1ᴴ * signMatrix ε * k)‖ < ‖k.1 i
    j ^ 2‖ ^ h / 2 ^ (C * h - e ⬝ᵥ paramAddRho l)) fun k ↦ Not.imp_symm fun y ↦
    have c := mem_blockDiagAlg_iff_commute.1 (mem_blockDiagAlg (x := k).2 fun i j p ↦ y.imp_symm
      fun _ ↦ (ContinuousAt.eventually_lt ?_ ?_ (by simp; positivity)).mono fun _ h ↦ ⟨i, j, p, h⟩);
      ⟨⟨k, by simp [U, c.right_comm, by simpa [U] using
      k.2]⟩, 1, by simp [IsBorelMatrix]⟩).exists_gt (a := 0)
  refine norm_le_zero_iff.1 (((isClosed_le ?_ ?_ : IsClosed {t : ℝ | ‖S e P 0 _ t‖ ≤ ‖S e Q L 2⁻¹ t‖
    / r}).mem_of_tendsto summable_geometric_two.tendsto_atTop_zero ((eventually_gt_atTop C.toNat
    ).mono fun s u ↦ ?_)).trans_eq (by simp [S, _root_.zero_zpow_eq]; grind [Finset.sum_eq_zero]))
  rotate_left 2; let D (z : ℂ) := diagonal (z ^ (s • o + e) ·)
  have A {z} h := (PosDef.diagonal fun _ ↦ zpow_pos h _).isAccretive.setOf_mem_nhds (z := D z)
  have E := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (f := fun z ↦ S e P 0 z (z ^ s)) (g
    := (fun z ↦ S e Q L z (z ^ s) / z ^ (s * L)) * offOrbitIntegral l ∘ D) (fun _ z ↦ ?_) (fun _ z ↦
    .mul ?_ (((isAnalyticFamily_of_differentiable (.mono (A z) fun _ _ _ ↦
    ⟨?_, ?_⟩)).analyticAt_integral _).comp (((diagonalLinearMap n
    ℂ ℂ).toContinuousLinearMap.analyticAt _).comp (.pi ?_)))) (convex_Ioi _).isPreconnected z
    (((hasDerivAt_circleMap ..).tendsto_nhdsNE (by simp)).frequently (.mono (Eventually.frequently
    ((?_ : ContinuousWithinAt (D ∘ _) ..) (A z))) fun z _ ↦ ?_)) (one_half_pos (α := ℂ))
  any_goals fun_prop (disch := first | grind | simp [ne_zero_of_re_pos z.1, *])
  simp [D] at E; simp [E]; grw [offOrbitIntegral, norm_setIntegral_le_of_norm_le_const
    (C := 2 ^ (-s * L) / r) (by simp) fun k ↦ ?_ ∘ hr k, measureReal_le_one]
  simp [field]; rintro ⟨i, j, p, q⟩
  grw [le_div_iff₀', norm_div, mul_div, q, div_le_of_le_mul₀] <;> try positivity
  have := le_norm_weightMinors_twoPowDiagConj h k (-paramAddRho l) (-(s • o + e)) i j (s - C)
    (by simp [U.inv_mat]) (by simp [hg.paramAddRho_lt_iff]; intro a c k; grind
    [Int.mul_le_mul_of_nonneg_left (ho _ _ k) s.cast_nonneg])
    (by simp; grind [paramAddRho, by exact_mod_cast hg.3 i j p])
  simp [L, mul_pow, div_pow, field, dotProduct] at *; grind
  specialize hP fun i ↦ ⟨ε i * circleMap 0 1 z ^ (s • o + e) i, by simp [Submonoid.unitSphere]⟩
  simp_all [torusEval, signMatrix, diagTorus, ← mul_assoc, ← Int.cast_mul, S, D, dotProduct,
    mul_div, ← sum_div, lift_apply', div_mul_eq_mul_div, field]

end

attribute [-instance] FiniteField.instGrindPowIdentity IsOrderedRing.toIsStrictOrderedRing
  instIsCharPOfIsLeftCancelAddOfCharP

/-- Rearrangement inequality with a gain: for integer vectors o, b with o_i < o_j whenever b_j <
b_i, ⟨o,b⟩ + |b_i−b_{w(i)}| ≤ ⟨o,b∘w⟩ for every permutation w and index i. -/
lemma Orbital.dotProduct_add_gain_le_comp_perm {n} [Fintype n] (o b : n → ℤ) (ho : ∀ i j,
  b j < b i → o i < o j) (w : Perm n) i : o ⬝ᵥ b + |b i - b (w i)| ≤ o ⬝ᵥ b ∘ w := by
  have p s : (o + Pi.single i (cond s 1 (-1))) ⬝ᵥ b ≤ _ ⬝ᵥ b ∘ w :=
    Antivary.sum_mul_le_sum_mul_comp_perm fun x y z ↦ by grind [ho y x z, Pi.add_apply]
  simp_all; grind

/-- Harish-Chandra: for λ of gap 500n³+10n⁵ and signature (p,q), deg_λ =
∏_{λ_j<λ_i}(λ_i−λ_j)/∏_{i<n} i!; for x in the torus with distinct entries, (−1)^{pq}
Σ_{σ∈S_n} ∫_G e_λ(g⁻¹(x∘σ)g) dg = p!q!·conj χ(x), χ the character of U(n) of highest weight
λ−ρ.

Known result: Discrete series character on the compact Cartan by orbital integrals; formal
degree. -/
lemma Orbital.harish_chandra_degree_and_orbital {n : Type} [Fintype n] {ε} {l : HCParam ε} [Nonempty
  n] (hg : l.HasLargeGap (10 * Fintype.card n ^ 5)) : l.formalDegree = weylDimensionPoly l ∧ ∀ x,
  x.Injective → (-1) ^ #(oppositePairs ε) * ∑ σ : Perm n, ∫ g, l.dsKernel (g⁻¹ * diagTorus ε (x ∘ σ)
  * g) = #{σ : Perm n | ε ∘ σ = ε} * star (l.compactForm.lowestKType.kTypeChar (diagTorusK x)) := by
  let h := 500 * Fintype.card n ^ 3 + 10 * Fintype.card n ^ 5; have g : l.HasGap h := by lia
  let o := (-l).compactForm.lowerCount Eq; let κ := paramAddRho l + o
  have hκ a : l a + Fintype.card n - 1 = 2 * κ a := by
    simp [κ, o, lowerCount]; grind [two_mul_paramAddRho, twoRho, card_lt_add_card_gt_add_one g.1 a]
  have k s : (toHCParam s l).lowestKType + (toHCParam s l).lowerCount Eq =
    κ - (-toHCParam s l).lowerCount Ne := by simp [κ, o, lowestKType, twoRho, lowerCount,
    filter_and, filter_not, sdiff_inter_right_comm, funext_iff]; grind
  have vt : l.rootProd Eq * l.rootProd Ne =
    l.compactForm.rootProd Eq := by simp [rootProd, prod_filter, ← prod_mul_distrib]; grind
  obtain ⟨W, G, ⟨P, aP, eP, ht⟩, σ, s1, lk⟩ := by simpa [↓k, lowerCount, Pi.sub_def] using
    (weyl_character_kTypeChar g.signs_one.1
    g.signs_one.isKDominant_lowestKType).2, by exact_mod_cast g.3, exists_laurent_orbital_integral l
    hg, orbital_eq_char_sub_offOrbitIntegral g; set N := 4 * Fintype.card n ^ 2
  set D := (-l).rootProd Ne; let δ := (-l).lowerCount Ne; let s : ℂ := (-1) ^ #(oppositePairs ε)
  have e : D = s • l.rootProd Ne := eq_of_torusEval_eq fun x ↦ by
    simp [D, s, torusEval_rootProd_noncompact, g.1, g.neg.1, ← mul_assoc,
      ← prod_neg]; left; congr! 1; grind [HasGap, oppositePairs]
  let c := l.formalDegree * l.compactForm.lowestKType.kTypeNormSq * s / σ; let E ε :=
    D ^ N * alternant ε κ; let b := κ + N • δ
  have nn r [DecidableRel r] x γ (c : (l.compactForm.rootProd r * D ^ N).1 γ ≠ 0) :
      o ⬝ᵥ (x + (-l).compactForm.lowerCount r + N • δ) < o ⬝ᵥ x + o ⬝ᵥ γ + h := by
    simp [add_assoc, ↓dotProduct_add, dotProduct, δ, o,
      lowerCount]; grw [← ((mul_mem (rootProd_mem_leadingMonomials l.compactForm r l) (pow_mem
      (rootProd_mem_leadingMonomials l Ne l) N)).2 γ (by simpa [e, smul_pow, s] using c)).1 _]
    (repeat grw [card_le_univ]); simp [N, h]; rw [← sub_pos]; ring_nf; positivity
  have m i j (p : l j < l i) : o i < o j ∧ b j < b i :=
    ⟨by grind [two_mul_paramAddRho g, Pi.add_apply], by
    simp [b, δ, lowerCount]; by_cases N * Fintype.card n < κ i - κ j; grw [card_le_univ]; lia
    apply add_lt_add_of_lt_of_le <;> (try gcongr 3) <;> grind⟩
  -- levels of `D ^ k` times a function supported in the Weyl translates of the cone
  have lev {k a} P : IsConeSeriesMultiple l a (D ^ k) P → a + k • δ = b → P.1 b = 1 ∧ ∀ γ,
    P.1 γ ≠ 0 → ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w ≤ o ⬝ᵥ b := fun ⟨t, hf, ht⟩ d ↦ by
    simp [hf]; clear * - m g ht d
    have := by simpa [leadingMonomials] using pow_mem (rootProd_mem_leadingMonomials (-l) Ne o) k
    have e γ β (c : (D ^ k).1 β * t (-β + γ) ≠ 0) : ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w +
        ite (β ∘ w = k • δ) 0 1 ≤ o ⬝ᵥ b := (ht.2 _ (right_ne_zero_of_mul c)).elim fun μ ⟨j, p⟩ ↦ by
      obtain ⟨w, q, rfl⟩ := by simpa [comp_symm_eq] using inv_surjective.exists.1 (
        exists_ne_zero_of_sum_ne_zero (j ∘ (alternant_apply _).trans))
      simp [rootCone, Pi.add_comp, Pi.neg_comp, ← d] at *
      grind [(@torusEval_comp_eq_mul_iff _ _ (D ^ k) w 1).1 (by simp [D,
        torusEval_rootProd_noncompact_comp g.neg.1, ← q])]
    refine ⟨(Finset.sum_eq_single (k • δ) (fun _ _ n ↦ by_contra (e _ _ · |>.elim fun w _ ↦ ?_))
      (by grind)).trans (by grind), by grind [exists_ne_zero_of_sum_ne_zero, Finsupp.sum]⟩
    simp [imp_iff_not_or] at m; simp_all [show ⇑w = id by ext i; grind [m i (w i), m (w i) i,
      HasGap, dotProduct_add_gain_le_comp_perm o b (fun i j ↦ by grind [m j i, HasGap]) w i]]
  obtain ⟨⟨p1, p2⟩, q1, q2⟩ := lev _ ht (by grind), lev (E ε) ⟨_,
    AddMonoidAlgebra.coeff_mul_apply_left _ _, by
    rw [alternant_apply, Fintype.sum_eq_single 1] <;> simp [funext_iff, Perm.ext_iff]
    grind [HasGap], by simp [rootCone]; grind⟩ rfl
  suffices R : P = c • E ε by
    simp [*] at p1
    refine ⟨by simpa [c, s, abs_of_pos, formalDegree_pos hg, s1,
      ← weyl_dimension_formula g.signs_one, field, ne_of_gt] using congr(‖$p1‖), fun x u ↦
      star_injective (mul_left_cancel₀ (torusEval_rootProd_ne_zero l.compactForm Eq u) ?_)⟩
    have a τ := congr(Perm.sign τ * torusEval (x ∘ τ) $R)
    have := @torusEval_rootProd_ne_zero
    simp [↓eP, *, E, pow_succ', ← mul_assoc, ← Int.cast_mul, mul_comm s, field,
      s, weyl_denominator g.signs_one.1 ▸ (torusEval_comp_eq_mul_iff
      _).2 (isWeylAntisymm_alternant _ rfl)] at a
    simp [dsKernel, integral_conj, mul_sum, ← mul_assoc, *, mul_left_comm _ (#_ : ℂ)]
    simp [alternant, torusEval, mul_sum, ← sum_filter, mul_left_comm, sum_comm,
      ← by simpa [det_apply', mul_sum] using (fun w ↦
      (det_transpose _).trans (det_permute' w⁻¹ (Matrix.of fun a b ↦ (x a).1 ^ κ (w b))))]
  ext γ; by_contra z; have ⟨w, hw, u⟩ := by_cases (fun _ ↦ q2 γ <| by simp_all) (p2 γ)
  have y : (E 1).1 (γ ∘ w) = w.sign * (E ε).1 γ := .trans ?_ ((torusEval_comp_eq_mul_iff w).1
    (by simp [E, *, torusEval_rootProd_noncompact_comp g.1, (torusEval_comp_eq_mul_iff w).2,
    isWeylAntisymm_alternant w, field]) _)
  apply z; simpa [aP w, *, field] using coeff_eq_zero_of_low_level g (P :=
    P - c • E 1) (Q := -(l.formalDegree * s / σ) • _) (by
    simp_all [E]; grind [norm_zero]) (m · · · |>.1) _ (u.trans_lt ∘ nn _ _ · ∘ right_ne_zero_of_mul)
  simp [E, AddMonoidAlgebra.coeff_mul_apply_left, alternant_apply, Finsupp.sum]; congr! with β B v
  specialize nn Ne κ β; simp [rootProd, lowerCount.eq_unfold] at nn ⊢; intro; funext i
  grind [dotProduct_add_gain_le_comp_perm o κ (by grind [Pi.add_apply]) v i, dotProduct_add,
    dotProduct_neg]
