import OmegaMath.NumberTheory.GRH.Lib.CM.Genus.QuadraticZeta
import OmegaMath.NumberTheory.GRH.Lib.CM.MainTheorem.ConjugateCurve
import OmegaMath.NumberTheory.GRH.Lib.CM.KroneckerLimit.LogTheta
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Height of the formal group of a CM curve. Only upper bounds are given here, over
the integers of the p-adic complex numbers. An endomorphism of odd degree q has a unit coefficient
in degree at most q, and a vanishing Hasse invariant forces a non-split prime. Source: M. Deuring,
Die Typen der Multiplikatorenringe elliptischer Funktionenkörper (1941); J. Silverman, The
Arithmetic of Elliptic Curves, IV.7; for the Lubin-Tate form, V. Drinfeld, Elliptic modules (1974),
1.7.

Known result: the Chowla-Selberg formula in logarithmic form. It is stated here for prime
discriminant with 2 split, and the area is left in terms of the logarithmic derivative of the
L-function at 1, with no Gamma values. One unit makes the area the same for all conjugate curves.
Source: S. Chowla, A. Selberg, On Epstein's zeta-function, J. reine angew. Math. 227 (1967) 86-110;
B. Gross, On the periods of abelian varieties, arXiv 2005.04194.

Known result: the main theorem of complex multiplication for elliptic curves, in a soft form. The
statement here is only that multipliers with a cluster point in the finite adeles describe the
Galois action on torsion translates of the theta function. The adele is not identified with the
Artin map. Source: G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions
(1971), Thm 5.4; J. Milne, Complex Multiplication (2020), 9.17.

This file: Chowla-Selberg area formula for conjugates; soft CM main theorem; sums over ideal
classes. Vanishing Hasse invariant forces a non-split prime and a large coefficient. Endomorphism of
odd degree q has a unit coefficient in degree at most q. -/
seal Finset.univ Finset.sum Finset.prod

open Nat Complex Finset FractionalIdeal IsAlgClosed IsLocalRing QuadField NumberField PowerSeries
  Prod Real

/-- Complex multiplication for theta functions. Let Λ_C = Ω₀𝒪_K and C^σ = `CMLattice.galConjugate`.
There are Ω ≠ 0 with area(C^σ) = |Ω|²√d/2 and a positive integer multiple in Λ_{C^σ}, and a_S ∈ K
for finite S ⊂ K, clustering at a finite adele as S grows, with σ(U_{xΩ₀}θ_C) =
U_{xΩa_S}θ_{C^σ} as Taylor series for x ∈ S.

Known result: Main theorem of complex multiplication for elliptic curves, soft form. -/
lemma CMLattice.complex_multiplication_theta {d} [PrimeSevenModEight d] (C :
  CMLattice d) σ {Ω₀} (h₀ : C.latticeModule = scaledIdeal d (Ω₀, 1)) : let D := C.galConjugate σ
  ∃ Ω : ℂˣ, D.area = ‖Ω.1‖ ^ 2 * √d / 2 ∧ ∃ e : ℕ+, Ω.1 * e ∈ D.latticeModule ∧ ∃ β a,
    MapClusterPt β .atTop (algebraMap (QuadField d) (𝔸f (QuadField d)) ∘ a) ∧ ∀ S :
    Finset (QuadField d), ∀ x ∈ S, taylorVia σ (C.twistedTranslate 1 (x * Ω₀) C.θ) =
    taylorAtZero (D.twistedTranslate 1 (x * Ω * a S) D.θ) := by
  obtain ⟨⟨v, 𝔞⟩, h⟩ := (C.galConjugate σ).exists_latticeModule_eq_scaledIdeal
  cases' classGroup_sq_bijective.2.comp ClassGroup.mk0_surjective (.mk _ 𝔞) with 𝔠
  obtain ⟨p, u, e⟩ := Ideal.absNorm_pos_of_nonZeroDivisors 𝔠, by
    simpa [← h, ↓← map_mul] using @exists_eq_scaledIdeal_mul_of_mk_eq_one d (mk0 _ 𝔠 ^ 2 / 𝔞)
      (by aesop) (scaledIdeal d (v, 𝔞))
  have E := by simpa [↓mem_scaledIdeal, ← coeIdeal_pow] using (congr(· ∈ $e))
  choose a _ H using by simpa [E] using C.exists_taylorVia_twistedTranslate_theta (C.galConjugate σ)
                          σ (by grind [galConjugate]) Ω₀ (by simp [*, mem_scaledIdeal, quadInt])
  refine ⟨u * v * .mk0 𝔠.1.absNorm ?_, ?_, ⟨_, p⟩, (E _).2 ⟨_, Ideal.pow_mem_pow 𝔠.1.absNorm_mem 2,
    ?_⟩, ((isCompact_Ô.smul (𝔠.1.absNorm⁻¹ : QuadField d)).exists_mapClusterPt_of_frequently
    (.of_forall (⟨_, coe_mem_Ô <| a ·, (map_mul ..).symm⟩))).imp fun β b ↦ ⟨_, b.2, ?_⟩⟩ <;>
    simp [area_eq_of_eq_scaledIdeal e, field, coeIdeal_absNorm, mul_assoc, p.ne'] at H ⊢; exact H

/-- Splitting a sum over ideals by classes: let fractional ideals 𝔟_c represent each class once,
f(0) = 0, and ∑_{y ∈ 𝔟_c} f(|Ny|/N𝔟_c) = S_c. Then ∑ w·f(NI) over integral ideals I equals ∑
S_c, w the number of units (0 if infinite). -/
lemma hasSum_ideal_classes {K ι} [Field K] [NumberField K] [Fintype ι] {𝔟 : ι → _} (f : ℚ → ℝ)
    (h : ∀ C, ∃! c, ClassGroup.mk K (R := 𝓞 K) (𝔟 c) = C) (f0 : f 0 = 0) {S : ι → ℝ}
    (hS : ∀ c, HasSum (fun y : (𝔟 c).1.1 ↦ f (|Algebra.norm ℚ y.1| / absNorm (𝔟 c).1)) (S c)) :
    HasSum (Nat.card (𝓞 K)ˣ * f ·.absNorm : Ideal (𝓞 K) → ℝ) (∑ c, S c) := by
  choose Φ m using fun {c} {y : (𝔟 c).1} ↦ (le_one_iff_exists_coeIdeal.1
    (div_le_one_of_le₀ (spanSingleton_le_iff_mem.2 y.2) bot_le)).imp fun J e {I} ↦
    coeIdeal_inj (J := I).symm.trans (e ▸ div_eq_iff_mul_eq (by simp))
  convert! hasSum_sum fun c _ ↦ (hS c).tsum_fiberwise (@Φ c) with I
  simp [← absNorm_span_singleton (𝓞 K), ← m.1 (_ : _ ⁻¹' {I}).2, coeIdeal_absNorm, ← sum_mul,
    ← cast_sum, or_iff_not_imp_right]; intro
  obtain ⟨c, ⟨⟨z, g⟩⟩⟩ := by simpa [← mul_eq_one_iff_eq_inv', ← map_mul,
    ClassGroup.mk_eq_one_iff, ↓isPrincipal_iff] using h (.mk K (.mk0 I (by aesop)))⁻¹
  erw [Fintype.sum_eq_single _ fun c e ↦ @card_of_isEmpty _ ⟨by simp [*]; tauto⟩,
    @Set.ext _ (_ ⁻¹' {I}) (.range (· • ⟨z, spanSingleton_le_iff_mem.1 (g ▸ mul_le_of_le_one_left'
    coeIdeal_le_one)⟩)) fun y ↦ m.trans (g.congr_left.trans (spanSingleton_eq_spanSingleton.trans
    (exists_congr (by simp [Subtype.ext_iff])))), card_range_of_injective
    ((smul_left_injective _ (by aesop)).comp (@Units.ext _ _))]

/-- Chowla–Selberg, mean area: some complex u, a unit for all p and ι, satisfies area(Λ^σ)·|σu|²
= π·exp(γ − Re L′/L(1, χ_K))·2π/√d for every σ ∈ Aut(ℂ/K), γ Euler's constant.

Known result: Chowla-Selberg formula in logarithmic form. -/
lemma CMLattice.chowla_selberg {d} [PrimeSevenModEight d] (C : CMLattice d) : ∃ u,
  (∀ p [Fact p.Prime] [PadicPlace p], ‖ιₚ u‖ = 1) ∧
  ∀ σ, (C.galConjugate σ).area * ‖σ u‖ ^ 2 = π * rexp (chowlaSelbergConst d) * (2 * π / √d) := by
  choose 𝔞 _ using
    ClassGroup.induction (R := 𝓞 (QuadField d)) (QuadField d) (P := (∃ a, .mk _ a = ·)) (⟨·, rfl⟩)
  choose D u q using fun c ↦ C.exists_latticeModule_eq_scaledIdeal_mul (𝔞 (c ^ 2) / 𝔞 c)
  obtain ⟨i, k⟩ := (@Units.inv_mul_le_iff _ _ _ _ <| (scaledIdeal d).toHomUnits ·),
    classNumber_pos (QuadField d)
  obtain ⟨r, h⟩ := fun {c} ↦ (i _).2 (q c).le, succ_mul_pos 11 k, NeZero.pos d
  refine (exists_pow_nat_eq (∏ c, u c ^ 12 * ((D c).a₁ ^ 4 - 64)) h).imp fun w _ ↦ ⟨fun p _ _ ↦
    ?_, fun σ ↦ (C.galConjugate σ).exists_latticeModule_eq_scaledIdeal.elim fun x
    e ↦ ?_⟩ <;> rw [← pow_left_inj₀ (by simp)
    (by bound) h.ne'] <;> simp [sq, mul_pow, ← norm_pow, ← map_pow, map_ofNat, *]
  have n {f} i (e := by simp [snd_prod, classGroup_sq_bijective.prod_comp]) : ‖ιₚ _‖ ≤ 1 :=
    prod_induction_nonempty f (∀ z ∈ scaledIdeal d ·,
    ιₚ z ∈ valRingCp p) (by simp_intro ..; induction ‹_› using
    Submodule.mul_induction_on' <;> aesop) (card_pos.1 k) i _ (mem_scaledIdeal.2 ⟨1, e, rfl⟩)
  simp [prod_pow, norm_disc_eq_one, by simpa [fst_prod] using (n fun c _ _ ↦ norm_le_one_of_isogeny
    _ ∘ Submodule.mul_le.1 (q c).ge _).antisymm (by simpa [-inv_mk, field] using (n fun c _ _ ↦
    norm_le_one_of_isogeny _ ∘ Submodule.mul_le.1 r _))]
  have G {C} : (galConjugate C σ).a₁ = σ C.a₁ := by grind [galConjugate]
  have A {C D x} : scaledIdeal d x * latticeModule C ≤ latticeModule D → scaledIdeal d (x.1.map σ,
    x.2) * (C.galConjugate σ).latticeModule ≤ (D.galConjugate σ).latticeModule := by
    simp [Submodule.mul_le, mem_scaledIdeal]
    use fun h _ y m b e ↦ by simpa [*, by simpa using σ.commutes] using! (conj_isogeny_mem_lattice σ
      G G (exists_isIsogeny_of_mul_mem_lattice (h _ y m b rfl)).choose_spec).1
  have R {c} := by simpa [e, ← map_mul] using (A (q c).ge).antisymm' ((i _).1 (A r :))
  choose F _ hF S using fun c ↦ kronecker_limit ((D c).galConjugate σ).1 (2 / √d) (by simpa)
  obtain ⟨b, a⟩ := (HasDerivWithinAt.fun_sum (u := univ) fun c _ ↦ hF c).ofReal_comp,
    ((differentiable_riemannZeta₁ _).hasDerivAt.mul ((analyticAt_entireL (@quadTwist 1 1 d _)
    1).differentiableAt.hasDerivAt.const_mul _)).comp_ofReal.hasDerivWithinAt
  have := tendsto_nhds_unique (a.continuousWithinAt.congr' ?e) b.continuousWithinAt
  have e2 := (uniqueDiffWithinAt_Ioi 1).eq a (b.congr_of_eventuallyEq ?e this)
  simp [-ofReal_sum, ← G, ← disc_eq, chowlaSelbergConst, logDeriv] at this e2 ⊢
  rw [← mul_div_mul_left, eq_sub_of_add_eq' e2]
  apply log_injOn_pos <;> simp [-ofReal_mul, classGroup_sq_bijective.sum_comp (Real.log <|
    𝔞 · |>.1.absNorm), ← mul_sum, ← sum_div, area_eq_of_eq_scaledIdeal e, ↓weierstrass_disc_ne_zero,
    classNumber, log_div, area_eq_of_eq_scaledIdeal R, log_prod,
    ne_of_gt, Real.log_mul, *, (absNorm_nonneg _).lt_iff_ne', prod_eq_zero_iff]
  positivity; field; swap; filter_upwards [Ioo_mem_nhdsGT one_lt_two] with s ⟨h, k⟩
  rw [← (hasSum_ideal_classes (_ * · ^ _) _ _ fun c ↦
    ((latticeEquiv R).hasSum_iff.2 (S c ..)).congr_fun
    fun y ↦ congr(_ * $_ ^ _)).tsum_eq, ofReal_tsum] <;> simp [*, tsum_mul_left, ofReal_cpow, field,
    by simpa using (hasSum_eulerProd 1 (by simp) h).tsum_eq.trans (@eulerProd_one_eq_zeta_mul d _ _
    h), abs_norm_eq_norm_sq, area_eq_of_eq_scaledIdeal R,
    latticeEquiv, sq, ← eq_div_iff_mul_eq', riemannZeta_eq_inv_sub_mul, ne_of_gt, one_pos.trans h]
  aesop

/-- If for every f in 𝔬[[φ]] ⊂ ℂ_p[[z]] the coefficient of z^{p−1} in f′ has absolute value
below 1, then the coefficient of z^{p−1} in ιξ has absolute value at least 1, and p does not
split in ℚ(√−d).

Known result: Height of the formal group of a CM curve. -/
lemma CMLattice.one_le_norm_coeff_translatedWp_nonsplit {d p} [PrimeSevenModEight d] [pp :
  Fact p.Prime] [PadicPlace p] (C : CMLattice d) (h : ∀ f ∈ C.phiSeriesRing, ‖coeff
  (p - 1) (d⁄dX f)‖ < 1) : 1 ≤ ‖coeff (p - 1) (taylorVia ιₚ C.translatedWp)‖ ∧ chiK d p ≠ 1 := by
  obtain ⟨⟨L, _, -, -, -, e, -, H⟩, s, j : p - 1 ≠ 0, ⟨u, _⟩ : X ^ 2 ∣ taylorVia ιₚ C.translatedWp,
    m, hm⟩ := C.exists_log_theta, sqrt_neg_mem_quadInt d, pp.1.pred_pos.ne', by simp [X_pow_dvd_iff,
    ↓forall_lt_succ_right, translatedWp], pp.1.odd_of_ne_two fun e ↦ (norm_lt_one_of_eq_mul_add_mul
    ((valRingCp p).pow_mem C.norm_a₁_le_one 3) (intCast_mem (valRingCp p) (-32))
    (by simp [e, coeff_one_mul, sq, translatedWp]; ring) (h _ (neg_mem
    C.isSeriesGenerator_translatedWpDeriv.generator_mem)) norm_p_lt_one).ne (norm_disc_eq_one ..)
  apply (iff_self_and.2 fun t k ↦ (h _ (H _ (subset_closure ⟨_, s, rfl⟩)).2.2).not_ge ?_).1
  by_contra!; set x := taylorVia ιₚ _
  have e (n : ℕ) : d⁄dX (x ^ n * d⁄dX x) + ((-(n + 1) * ιₚ C.a₁ ^ 2) • x ^ (n + 1) +
      (-4 * n - 2 : ℂ_[p]) • x ^ n) = .C ↑(4 * n + 6) * x ^ (n + 2) := by cases n <;> simp [x,
    two_mul, smul_eq_C_mul, map_ofNat] <;> grind [taylorVia_curve_eq]
  suffices ∀ n ≤ m, ‖(x ^ n).coeff (p - 1)‖ < 1 by simpa [*, mul_pow, ← pow_mul, coeff_X_pow_mul',
    (by simpa [*, add_neg_eq_zero, map_ofNat] using congr(coeff 0 $(e 0)))] using this m
  apply twoStepInduction <;> intros <;> try simp [j, this]
  grw [← one_mul ‖_‖, ((pp.1.coprime_iff_not_dvd.2 _).norm_natCast_eq_one ℂ_[p]).ge, ← norm_mul,
    ← coeff_C_mul, ← e, map_add, IsUltrametricDist.norm_add_le_max]
  apply_rules [max_lt, pow_mem, mul_mem, deriv_mem_phiSeriesRing,
    taylorVia_translatedWp_mem_phiSeriesRing, norm_a₁_le_one, norm_lt_one_of_eq_mul_add_mul (_ :
    _ ∈ valRingCp p) (_ : _ ∈ valRingCp p) rfl] <;> bound; rintro ⟨_ | _ | _⟩ <;> lia
  let y : valRingCp p := ⟨_, C.norm_le_one_of_isogeny (C.5 s)⟩
  grw [t, ← sub_eq_of_eq_add' e, ← one_mul ‖_‖, ← isUnit_integer_iff_norm_eq_one.1 (.of_map (residue
    _) (y * y * (-1 - y ^ (p - 1))) _)]; simp [coeff_derivative, coeff_C, ← norm_mul]; grind
  simp [← k ▸ legendreSym_eq_pow_of_sq_eq_neg (by omega) (x := residue _ y)
    congr(⟦⟨$(map_sqrt_neg_sq _), _⟩⟧), neg_one_eq_one_iff, ringChar.eq, hm.trans_ne, ne_zero_pow j]

attribute [local simp ↓] CMLattice.two_t_mem CMLattice.translatedWp Finset.Nat.antidiagonal_succ
  HasSubst.of_constantCoeff_zero' coeff_X_pow_mul' isUnit_iff_constantCoeff subst_add
  subst_comp_subst_apply subst_mul subst_pow _root_.pow_dvd_pow_iff pow_mul' taylorAtZero_mul

/-- Let Z = X + ⋯ with f(Z) integral for all f ∈ 𝔬[[φ]], let aΛ ⊂ Λ with aā = q odd, and let g
be integral without constant term, Z(g) = ι(a)Z. Then g has a unit coefficient in some
degree ≤ q.

Known result: Height of the formal group of a CM curve. -/
lemma CMLattice.exists_unit_coeff_degree_le {d} [PrimeSevenModEight d] (E :
  CMLattice d) {p} [Fact p.Prime] [PadicPlace p] {Z g : ℂ_[p]⟦X⟧} (Z0 : constantCoeff Z = 0) (Z1 :
  coeff 1 Z = 1) (hZ : ∀ {f}, f ∈ E.phiSeriesRing → f.subst Z ∈ seriesToCp.range)
  {a q} (m : E.IsIsogeny E.1 a q) (o : Odd q) (hg : g ∈ seriesToCp.range) (g0 : constantCoeff g = 0)
  (h : subst g Z = ιₚ a • Z) : ¬∀ n ≤ q, ‖coeff n g‖ ≠ 1 := fun H ↦ by
  have D f j (h : ‖coeff j (seriesToCp f)‖ = 1) : f.map (residue (valRingCp p)) ∣ X ^ j :=
    (ValuationRing.dvd_total ..).elim id fun ⟨u, e⟩ ↦ by
    have := congr(coeff j $e) ▸ (isUnit_integer_iff_norm_eq_one.2 h).map (residue _); aesop
  obtain ⟨⟨g, rfl⟩, ⟨x, hx⟩, ⟨u, hu, e⟩, k, _, -, hs, K⟩ := hg,
    hZ E.taylorVia_translatedWp_mem_phiSeriesRing,
    (E.rescale_translatedWpDeriv_mem m).2, (E.comp_mul_mem_sections m E.θ_mem).2 _ E.two_t_mem,
    E.exists_eq_theta_pow_mul_of_norm_le (E.comp_mul_mem_sections m (monomialSection_mem ..))
    (by simpa using!
    E.norm_translate_le_naiveHeight_pow m 0 1 nofun (by simp) (E.norm_monomialSection_le (0, 1, 0)))
  obtain ⟨g1 : HasSubst g, x0, Q, e', rfl, hQ⟩ := by simpa [constantCoeff] using g0,
    by simpa [Z0] using congr(($hx).constantCoeff), K fun _ ↦ by simp [monomialSection]
  obtain ⟨⟨R, e'⟩, v, hu⟩ := (@mem_range_seriesToCp p _ (Q.map ιₚ)).2 (by simpa), hZ hu
  have l : Q.coeff q ^ 2 = 1
  rcases k 0, k (-E.t), (thetaSpace.pow E.θ_mem q).2 _ E.two_t_mem 0
  simp_all [monomialSection, multiplier_eq_neg_sigmaSign, sigmaSign, add_mul, mul_add, self_eq_neg]
  simp_all [← two_mul, E.θ_eq_zero_iff.2, o.neg_pow]; grind [Complex.exp_ne_zero, pow_right_comm]
  simp (disch := first | fun_prop | simp) [E.taylorAtZero_congr (E.monomialSection_eq _), taylorVia,
    e, mul_pow, mul_assoc, IsUnit.ne_zero, ← subst_coe, ← rescale_map] at hs
  have := map_dvd (PowerSeries.map (residue _)) (⟨v ^ 2, PowerSeries.map_injective (valRingCp
    p).subtype (by simp) (by simpa [*, PowerSeries.map, map_subst, ↓g1, coe_substAlgHom,
    mul_comm] using! congr(subst Z $hs).symm)⟩ : substAlgHom g1 x ∣ subst x R)
  grw [PowerSeries.map, map_subst (by simpa), ← coe_substAlgHom (by simp [*]), PowerSeries.map, D R
    q, map_pow, substAlgHom_X, D x 2, ← (@X_pow_dvd_iff _ _ 2 x).2, map_pow, map_pow, substAlgHom_X,
    ← (@X_pow_dvd_iff _ _ q.succ (g.map _)).2] at this
  iterate 2 simp_all +arith [← pow_mul', coeff]
  simpa [↓forall_lt_succ_right, Z0, ← PowerSeries.map.eq_def] using! And.intro x0 congr(coeff 1 $hx)
  simpa [*, pow_succ, coeff_mul] using congr(‖coeff 2 (subst Z $(E.taylorVia_curve_eq ιₚ))‖).symm
  simpa [e'] using congr(√‖ιₚ $l‖)
