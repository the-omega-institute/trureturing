import GRH.Lib.CM.LocalHeight.IntegralParameter
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Supporting lemmas (textbook or folklore).

Part of: Local heights and Tate's trick; integrality of CM theta functions and torsion translates
(known result; see Lib.CM.LocalHeight.IntegralParameter).

Part of: Main theorem of complex multiplication for elliptic curves, soft form (known result; see
Lib.CM.FormalGroup.FormalHeight).

This file: Transport of sections and points to a Galois conjugate curve. Sections bounded by the
local height are integral in the formal parameter. Roots-of-unity filter on power series; iterating
an Artin-Schreier relation. Torsion translates and isogeny pull-backs of the CM theta function are
integral series. -/

open CMLattice ComplexConjugate Finset IsAIC IsLocalRing MvPolynomial NormedField PeriodPair
  PowerSeries Submodule Valued.integer

variable {d d'} {C : CMLattice d} (σ : ℂ ≃+* ℂ) {C' : CMLattice d'}

/-- The power series θ′/σθ: the Taylor series of the theta function of C' times the inverse of
the σ-conjugate of that of C. -/
noncomputable def thetaQuotient (C : CMLattice d) (σ : ℂ ≃+* ℂ) (C' : CMLattice d') :=
  taylorAtZero C'.θ * (taylorVia σ C.θ)⁻¹

lemma taylorAtZero_monomialSection (h : C'.a₁ = σ C.a₁) x : taylorAtZero (C'.monomialSection x) =
  thetaQuotient C σ C' ^ monomialDeg x * taylorVia σ (C.monomialSection x) := by
  have A i a : a * taylorVia σ (cond i translatedWp translatedWpDeriv C) = a * taylorVia (.id _)
    (cond i translatedWp translatedWpDeriv C') := by ext n; revert i a; induction n <;> simp_all
    [translatedWp, sq, mul_add, mul_sub, mul_comm (taylorVia _ _),
    ← mul_assoc, mul_right_comm, ← div_eq_of_eq_mul (mod_cast _) (@coeff_derivative ℂ ..)]
  simp (disch := fun_prop) [taylorVia, taylorAtZero_congr _ (monomialSection_eq _ _), by simpa using
    (A · 1)]
  simp [thetaQuotient, ← mul_assoc, ← mul_pow, mul_assoc (taylorAtZero _)]

/-- Let a₁(C') = σ(a₁(C)), σ an automorphism of ℂ. Each z has y and μ ≠ 0, with y = t if θ′(z) =
0, such that every degree-m section f of C has a degree-m section g of C' with Taylor series
(θ′/σθ)^m·σf and g(z) = μ^m σ(f(y)). -/
lemma exists_conjugate_section (h : C'.a₁ = σ C.a₁) z : ∃ y, ∃ μ ≠ 0, (C'.θ z = 0 → y = C.t) ∧ ∀ {m
  f}, f ∈ C.sections m → ∃ g ∈ C'.sections m, taylorAtZero g = thetaQuotient C σ C' ^ m * taylorVia
  σ f ∧ g z = μ ^ m * σ (f y) := by refine Exists₂.imp (fun y μ ↦
  .imp_right (.imp_right fun (_ : (C'.θ z, C'.σ z ^ 2, C'.phiThetaCube z) = (μ * σ (C.θ y),
  μ ^ 2 * σ (C.σ y ^ 2), μ ^ 3 * σ (C.phiThetaCube y))) m f k ↦ @And.right (Differentiable ℂ f) _
  (closure_induction ⟨?_, 0, ?_⟩ (fun _ _ _ _ ⟨_, _, p@⟨_, _⟩, _⟩ ⟨_, _, q@⟨_, _⟩, _⟩ ↦
  ⟨?_, _, add_mem p q, ?_⟩) (fun | c, _, ⟨x, k, rfl⟩ => k.2 ▸ ⟨?_, _, smul_mem _ (σ c)
  (monomialSection_mem ..), ?_, by simp_all [monomialSection, ← k.2]; ring⟩)
  (C.sections_le_span_monomialSection _ k)))) (if k : z + C'.t ∈ C'.Λ then ⟨C.t, C'.phiThetaCube z /
  σ (C.phiThetaCube C.t) / (C'.σ z / σ (C.σ C.t)) ^ 2, by grind [two_t_mem, phiThetaCube_sq_add,
  t_notMem, (sub_mem k).mt, congr(σ $(C.phiThetaCube_sq_add C.t)), θ_eq_zero_iff, sigma_eq_zero_iff,
  map_ne_zero]⟩ else (C.exists_weierstrassP_eq_of_cubic (σ.symm (C'.translatedWp z) + ℘[C.1] C.t)
  (σ.symm (℘'[C'.1] (z + C'.t))) (by grind [CMLattice, g₂_eq, g₃_eq, by
  simpa [translatedWpDeriv, h, map_ofNat] using congr(σ.symm $(C'.weierstrass_equation k))])).elim
  fun w _ ↦ ⟨w - C.t, C'.θ z / σ (C.θ _), by simp_all [phiThetaCube_spec, translatedWpDeriv,
  translatedWp, field, map_ofNat]⟩) <;> simp (disch := fun_prop) [↓zero_mem, Pi.zero_def,
  Pi.add_def, Pi.smul_def, taylorVia, taylorAtZero_monomialSection σ h] <;> grind

variable [PrimeSevenModEight d] (C :
  CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p] [Fact d'.Prime]

section

attribute [local simp] Algebra.smul_def Polynomial.aeval_eq_sum_range Polynomial.hom_eval₂ map_ofNat

/-- For a valuation v on an algebraically closed field K and finitely many multivariate
polynomials f_i over K, there is a point y with coordinates in the valuation ring such that
v(c) ≤ v(f_i(y)) (v multiplicative) for every i and every coefficient c of f_i. -/
lemma exists_val_coeff_le_val_eval {K σ n} [Field K] [IsAlgClosed K] (v : Valuation K NNReal) (f :
  Fin n → _) : ∃ y : σ → v.valuationSubring, ∀ i m, v ((f i).coeff m) ≤ v
  (eval (algebraMap .. ∘ y) (f i)) := by
  choose c g hg h using (f · |> fun f ↦ show ∃ c g,
    MvPolynomial.map (residue v.valuationSubring) g ≠ 0 ∧ f = c • g.map (algebraMap ..) by
    choose! k w _ using Set.exists_upper_bound_image f.support
      (v.valuationSubring.valuation ∘ f.coeff) (by simp)
    use f.coeff k, MvPolynomial.monomial k 1 + ∑ n ∈ f.support \ {k}, MvPolynomial.monomial n (w n)
    simp_all [coeff_sum, MvPolynomial.ext_iff]; use ⟨k, by simp⟩, by grind)
  have := ((of_isIntegrallyClosedIn K).of_surjective
    (@residue_surjective v.valuationSubring _ _)).isAlgClosed
  peel residue_surjective.comp_left.exists.1 (not_forall.1 (finprod_ne_zero hg ∘ funext))
  intros; simp_all [← eval₂_comp, prod_eq_zero_iff, finprod_eq_prod_of_fintype]
  gcongr; use (Valuation.integer.integers _).le_of_dvd (this _).dvd

/-- Integrality principle: if f is a section of degree m with |ιf(z)| ≤ ht(z)^m for all z, its
series over ℂ_p is θ^m·u, u ∈ 𝔬[[φ]]. For even f, u = (ιP)(ξ) with ιP an integral
polynomial, and f(t) = P_{m/2}σ(t)^m if m is even. -/
lemma CMLattice.exists_eq_theta_pow_mul_of_norm_le {f m} (hf : f ∈ C.sections m) (hi :
  ∀ z, ‖ιₚ (f z)‖ ≤ C.naiveHeight z ^ m) : ∃ u ∈ C.phiSeriesRing, taylorVia ιₚ f =
  taylorVia ιₚ C.θ ^ m * u ∧ (f.Even → ∃ P : Polynomial ℂ, (∀ i, ‖ιₚ (P.coeff i)‖ ≤ 1) ∧ u = (P.map
  ιₚ).aeval (taylorVia ιₚ C.translatedWp) ∧ (Even m → f C.t = P.coeff (m / 2) * C.σ C.t ^ m)) := by
  have ⟨R, h, j⟩ : ∃ R : ℕ → Polynomial ℂ, (∀ z, C.θ z ≠ 0 → f z =
    C.θ z ^ m * (R 0 + C.translatedWpDeriv z • R 1).eval (C.translatedWp z)) ∧ (Even m → f C.t =
    (R 0).coeff (m / 2) * C.σ C.t ^ m) := C.sections_le_span_monomialSection m hf |>
    closure_induction ⟨0, by simp⟩ (fun _ _ _ _ ⟨R, _⟩ ↦ .imp' (R + ·) (by simp_all; grind)) (by
    rintro c _ ⟨⟨j, k, e⟩, _, ⟨⟩⟩; use Pi.single e (c • .X ^ k); cases e <;> simp_all
    [monomialSection_eq] <;> simp [monomialSection, C.θ_eq_zero_iff.2, two_t_mem,
      zero_pow_eq] <;> grind [pow_mul])
  let F := ![R 0, R 1, Cubic.toPoly ⟨4, C.a₁ ^ 2, 4, 0⟩]
  obtain ⟨x, hx, H⟩ := by simpa [↓coeff_uniqueAlgEquiv_symm, eval, ← NNReal.coe_le_coe,
    Fin.exists_fin_succ_pi] using (exists_val_coeff_le_val_eval (valuation.comap ιₚ)
    ((uniqueAlgEquiv ℂ (Fin 1)).symm <| F ·)).imp fun _ ↦ (· · <| .single 0 ·)
  obtain ⟨⟨y, hy⟩, l, e⟩ := ((F 2).eval x).isSquare, Subtype.range_coe.ge C.two_t_mem
  obtain ⟨z⟩ : ∃ z, z + C.t ∉ C.Λ ∧ x = C.translatedWp z ∧ C.translatedWp (-z) = x ∧
    C.translatedWpDeriv (-z) = C.translatedWpDeriv z + -y := (C.exists_weierstrassP_eq_of_cubic
    (x + C.weierstrassP C.t) y (by simp_all [F, Cubic.toPoly]; grind [g₃_eq,
    CMLattice])).imp' (-C.t + ·) (by simp [translatedWpDeriv, translatedWp, add_assoc, ← e]; grind)
  have hd h := have k := (H 2 · |>.trans_lt h)
    (norm_lt_one_of_eq_mul_add_mul (k 2).le (intCast_mem (valRingCp p) (-16)) (by simp [F]; ring)
      (k 2) (k 1)).ne (norm_disc_eq_one ..)
  simp [↓hy, eq_div_of_mul_eq _ (phiThetaCube_spec ..).1.symm, field, sq_le_sq, *] at hx hd
  obtain ⟨k, k', l⟩ := hi z, hi (-z), C.naiveHeight_spec z, one_pos.trans_le hd, h (-z), H 1
  simp [phiThetaCube_spec, add_mul, ← mem_iff, *] at k k' l H h
  obtain ⟨q, A⟩ := by simpa [mem_iff] using sub_mem k k', fun i h ↦ sum_mem (t :=
    range (F i).natDegree.succ) fun n _ ↦ C.isSeriesGenerator_translatedWpDeriv.smul_mem
    ((H i n).trans h) (pow_mem C.taylorVia_translatedWp_mem_phiSeriesRing n)
  grw [← hd, one_mul] at q; rw [add_mem_cancel_right (by bound)] at k
  exact ⟨_, add_mem (A 0 k) (mul_mem C.isSeriesGenerator_translatedWpDeriv.generator_mem
    (A 1 q)), by simp (disch := fun_prop) [C.taylorAtZero_congr
    h, F, taylorVia], fun e ↦ ⟨_, (H 0 · |>.trans k), by simp_all [e.eq, F], j⟩⟩

end

/-- The part of the power series f in the degrees congruent to r modulo m. -/
noncomputable def congruencePart m r (f : ℂ_[p]⟦X⟧) := PowerSeries.mk fun n ↦ ite (n ≡ r [MOD m])
    (f.coeff n) 0

lemma congruencePart_eq_sum {m} [M : NeZero m] {ζ : ℂ_[d']} (hζ : IsPrimitiveRoot ζ m) r f :
    congruencePart m r f = (m : ℂ_[d'])⁻¹ • ∑ i ∈ range m, (ζ ^ i)⁻¹ ^ r • rescale (ζ ^ i) f := by
  ext; simp [congruencePart, ← mul_assoc, ← sum_mul, ← inv_pow, pow_right_comm, ← mul_pow,
    ← hζ.eq_orderOf ▸ (hζ.isOfFinOrder M.1).pow_eq_pow_iff_modEq]
  split <;> simp [*, ↓geom_sum_eq, hζ.1, mul_pow, pow_right_comm, field, hζ.ne_zero M.1]

lemma eq_sum_pow_of_sub_pow_eq {R} [CommRing R] [CharP R d'] {x s : R} {e} (h : s - s ^ d' ^ e =
  x) B : s = ∑ l ∈ range B, x ^ d' ^ (e * l) + s ^ d' ^ (e * B) := by simp [← h, sub_pow_char_pow,
  ← pow_mul', ← pow_add, ← mul_add_one, sum_range_sub', -sum_sub_distrib]

/-- Let 0 ≠ δ ∈ 𝓞_K with δδ̄ = N and δy ∈ Λ. Then, read in ℂ_p, the series (U_yθ)(δ̄z) lies in
θ^N·𝔬[[φ]].

Known result: Local heights and Tate's trick; integrality of CM theta functions and torsion
translates. -/
lemma CMLattice.rescale_translate_eq_theta_pow_mul {δ y N} (h : C.IsIsogeny C.1 (conj δ) N) (h0 :
  δ ≠ 0) (hy : δ * y ∈ C.Λ) : ∃ u ∈ C.phiSeriesRing, (taylorVia ιₚ (C.twistedTranslate 1 y
  C.θ)).rescale (ιₚ (conj δ)) = taylorVia ιₚ C.θ ^ N * u := have := by simpa [ne_of_gt] using h.2
  (C.exists_eq_theta_pow_mul_of_norm_le (C.twistedTranslate_comp_mem h h0 hy)
    (one_mul N ▸ C.norm_translate_le_naiveHeight_pow h y N (by aesop) (by grind [h.1 _ hy])
    (by simp))).imp (by simp_all [taylorVia, rescale_map])

/-- Let aΛ ⊂ Λ' for CM lattices of areas A, A', with aāA = NA', N a natural number. Then, read
in ℂ_p, φ'(az) lies in 𝔬[[φ]] and θ'(az) lies in θ^N·𝔬[[φ]]. -/
lemma CMLattice.rescale_translatedWpDeriv_mem {C' a N} (h : C.IsIsogeny (@periodPair d C') a N) :
  (taylorVia ιₚ C'.translatedWpDeriv).rescale (ιₚ a) ∈ C.phiSeriesRing ∧
  ∃ v ∈ C.phiSeriesRing, (taylorVia ιₚ C'.θ).rescale (ιₚ a) = taylorVia ιₚ C.θ ^ N * v := by
  choose u A B _ using (C.exists_eq_theta_pow_mul_of_norm_le (C.comp_mul_mem_sections h
    (monomialSection_mem ..)) <| by simpa using
    C.norm_translate_le_naiveHeight_pow h 0 1 nofun (by simp) <| C'.norm_monomialSection_le ·)
  simp (disch := fun_prop) [C'.taylorAtZero_congr (monomialSection_eq _ _), taylorVia, pow_mul',
    ← rescale_map] at *
  obtain ⟨_, k⟩ := C.isSeriesGenerator_translatedWpDeriv.exists_mul_eq_one (A ..)
    (by simpa using congr(‖PowerSeries.constantCoeff $(B 1 0 0)‖).symm)
  grind [mul_mem (A 0 0 1) (pow_mem k.1 3), (taylorVia ιₚ C.θ ^ N).inv_mul_cancel (by simp)]

/-- If a complex number a satisfies aΛ ⊂ Λ' for the lattices of two CM data for d (a prime ≡ 7
mod 8), then a is p-adically integral: |ι(a)|_p ≤ 1. -/
lemma CMLattice.norm_le_one_of_isogeny {C' a} (h : ∀ x ∈ C.Λ, a * x ∈ @Λ d C') : ‖ιₚ a‖ ≤ 1 := by
  simpa using (C.isSeriesGenerator_translatedWpDeriv.norm_coeff_le_one
    (C.rescale_translatedWpDeriv_mem (exists_isIsogeny_of_mul_mem_lattice h).choose_spec).1).2
