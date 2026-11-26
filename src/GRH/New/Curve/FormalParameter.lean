import GRH.Lib.General.Algebra.DepthBounds
import GRH.Lib.CM.FormalGroup.FormalHeight
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Normal form of theta series at non-split primes. For p inert or ramified in K, a rescaled
product of CM theta functions is integral wherever the couplings of Frobenius powers of a variable
with its partners vanish modulo the prime, and for inert p it is an integral series times one
exponential with unit couplings; this gives both bounds for jet valuations. Denominators of theta
for one CM curve at inert p, led by degree p+1, are known. Related work: Bannai–Kobayashi, Algebraic
theta functions and Eisenstein–Kronecker numbers (arXiv v1, Thm 4.1), 2006; Bannai–Kobayashi–Yasuda,
Radius of convergence of the p-adic sigma function, 2017; Katz, Divisibilities, congruences, and
Cartier duality, 1981.

This file: Jets of products of torsion translates of theta are integral after scaling. Valuations of
coefficients of log theta: only two degrees keep a denominator. Property: series integral on
substitutions killing the Frobenius couplings. Good formal parameter and three-term normal form of
log theta at non-split primes. -/

section

open PowerSeries Algebra ComplexConjugate Finset IsUltrametricDist Nat

attribute [local simp] Subring.smul_def add_mem mul_mem derivative_exp

/-- Let 0 ≠ δ ∈ 𝓞_K, δy_i ∈ Λ, and c_{i,x}/(δ̄d) integral under ι. Then the jet of ∏_i
(U_{y_i}θ)(∑_x c_{i,x}z_x) along any polynomial with coefficients in ι⁻¹𝔬, read in ℂ_p, lies
in 𝔬. -/
lemma CMLattice.jet_theta_prod_integral {d} [PrimeSevenModEight d] (C : CMLattice d) {p} [Fact
  p.Prime] [PadicPlace p] {I σ} [Fintype I] [Fintype σ] {c : I → σ → _} {δ} (k : ∀ i x, ‖(ιₚ (conj
  δ))⁻¹ * c i x / d‖ ≤ 1) (u : δ ∈ quadInt d) (h0 : δ ≠ 0) {y : I → ℂ} (w : ∀ i, δ * y i ∈ C.Λ) Q :
  jet _ (.map ιₚ (.map ((valRingCp p).comap ιₚ).subtype Q)) (∏ i, (taylorVia ιₚ (C.twistedTranslate
  1 (y i) C.θ)).subst (linearSeries (c i))) ∈ valRingCp p := have ⟨L, _, l⟩ := C.exists_log_theta
  have s i : HasSubst ((ιₚ (conj δ))⁻¹ • linearSeries (c i)) := by simp
  let S := adjoin (valRingCp p)
    {f.substAlgHom (s i) | (i) (f ∈ C.phiSeriesRing.carrier ∪ {d⁄dX L, expSubst (-L)})}
  have m {i f} hf : _ ∈ S := subset_adjoin ⟨i, f, hf, rfl⟩
  have h {F} : F ∈ S → F.constantCoeff ∈ valRingCp p ∧ ∀ x, F.pderiv x ∈ S := by
    apply adjoin_induction
    rintro _ ⟨i, f, hf, ⟨⟩⟩
    simp [coe_substAlgHom]
    refine .imp_right (fun (h : (d • d⁄dX f).substAlgHom (s i) ∈ S) x ↦ ?_) ?_
    simpa [subst, linearSeries, MvPowerSeries.pderiv_X, coe_substAlgHom,
      ← Nat.cast_smul_eq_nsmul ℂ_[p], ← smul_assoc] using! S.smul_mem h ⟨_, k ..⟩
    obtain g | ⟨⟨⟩⟩ := hf
    use (C.isSeriesGenerator_translatedWpDeriv.norm_coeff_le_one g).1, by simp [*,
      C.deriv_mem_phiSeriesRing g]
    use by simp [*, ← coeff_zero_eq_constantCoeff, coeff_derivative], m (.inl ?_)
    simpa [*, ↓← mul_assoc, ↓← sq, ↓map_sqrt_neg_sq, smul_eq_C_mul, add_mem_cancel_right,
      taylorVia_translatedWp_mem_phiSeriesRing] using
      C.isSeriesGenerator_translatedWpDeriv.smul_mem ((valRingCp p).mul_mem
      (C.norm_le_one_of_isogeny (C.5 (sqrt_neg_mem_quadInt _))) l.2.2.2.2.1) (one_mem _)
    repeat simp_all [algebraMap_eq_smul_one, S, derivative_subst]
  (by apply Q.induction_on <;> simp_all [jet_mul_X, ← MvPolynomial.monomial_zero'] : ∀ F ∈ S, jet _
  _ F ∈ _) _ (prod_mem fun i ↦ (C.rescale_translate_eq_theta_pow_mul
    (exists_isIsogeny_of_mul_mem_lattice (C.5 (conj_mem_quadInt u))).choose_spec h0 (w i)).elim
  fun _ ⟨_, e⟩ ↦ by simpa [coe_substAlgHom, h0] using congr(substAlgHom (s i) $e ∈ S).ge (by aesop))

variable {p e Q} [h : Fact (Prime p)]

lemma exists_norm_eq_inv_pow_bounds x t ε J k (hQ : p ^ e = Q + 1) (H : e ≠ 0 ∧ ε ≤ 1 ∧ x + 1 + Q *
  J = p * t + ε + Q * k := by omega) : ∃ a, ‖(x + 1 : ℂ_[p])‖ = (↑p)⁻¹ ^ a ∧ (1 < a → p < x + 1) ∧
  (a = 0 ∨ k ≡ ε + J [MOD p]) ∧ ∀ n ≤ p, n * (a - e) ≤ k + t := by
  obtain ⟨h1, h2, v, _⟩ := h.1.one_lt, le_of_dvd x.succ_pos pow_padicValNat_dvd, dvd_pow_self p H.1
  exact ⟨_, by grind [norm_natCast_eq_inv_pow_padicValNat], h2.trans_lt' ∘ lt_self_pow₀ h1,
    (em' _).imp padicValNat.eq_zero_of_not_dvd fun ⟨u, _⟩ ↦ modEq_of_dvd ⟨u - t + v * (J - k), by
    zify at *; grind⟩, fun n hn ↦ (le_total _ e).elim (tsub_eq_zero_of_le · ▸ bot_le) (by
    grw [hn, mul_le_pow h1.ne']; nlinarith [le_self_pow H.1 p, p.pow_sub_mul_pow ·])⟩

/-- Let p ≥ 13, q = p^e = Q + 1, e ∈ {1, 2}, |ϖ^Q|² = p^{−e}, m′ = nZ′ with n′, Z′ integral,
n(0) = 0, m = O(X³), Z (beyond its constant) in degrees ≡ 1 mod Q, Z_q = −ϖ^{−Q}. Then μ =
pϖ^{−p−1}·m̃(ϖX), m̃ the part of m in degrees ≡ p + 1 mod Q, is b₁X^{p+1} + b₂X^{p+q} modulo
ϖ^Q, b₁, b₂ integral. -/
lemma norm_coeff_le_of_deriv (hp : 13 ≤ p) (he : e = 1 ∨ e = 2) (hQ : p ^ e = Q + 1)
    {ϖ : ℂ_[p]} (hπ : ‖ϖ ^ Q‖ ^ 2 = (↑p)⁻¹ ^ e) (ϖ0 : ϖ ≠ 0) {m n Z μ} (hn : d⁄dX n ∈
    seriesToCp.range) (hw : d⁄dX Z ∈ seriesToCp.range) (hn0 : coeff 0 n = 0) (R : ∀ j, ¬Q ∣ j →
  coeff (j + 1) Z = 0) (nc : coeff (Q + 1) Z = -(ϖ ^ Q)⁻¹) (m0 : ∀ k ≤ 2, coeff k m = 0) (hm : d⁄dX
  m = n * d⁄dX Z) (hμ : μ = (ϖ ^ (p + 1) / p)⁻¹ • rescale ϖ (congruencePart Q (p + 1) m)) :
  ‖coeff (p + 1) μ‖ ≤ 1 ∧ ‖coeff (p + p ^ e) μ‖ ≤ 1 ∧ (ϖ ^ Q)⁻¹ • (μ - coeff (p + 1) μ •
  X ^ (p + 1) - coeff (p + p ^ e) μ • X ^ (p + p ^ e)) ∈ seriesToCp.range := by
  set P := ϖ ^ Q; simp [↓mem_range_seriesToCp, congruencePart] at *; have :=
    hQ ▸ le_self_pow (by omega) p
  have {k} : ‖μ.coeff k‖ ≤ ite (k ∈ [p + 1, p + p ^ e]) 1 ‖P‖ := by
    by_cases g : k ≡ p + 1 [MOD Q]; by_cases! 2 < k
    obtain ⟨I, rfl⟩ := (modEq_iff_exists_eq_add (g.symm.le_of_lt_add (by omega))).1 g.symm
    obtain ⟨a, na, A⟩ := exists_norm_eq_inv_pow_bounds (p + Q * I) 1 1 0 I hQ
    grw [← mul_le_mul_iff_left₀ (na.trans_gt _), ← norm_mul, show _ * _ = p * P ^ I *
      (d⁄dX m).coeff _ by simp [hμ, pow_add, pow_mul, add_right_comm, ModEq.rfl, coeff_derivative,
      field], hm, coeff_mul, mul_sum, norm_sum_le_of_forall_le_of_nonneg _]
    simp [coeff_derivative] at *; rintro (_ | i) j x; swap; obtain ⟨J, rfl⟩ | _ := em (Q ∣ j)
    obtain ⟨_ : J ≤ I + 1, c, nc', B⟩ := by nlinarith, exists_norm_eq_inv_pow_bounds i 1 0 J I hQ
    grw [(le_div_iff₀ _).2 (hn i), nc', ← sq_le_sq₀]; any_goals simp [*]; positivity
    by_cases! J ≠ 1; grw [hw]
    repeat simp [*, apply_ite, pow_right_comm _ I, field, ← cast_succ, -hQ, ← hQ, hQ ▸ nc, Fact.out,
      pow_le_pow_iff_right₀, norm_p_eq_inv, ← pow_mul, ← pow_add]; clear! Z ϖ n m; cases he <;>
      grind [ModEq.eq_of_abs_lt]
  grind [_root_.norm_zero, inv_mul_le_one_of_le₀]

end

/-- Θ(ϖZ) is integral in degrees ≤ B whenever Z are series over 𝔬 without constant term whose
couplings ∑ Z_{σ,c}^{p^j} Z_{pr_j σ,c}, j ∈ S, vanish modulo p and θ. -/
def IsIntegralOnNullCone {p} [Fact p.Prime] {Φ c} [Fintype Φ] [Fintype c] (pr : ℕ → Φ → Φ) (S :
  Finset ℕ) (ϖ : ℂ_[p]) θ B (Θ : MvPowerSeries _ ℂ_[p]) := ∀ {τ} (Z : Φ × c → _), (∀ x,
  (Z x).constantCoeff = 0) → (∀ {Q : Type} [CommRing Q] [CharP Q p] (φ : _ →+* Q), φ (.C θ) = 0 →
  ∀ j ∈ S, φ (∑ x, Z x ^ p ^ j * Z (pr j x.1, x.2)) = 0) →
  ∀ ⦃m⦄, m.degree ≤ B → ‖(Θ.subst fun x ↦ ϖ • @seriesToCp p _ τ (Z x)).coeff m‖ ≤ 1

open PowerSeries Complex IsUltrametricDist ComplexConjugate Nat

attribute [-simp] map_smul

attribute [local simp] coeff_X subst_smul subst_sub subst_pow subst_X coeff_derivative
  congruencePart ite_apply ModEq.rfl NeZero.one_le NeZero.ne norm_p_eq_inv pow_eq_one_iff_of_nonneg
  MulChar.map_zero pow_le_one_iff_of_nonneg

attribute [local simp ←] subst_comp_subst_apply Real.rpow_mul_natCast Real.rpow_add_one

/-- First-order Taylor formula for a substitution tangent to the identity: if Z ≡ X modulo
X^{m+1}, then g(Z) ≡ g + g′(0)(Z − X) modulo X^{m+2}. -/
lemma coeff_subst_tangent {p} [Fact p.Prime] {Z : ℂ_[p]⟦X⟧} {m} (h : X ^ (m + 1) ∣ Z - X) k
    (hk : k ≤ m + 1) g : coeff k (subst Z g) = coeff k g + coeff 1 g * coeff k (Z - X) := by
  obtain ⟨W, ⟨⟩⟩ := h.imp fun _ ↦ eq_add_of_sub_eq
  induction k generalizing g <;> rw [g.eq_X_mul_shift_add_const, subst_add, subst_mul] <;> simp_all
    [add_mul, tsub_eq_zero_of_le, mul_assoc, coeff_X_pow_mul', le_of_succ_le, ← C.eq_def]; grind

/-- Let p ≥ 13 if (p/d) ≠ 1. Some T ∈ 𝔬[[φ]], |ϖ| = p^{−ρ_p}, q = p^e > 1, 1/p ≤ |π| < 1 have
T(ϖX) = ϖS, S integral, S(0) = 0, S − S^q ≡ X mod π. If (p/d) ≠ 1, some integral
ψ ≡ u₀X² + u₁S^{p+1} + u₂S^{p+q} mod π (u₀ = 0, u₁ a unit unless p = d = q) gives, for n prime to p,
a unit N and κ, |κ| = p^{(1−(p/d))/2−1/(p−1)}, with (U_yθ)(ϖX) ∈ (exp(κψ)𝔬[[X]])(NX) whenever
ny ∈ Λ.

Normal form of theta series at non-split primes. -/
lemma CMLattice.exists_formal_parameter {d} [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact
  p.Prime] [PadicPlace p] : ∃ e ϖ, ∃ (π : valRingCp p) (S E : (valRingCp p)⟦X⟧), (e ≠ 0 ∧ ‖ϖ‖ =
  p ^ (-nonsplitWeight d p) ∧ (↑p)⁻¹ ≤ ‖π.1‖ ∧ ‖π.1‖ < 1 ∧ (seriesToCp S).constantCoeff = 0 ∧
  S - S ^ p ^ e = X + π • E ∧ ∃ T ∈ C.phiSeriesRing, rescale ϖ T = ϖ • seriesToCp S) ∧
  (chiK d p ≠ 1 → 13 ≤ p → ∃ u₀ u₁ u₂ : valRingCp p, ∃ R ψ, ‖π.1‖ = p ^ ((chiK d p - 1) / 2 : ℝ) ∧
  (e = 1 ∧ p = d ∨ e = 2 ∧ u₀ = 0 ∧ ‖u₁.1‖ = 1) ∧ ψ = seriesToCp (u₀ • X ^ 2 + u₁ • S ^ (p + 1) +
  u₂ • S ^ (p + p ^ e) + π • R) ∧ ψ.constantCoeff = 0 ∧ ∀ n, p.Coprime n → ∃ N κ : ℂ_[p],
  (‖N‖ = 1 ∧ ‖κ‖ = p ^ ((1 - chiK d p) / 2 - 1 / (p - 1) : ℝ)) ∧ ∀ y : ℂ, n * y ∈ C.Λ → ∃ V, rescale
  ϖ (taylorVia ιₚ (C.twistedTranslate 1 y C.θ)) = rescale N (expSubst (κ • ψ) * seriesToCp V)) := by
  let a := ite (p = d) (I * √d) p
  obtain ⟨e, s, ha, hq, hs, hρ, h', t, K, he, hπ⟩ : ∃ e s : ℕ, a ∈ quadInt d ∧ primeNorm d p =
    p ^ e ∧ ‖ιₚ a‖ ^ 2 = (↑p)⁻¹ ^ s ∧ nonsplitWeight d p = s / 2 / (primeNorm d p - 1) ∧
    chiK d p = 1 + s - 2 * e ∧ 1 < p ∧ (e = 1 ∧ a = p ∧ s = 2 ∨ a * conj a = primeNorm d p ∧
    Odd p ∧ 2 < p ∧ e = s ∧ (e = 1 ∧ p = d ∨ e = 2)) ∧ e ≠ 0 ∧ ‖ιₚ a‖ < 1
  obtain ⟨rfl, _⟩ | ⟨_, _ | _⟩ := chiK_cases d p <;> [use 1, 1; use 1, 2; use 2, 2] <;> simp [a,
    nonsplitWeight, ← sq, map_sqrt_neg_sq, mul_pow, ← norm_pow, -map_mul, map_mul conj,
    sqrt_neg_mem_quadInt, *, ← ofReal_pow, inv_lt_one_iff₀,
    ← sq_lt_one_iff₀] <;> grind [QuadField.chiK_two, Fact, prime_def, Prime.odd_iff]
  obtain ⟨m, hm⟩ := exists_eq_add_one.2 (pow_pos t.le e)
  have M : NeZero m := ⟨by aesop⟩
  obtain ⟨⟨L, L₂, L0, L1, hθ, dL, nL, hL⟩, pm, ζ, hζ⟩ := C.exists_log_theta, ((coprime_pow_left_iff
    he.bot_lt p m).1 (by simp [*])).norm_natCast_eq_one ℂ_[p],
    @HasEnoughRootsOfUnity.prim ℂ_[p] _ m _
  obtain ⟨nζ, G, g : @IsSeriesGenerator p _ seriesToCp.range X, tX : @seriesToCp p _ _ X = X, l⟩ :=
    (hζ.isOfFinOrder M.1).norm_eq_one, C.isSeriesGenerator_translatedWpDeriv, by
    simp [IsSeriesGenerator, eq_comm], map_X _, hm ▸ le_self_pow he p
  have hi (i : ℤ) := hL (ζ ^ i, _) (mem_normPairClosure_of_pow_eq _ (by simp [*])
    (by simp [*, pow_succ, ← zpow_natCast, zpow_comm ζ i, hζ.zpow_eq_one]))
  have hT@⟨_, _⟩ := G.of_mem (congr($(congruencePart_eq_sum hζ 1 _) ∈ _).ge (G.smul_mem
    (by simp [*]) (sum_mem fun i _ ↦ G.smul_mem (by simp [*]) (hi i).1))) (by simp) (by simp)
  set T := @congruencePart p _ m 1 _
  obtain ⟨Z, Z0, TZ, ZT, hZ⟩ := hT.exists_subst_inverse
  obtain ⟨sZ : HasSubst Z, Z1⟩ := by simpa, by simpa [*] using congr(coeff 1 $TZ)
  have z i := congr(subst (subst Z $(show ζ ^ i • T = rescale (ζ ^ i) T by
    ext; simp +contextual [T, pow_right_comm ζ i, pow_eq_pow_of_modEq (b := 1) _ hζ.1])) Z)
  simp [*, ← rescale_eq_subst] at z
  have R n := congr(coeff (n + 1) $(z 1))
  simp [hζ.pow_eq_one_iff_dvd, pow_succ, hζ.ne_zero, or_iff_not_imp_left] at R
  have hX : ∀ k < m + 1, coeff k (Z - X) = 0
  rintro (_ | _ | k) <;> simp +contextual [not_dvd_of_pos_of_lt, *]
  obtain ⟨hd, hg, ⟨ϖ, τt⟩, wi⟩ := coeff_subst_tangent (X_pow_dvd_iff.2 hX), hZ.1 (G.rescale_mem
    (hL _ (subset_closure ⟨_, ha, rfl⟩)).1 hT.generator_mem), IsAIC.exists_pow_eq m (-coeff (m + 1)
    Z)⁻¹, (g.exists_mul_eq_one (hZ.1 (C.deriv_mem_phiSeriesRing hT.generator_mem))
    (by simp [← coeff_zero_eq_constantCoeff,
    *])).elim fun _ k ↦ inv_unique k.2 ((derivative_subst sZ).symm.trans (by simp [*])) ▸ k.1
  have cZ k hk := by simpa [hX k hk] using hd k (le_of_lt hk)
  have U k := C.one_le_norm_coeff_translatedWp_nonsplit fun f ↦ (fun i ↦
    norm_lt_one_of_eq_mul_add_mul (i p) (v := -coeff p (Z - X) * p) (i 1)
    (by simp [*]; ring) norm_p_lt_one k) ∘ mem_range_seriesToCp.1 ∘ hZ.1
  replace τt : coeff (m + 1) Z = -(ϖ ^ m)⁻¹ := by simp [τt]
  have cg k := (mem_range_seriesToCp.1 hg (m + 1)).eq_of_not_lt (K.elim k fun K k ↦
    C.exists_unit_coeff_degree_le Z0 Z1 hZ.1 ⟨C.5 ha, by simp [*]⟩ K.2.1.pow hg (by simp [*])
    (by simp [*]) fun n h ↦ (hm ▸ h).eq_or_lt.elim (· ▸ k.ne) (by simp +contextual [← cZ _ · T,
    hπ.ne, -subst_rescale_eq_subst_smul, apply_ite, *]))
  simp [eq_sub_of_add_eq (hd _ .refl T).symm, ← sub_eq_add_neg, ← sub_one_mul, mul_assoc, hπ.ne, *,
    norm_sub_eq_max_of_norm_sub_ne_norm_sub _ (ιₚ 0), pow_succ, -subst_rescale_eq_subst_smul,
    hπ.le] at cg
  have nπ := eq_of_div_eq_one (cg fun h _ _ ↦ by
    simp [h] at hm; simpa [*, field] using mt U (·.2 (by omega)))
  rw [nπ, ← norm_pow] at hs hπ
  have ϖ0 : ϖ ≠ 0 := (by simp [·, eq_comm] at hs)
  have E : (ϖ ^ m)⁻¹ • (X - X ^ (m + 1) - ϖ⁻¹ • rescale ϖ Z) ∈ seriesToCp.range
  rw [mem_range_seriesToCp]
  rintro (_ | k) <;> (try obtain ⟨_ | _ | j, ⟨⟩⟩ | _ := em (m ∣ k)) <;> simp [pow_mul,
    pow_succ' ϖ, mul_assoc, ne_of_apply_ne (m ∣ ·), *]
  obtain ⟨b, nb, c⟩ := exists_norm_eq_inv_pow_bounds (m * (j + 2)) 0 1 0 (j + 2) hm
  grw [← mem_range_seriesToCp.1 wi, coeff_derivative, norm_mul, nb, ← mul_assoc, mul_comm]; gcongr
  rw [← sq_le_sq₀, mul_pow, pow_right_comm, ← norm_pow] <;> simp [*, -norm_pow, field, ← pow_mul,
    ← pow_add, pow_le_pow_iff_right₀]; clear * - K t c; grind [ModEq.eq_of_abs_lt,
    PrimeSevenModEight]
  obtain ⟨S, S0, u, -, i⟩ :=
    (g.of_mem (by simpa [*] using (sub_mem (sub_mem g.generator_mem (pow_mem g.generator_mem
    m.succ)) (g.smul_mem hπ.le E))) (by simp [*]) (by simp [*])).exists_subst_inverse
  choose c hc using fun {g} ↦ (@i g).1; have ZS f := by
    simpa [← u, *, -u] using (rescale_eq_subst ϖ f).symm
  refine have nϖ := by rw [← pow_left_inj₀ (n := m * 2), pow_mul,
      ← norm_pow, hs] <;> simp [*, ← mul_assoc]; bound
    ⟨e, ϖ, ⟨_, hπ.le⟩, c g.generator_mem, c E, ⟨he, nϖ, by rw [← sq_le_sq₀, hs] <;> bound, hπ,
    by simp [*], map_injective _ (valRingCp p).subtype_injective (by simp [map, *]), T,
      hT.generator_mem, by simp [← ZS, *]⟩, fun _ p13 ↦ ?_⟩
  obtain ⟨⟨⟩, -, o, -, ⟨⟩, he⟩ := by simpa [translatedWp] using congr(coeff 0 $dL),
    K.resolve_left (by omega)
  let L₁ := L - coeff 2 L • X ^ 2
  have dL : d⁄dX (d⁄dX L₁) = taylorVia ιₚ C.translatedWp
  simp [L₁, *, sq, smul_eq_C_mul]
  obtain ⟨b, v, r⟩ := norm_coeff_le_of_deriv p13 (by omega) hm hs ϖ0 (derivative_subst sZ ▸ mul_mem
    (hZ.1 (dL ▸ taylorVia_translatedWp_mem_phiSeriesRing _)) wi) wi
    (by simp [↓cZ, ↓coeff_derivative, L₁, *]) R τt (fun k _ ↦ (cZ k
    (by omega) L₁).trans (by interval_cases k <;> simp [L₁, *])) (derivative_subst sZ) rfl
  set κ := ϖ ^ _ / _; set ψ := κ⁻¹ • rescale ϖ (congruencePart m (p + 1) L)
  refine Exists.elim ?_ fun w : ‖_‖ ≤ 1 ↦ (⟨⟨coeff 2 ψ, w⟩, ⟨_, b⟩, ⟨_, v⟩, c r, ψ, ?_, ·, by
    symm; simp only [map_add, seriesToCp_smul, *, ↓congruencePart_eq_sum hζ _ (.subst Z
      _), ↓rescale_subst Z0, ← subst_rescale_eq_subst_smul _ sZ, ← coe_substAlgHom sZ, ← map_sum,
      ← congruencePart_eq_sum hζ, ← map_smul]
    ext; simp [*, coe_substAlgHom, ψ, L₁, -ite_smul]; split <;> simp [*], by
    simp [ψ, *], fun n k ↦ have : n ≠ 0 := (by simp [·, t.ne'] at k)
    ⟨(n * m)⁻¹, -(n * m) ^ 2 * κ, cast (by simp [k.norm_natCast_eq_one, *]; rfl) ?_, fun y hy ↦
      (C.rescale_translate_eq_theta_pow_mul
      (δ := ↑(n * m)) ⟨C.5 (by simp [mul_mem]), by simp_rw [map_natCast]; norm_cast⟩ (by simp [*])
      (by simpa [mul_assoc, mul_comm n] using nsmul_mem hy m)).elim fun _ e ↦ ⟨c (g.rescale_mem
      (by simpa [↓mem_range_seriesToCp, apply_ite] using hπ.le) (hZ.1 (mul_mem (pow_mem
      (prod_mem (t := .range m) fun i _ ↦ G.rescale_mem (hi i).1 (hi (-i)).2.1) (n * m * n)) e.1))),
      by simpa [κ, -inv_div, *, ↓subst_rescale_eq_subst_smul, rescale_subst, ψ, sq, ← mul_assoc,
      ← subst_pow, exp_pow_eq_rescale_exp, ← expSubst_sum,
      ← expSubst_add, ↓congruencePart_eq_sum hζ, rescale_rescale, hζ.ne_zero,
      smul_smul, ← cast_smul_eq_nsmul ℂ_[p], mul_comm ϖ] using congr(rescale ϖ (rescale (n * m :
      ℂ_[p])⁻¹ $(e.2)))⟩⟩⟩) <;> obtain ⟨h, ⟨rfl, rfl⟩ | rfl⟩ := eq_tsub_of_add_eq hm.symm, he <;>
    simp only [ψ, congruencePart, coeff_mk, map_smul, coeff_rescale, Subtype.ext_iff] at b ⊢
  simp [a] at nπ hs
  split; simpa [κ, ← hs, nπ, pow_sub₀, ϖ0, pow_succ, h, field, (mod_cast
    o.coprime_two_right.norm_natCast_eq_one _ : ‖(1 + 1 : ℂ_[p])‖ = 1)] using nL
  simp
  have : p < m := by nlinarith only [hm, t]
  rw [ite_eq_right (absurd ·.symm.le_of_lt_add (by omega)), b.antisymm ((U (by simp [hX, this.le])
    ).1.trans _)] <;> simp [← dL, κ, cZ, this, field, ← cast_succ, -cast_add,
    @Coprime.norm_natCast_eq_one p]
  repeat simp [κ, *, -hm]; congr 1; field [sub_eq_zero, t.ne']
