import GRH.Lib.General.Algebra.AdicRingHomExt
import GRH.Lib.General.Algebra.JetChainRule
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Local heights and Tate's trick, and integrality of CM theta functions and torsion translates.
For prime discriminant with 2 split, all primes are covered here, including 2 and the supersingular
ones. By good reduction the naive height is exactly quadratic under doubling, so no limit is taken,
and Tate's trick bounds translates and isogeny pull-backs. Source: J. Silverman, Advanced Topics
(1994), VI; K. Bannai, S. Kobayashi, Algebraic theta functions and p-adic interpolation of
Eisenstein-Kronecker numbers, Duke Math. J. 153 (2010), 2.14-2.16; B. Mazur, J. Tate, The p-adic
sigma function, Duke Math. J. 62 (1991).

General lemmas of commutative and general algebra (textbook or folklore).

Known result: Good reduction of CM curves, and Weber's unit for discriminants 1 modulo 8. For prime
discriminant with 2 split, an explicit cubic has unit discriminant at every prime. The proof uses a
monotone quantity along the cycle of 2-isogenies, without modular polynomials or Tate modules.
Source: J. Milne, Complex Multiplication (2020); for the unit, M. Deuring, Die Klassenkörper der
komplexen Multiplikation (1958), S. Lang, Elliptic Functions, B. Birch, Weber's class invariants,
Mathematika 16 (1969).

This file: Exponential of formal series; Legendre bounds for valuations of factorials. Normalised CM
cubic has unit discriminant at every prime; ultrametric bounds. Local height of the curve; Tate's
trick under torsion translation and isogeny. Rings of integral power series in a parameter;
stability for the curve's parameter. -/

open Nat PowerSeries WithPiTopology

variable {p : ℕ} [hp : Fact p.Prime] {σ} {c : ℂ_[p]} (a : MvPowerSeries σ ℂ_[p]) {n K : ℕ}

/-- The series exp(a): a substituted into the exponential series over ℂ_p (meaningful when a has
no constant term). -/
noncomputable abbrev expSubst := (exp ℂ_[p]).subst a

@[simp] lemma constantCoeff_subst_mv (ha : a.constantCoeff = 0) f : (subst a f).constantCoeff =
    constantCoeff f := by simp_all [constantCoeff_subst, finsum_eq_single _ 0]

lemma expSubst_add {b} (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) : expSubst (a + b) =
  expSubst a * expSubst b := by apply inv_unique (x :=
  expSubst (-a - b)) <;> apply MvPowerSeries.pderiv.ext <;> simp [*] <;>
  simp [subst, ← derivative.eq_def, derivative_exp, *] <;> grind

lemma expSubst_sum {I t} {a : I → _} (h : ∀ i, (a i).constantCoeff = 0) : expSubst (t.sum a) =
  ∏ i ∈ t, @expSubst p _ σ (a i) :=
  t.cons_induction (by simp [subst_zero_eq_C_constantCoeff]) (by simp_all [expSubst_add])

lemma norm_natCast_eq_inv_pow_padicValNat : n ≠ 0 → ‖(n : ℂ_[p])‖ = (↑p)⁻¹ ^ padicValNat p n :=
    (by simpa [Padic.norm_eq_zpow_neg_valuation, ·] using PadicComplex.norm_extends' p n)

/-- For p prime and n < p^K, one has 0 ≤ n/(p−1) − v_p(n!) ≤ K, a consequence of Legendre's
formula. -/
lemma padicValNat_factorial_mem_Icc (hn : n < p ^ K) : ↑(padicValNat p n !) ∈
    Set.Icc ((n : ℝ) / (p - 1) - K) (n / (p - 1)) := have := hp.1.one_lt; by
  simp_all [div_le_iff₀', le_div_iff₀', ← cast_pred this.le, ← digits_length_le_iff]; norm_cast
  grw [mul_add, sub_one_mul_padicValNat_factorial, List.sum_le_length_nsmul _ (p - 1), hn] <;>
    grind [→ digits_lt_base]

lemma rpow_le_norm_factorial :
  p ^ (-(n / (p - 1)) : ℝ) ≤ ‖(n ! : ℂ_[p])‖ := by grw [norm_natCast_eq_inv_pow_padicValNat,
  ← (padicValNat_factorial_mem_Icc (n.lt_pow_self Fact.out)).2] <;> simp [NeZero.one_le]

@[simp] lemma subst_rescale_eq_subst_smul (h : HasSubst a) f : (rescale c f).subst a = f.subst (c •
  a) := by rw [rescale_eq_subst, subst_comp_subst_apply (.smul_X' c) h, subst_smul h, subst_X h]

variable {d} (C : CMLattice d) {K : Type*} [Field K] (ι : ℂ →+* K) {p : ℕ}
  [Fact p.Prime] {x y : ℂ_[p]} [Fact n.Prime]

namespace CMLattice

@[simp ↓] lemma constantCoeff_taylorVia f :
    constantCoeff (taylorVia ι f) = ι (f 0) := congr(ι $constantCoeff_taylorAtZero)

lemma derivative_taylorVia [CharZero K] f : d⁄dX (taylorVia ι f) = taylorVia ι (deriv f) := ext
    (by simp [coeff_derivative, iteratedDeriv_succ', factorial, field])

attribute [local simp] CMLattice.derivative_taylorVia map_ofNat taylorVia sub_eq_add_neg

lemma taylorAtZero_congr {f g} (h : ∀ z, z + C.t ∉ C.Λ → f z = g z) : taylorAtZero f =
  taylorAtZero g := congr(.mk ($(Set.EqOn.iteratedDeriv_of_isOpen h
  C.isClosed_lattice.1.preimage_of_continuous · (C.t_notMem ∘ by simp)) / _))

lemma taylorVia_curve_eq : taylorVia ι C.translatedWpDeriv ^ 2 + .C (ι C.a₁) * taylorVia ι
  C.translatedWp * taylorVia ι C.translatedWpDeriv = taylorVia ι C.translatedWp ^ 3 + taylorVia ι
  C.translatedWp := by
  simpa (disch := fun_prop) using congr(map ι $(C.taylorAtZero_congr @C.weierstrass_equation))

@[simp] lemma derivative_taylorVia_translatedWp [CharZero K] :
    d⁄dX (taylorVia ι C.translatedWp) = 2 *
  taylorVia ι C.translatedWpDeriv + .C (ι C.a₁) * taylorVia ι C.translatedWp := by
  simp (disch := fun_prop) [funext C.deriv_translatedWp]

@[simp] lemma derivative_taylorVia_translatedWpDeriv [CharZero K] :
    d⁄dX (taylorVia ι C.translatedWpDeriv) =
  1 + 3 * taylorVia ι C.translatedWp ^ 2 - .C (ι C.a₁) * taylorVia ι C.translatedWpDeriv := by
  simp (disch := fun_prop) [← neg_mul, C.taylorAtZero_congr @C.deriv_translatedWpDeriv_eq]

end CMLattice

section

open IsUltrametricDist QuadField NumberField PeriodPair Submodule

/-- For d a prime ≡ 7 mod 8, the discriminant a₁⁴ − 64 of a CM datum is a p-adic unit under
every ι : ℂ → ℂ_p; so the curve has good reduction everywhere.

Known result: Good reduction of CM curves; Weber's unit for discriminants 1 modulo 8. -/
lemma CMLattice.norm_disc_eq_one [PrimeSevenModEight d] (ι : ℂ →+* ℂ_[p]) : ‖ι
  C.a₁ ^ 4 - 64‖ = 1 := by
  let v C := (@periodPair d C).G 4 / C.sumInvPow (C.t - quadGen d * C.t) 4 * 240 - 16
  let a x := ‖ι (v x)‖
  refine (Finset.prod_induction_nonempty (fun _ : ClassGroup (𝓞 (QuadField d)) ↦ .mk0 (1 +
    .spanSingleton _ (c₀ d / -2)) (by simp [-map_div₀])) (fun 𝔠 ↦ ∀ C D,
    (∃ u, latticeModule D = scaledIdeal d (u, 𝔠) * latticeModule C) → (a C =
    a D → ‖ι C.a₁ ^ 4 - 64‖ = 1) ∧ (‖ι 4096‖ ≤ a D ∧ a C ∉ Set.Ioo 1 (a D) ↔ a C ∈ Set.Icc (a D) 1))
    (fun _ 𝔠 k _ C D ⟨v, e⟩ ↦ have ⟨E, w, _⟩ := C.exists_latticeModule_eq_scaledIdeal_mul 𝔠
    by grind [map_ofNat, norm_natCast_le_one ℂ_[p] 4096, k E D ⟨v / w, by simp [*, ← mul_assoc,
      ← map_mul]⟩]) Finset.univ_nonempty (fun _ _ C D ⟨u,
    hf⟩ ↦ ?_) C C (exists_eq_scaledIdeal_mul_of_mk_eq_one (by simp [-map_div₀]) _)).1 rfl
  let b := C.a₁ ^ 4 - 64
  suffices H : v D = b * -v C ∧ (48 + v C + b) * -v D = 4096
  simp [a, ← H.2, H, show v C ≠ 0 ∧ b ≠ 0 by grind]
  grind [map_ofNat, norm_add_le_max, norm_add_eq_max_of_norm_ne_norm, norm_natCast_le_one ℂ_[p] 48]
  rcases C.quadGen_mul_t_notMem, @conj_quadGen, C.two_t_mem, C.t_notMem,
    D.mul_mem_or_mul_sub_t_mem (.inr rfl) (u * C.t)
  set T := quadGen _ * _
  replace hf x : u.1 * x ∈ D.Λ ↔ x + T ∈ C.Λ ∨ x ∈ C.Λ := .trans (b := ∃ l ∈ C.Λ, ∃ m ∈ C.Λ,
    l + quadGen d / -2 * m = x) (by simpa [scaledIdeal, map_span, one_eq_span, Submodule.sup_mul,
    mul_assoc, mem_span_singleton_mul, -map_div₀] using! congr(u * x ∈ $hf)) ⟨fun ⟨l, hl, m, _⟩ ↦ by
    grind [→ sub_mem hl, C.mul_mem_or_mul_sub_t_mem (.inl rfl) (m / 2)], by grind [C.Λ.zero_mem]⟩
  have S y z (h : u.1 * y - z ∈ D.Λ) := have k L (y : ℂ) := (Equiv.addLeft y).hasSum_iff.2 ((
    hasSum_subtype_iff_indicator (f := ((· - y) ^ 4 :)⁻¹)).1 (hasSum_sumInvPow L y (by lia)))
    (u.mulLeft.hasSum_iff.2 (k D.1 z)).unique ((((k C.1 (T + y)).add (k C.1 y)).div_const (u ^ 4)
    ).congr_fun (by simp [Set.indicator]; grind [add_mem_cancel_left, =_ add_mem_cancel_left h]))
  simp (disch := grind) [S (C.t - T), by simpa using S 0 0, field]
  grind (ringSteps := 999999) [by simpa [θ_sq, field, *] using C.phiThetaCube_spec (-T) (by grind),
    translatedWp, g₂_eq, derivWeierstrassP_eq_zero_iff, → C.5 quadGen_mem_quadInt, a₁_sq,
    deriv_derivWeierstrassP, weierstrass_disc_ne_zero, g₂,
    → derivWeierstrassP_sq, → derivWeierstrassPExcept_of_notMem, deriv_derivWeierstrassPExcept_self]

lemma norm_lt_one_of_eq_mul_add_mul : ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ∀ {u v z}, z =
  x * u + y * v → ‖u‖ < 1 → ‖v‖ < 1 → ‖z‖ < 1 := by
    simp_all [(norm_add_le_max ..).trans_lt, mul_lt_one_of_nonneg_of_lt_one_right]

attribute [-simp] Asymptotics.isBigO_top sup_of_le_left sup_of_le_right

attribute [local simp] Asymptotics.IsBigO.add Asymptotics.IsBigO.const_mul_left
  Asymptotics.isBigO_zero thetaShift_apply CMLattice.monomialSection CMLattice.t_notMem abs_of_pos
  add_mem_cancel_left map_ofNat mul_assoc pow_le_one_iff_of_nonneg

variable [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p] (w)

/-- For d a prime ≡ 7 mod 8, a CM lattice and any embedding ι: ℂ → ℂ_p, the invariant a₁ is
p-adically integral: |ι(a₁)| ≤ 1. -/
lemma CMLattice.norm_a₁_le_one : ‖ιₚ C.a₁‖ ≤ 1 := by
    simpa using Valued.integer.mem_iff.1 (add_mem (C.norm_disc_eq_one _).le (ofNat_mem _ 64))

/-- The naive p-adic height h(w) = max(|ι(σ(w))|, |ι(θ(w))|) of the point w, for the functions σ
and θ of C and a ring map ι : ℂ → ℂ_p. -/
noncomputable abbrev CMLattice.naiveHeight := max ‖ιₚ (C.σ w)‖ ‖ιₚ (C.θ w)‖

lemma CMLattice.naiveHeight_spec : 0 < C.naiveHeight w ∧ C.naiveHeight (2 * w) =
  C.naiveHeight w ^ 4 ∧ ‖ιₚ (C.phiThetaCube w)‖ ≤ C.naiveHeight w ^ 3 := by
  obtain ⟨c, e, h⟩ : ∃ c ∈ [ιₚ (C.σ w), ιₚ (C.θ w)], C.naiveHeight w ≤ ‖c‖ := by grind
  have : c ≠ 0 := by aesop
  have D n x : c ^ n ∣ ιₚ x := by aesop
  obtain ⟨⟨a, _⟩, ⟨b, _⟩, ⟨g, _⟩, ⟨x, _⟩, u, v⟩ := D 1 (C.σ w), D 1 (C.θ w), D 3 (C.phiThetaCube w),
    D 4 (C.σ (2 * w)), congr(ιₚ $(C.σ_two_mul_sq w)), congr(ιₚ $(C.phiThetaCube_sq_add w))
  rw [h.antisymm (by aesop)]; simp [naiveHeight, *, field, ← mul_max_of_nonneg, mul_pow,
    ← mul_sub] at *
  refine ⟨eq_of_le_of_not_lt ?_ (mt max_lt_iff.1 fun _ ↦
    (norm_lt_one_of_eq_mul_add_mul ?_ ?_ (.refl ((a * b) ^ 2 |> fun
    w ↦ ιₚ C.a₁ ^ 2 - 8 * w |> fun B ↦ B * x * x + (B * (B + 12 * w) - 64) * (1 - w ^ 2))) ?_
    (by grind [norm_sub_rev])).ne (by grind [C.norm_disc_eq_one ιₚ])), by_contra (· ?_)⟩
  rw [max_le_iff, ← sq_le_one_iff₀, ← norm_pow, u]
  any_goals rw [eq_sub_of_add_eq ((eq_inv_mul_iff_mul_eq₀ (by bound)).2 v)]
  repeat' rw [← Valued.integer.mem_iff]
  repeat bound [(norm_inv g).trans_le (c := 1), C.norm_a₁_le_one]

/-- For d a prime ≡ 7 mod 8, a ring map ι : ℂ → ℂ_p and x = (a, b, c), the monomial θ^a·σ^{2b}·G^c,
G = `CMLattice.phiThetaCube`, satisfies |ι(value at w)| ≤ h(w)^{a+2b+3c}, with h the height
`CMLattice.naiveHeight`. -/
lemma CMLattice.norm_monomialSection_le x w : ‖ιₚ (C.monomialSection x w)‖ ≤
  C.naiveHeight w ^ monomialDeg x := by simp [pow_add, pow_mul']; bound [C.naiveHeight_spec w]

/-- Tate's trick. Let d ≡ 7 mod 8 be prime, a: C → C′ an isogeny of degree N, y torsion modulo
Λ′, h, h′ the heights `CMLattice.naiveHeight` at a p-adic place ι. If |ιg| ≤ h′^m on ℂ, then
|ι((U′^m_y g)(az))| ≤ h(z)^{mN} for all z.

Known result: Local heights and Tate's trick; integrality of CM theta functions and torsion
translates. -/
lemma CMLattice.norm_translate_le_naiveHeight_pow {C' a g N m} (h : C.IsIsogeny (@periodPair d C') a
  N) y n (hn : n ≠ 0) (hl : n • y ∈ C'.Λ) (hg : ∀ w, ‖ιₚ (g w)‖ ≤ C'.naiveHeight w ^ m) z : ‖ιₚ
  (C'.twistedTranslate m y g (a * z))‖ ≤ C.naiveHeight z ^ (m * N) := by
  let r (C : CMLattice d) a N z := ‖ιₚ (C'.twistedTranslate 1 y 1 (a * z))‖ * C'.naiveHeight
    (a * z + y) / C.naiveHeight z ^ N
  have K {C a N} (H : r C' 1 1 ≤ 1 ⊔ r C a N) (h : C.IsIsogeny _ a N) : r C a N ≤ 1 :=
    have A {m g} : g ∈ C.sections m → (ιₚ <| g ·) =O[⊤] (C.naiveHeight ^ m) :=
      (span_induction (fun _ ⟨x, k, e⟩ ↦ e ▸ k.2 ▸ .of_norm_le (C.norm_monomialSection_le x))
      (by simp) (by simp_all) (by simp_all) <| sections_le_span_monomialSection _ _ ·)
    have B {f} k : (ιₚ <| C'.twistedTranslate 1 y f <| a * ·) =O[⊤] (C.naiveHeight ^ N) := .of_pow
      (by omega : n * 2 ≠ 0) ((A (C.comp_mul_mem_sections h (IsAppellHumbert.thetaShift_mem_of_dual
      (f := f ^ (n * 2)) (mem_dualLattice_nsmul.2 (isAppellHumbert_hermitianForm.le_dualLattice
      (mul_nsmul y .. ▸ nsmul_mem hl 2))) k))).congr (by simp [↓thetaShift_pow])
      (by simp [pow_mul']))
    le_ciSup (((B (by simpa [← pow_mul'] using monomialSection_mem _ (0, n, 0))).prod_left (B
    (by simpa using monomialSection_mem _ (_, 0)))).bound.imp (by simp [upperBounds, r,
      div_le_iff₀, ↓naiveHeight_spec,
      mul_max_of_nonneg])) |> fun b z ↦ (b z).trans (not_lt.1 fun h ↦ (pow_lt_pow_right₀ h
    (by decide : 2 < 4)).not_ge ((Real.iSup_pow (by bound) 4).trans_le (ciSup_le fun z ↦ by
    grw [sq, ← b (2 * z), ← (H _).trans (max_le h.le (b (a * (2 * z) + y)))]
    simp [(naiveHeight_spec ..).1.ne', field, ← (naiveHeight_spec ..).2.1, pow_right_comm _ N,
      ← norm_pow, ← norm_mul, ← map_pow, ← map_mul, ← Complex.exp_nsmul, ← Complex.exp_add]
    ring; rfl)))
  grw [pow_mul', ← (div_le_one _).1 (K (le_sup_of_le_left (K _ _)) h z), mul_pow, ← hg] <;> simp
    [↓naiveHeight_spec, ← norm_pow, ← map_pow, ← Complex.exp_nsmul, ← mul_div]

end

attribute [-simp] RingHomCompTriple.comp_apply add_eq_zero

/-- The series T has constant term 0 and linear coefficient 1, and A = 𝔬[[T]] consists exactly
of the g(T) with g an integral series. -/
def IsSeriesGenerator (A : Subring ℂ_[p]⟦X⟧) T := constantCoeff T = 0 ∧ T.coeff 1 = 1 ∧ ∀ f, f ∈ A ↔
  ∃ g : (valRingCp p)⟦X⟧, f = subst T (seriesToCp g)

variable {a c : ℂ_[p]} {B} {T : ℂ_[p]⟦X⟧} (h : IsSeriesGenerator B T) (k :
  T.constantCoeff = 0) {f : ℂ_[p]⟦X⟧}

@[simp] lemma constantCoeff_rescale : (rescale a f).constantCoeff =
  f.constantCoeff := by simp [rescale]

@[simp] lemma rescale_smul : rescale a (c • f) = c • rescale a f := ext (by simp [field])

@[simp] lemma constantCoeff_subst_eq (k : T.constantCoeff = 0) :
    constantCoeff (f.subst T) = f.constantCoeff := constantCoeff_subst_mv _ k f

attribute [local simp ↓] IsSeriesGenerator HasSubst.of_constantCoeff_zero' coe_substAlgHom
  constantCoeff_substInvOfIsUnit isUnit_iff_constantCoeff map_subst subst_X subst_comp_subst_apply
  subst_smul subst_substInvOfIsUnit_left subst_substInvOfIsUnit_right mul_le_one₀

include k in
@[simp ↓] lemma coeff_one_subst : coeff 1 (f.subst T) = f.coeff 1 * T.coeff 1 := by
  rw [coeff_subst', finsum_eq_single _ 1] <;> simp_all [coeff_one_pow]; lia

lemma rescale_subst (k : T.constantCoeff = 0) {f : ℂ_[p]⟦X⟧} :
    rescale a (f.subst T) = f.subst (rescale a T) := by simp_all [rescale_eq_subst]

@[fun_prop] lemma continuous_subst (h : HasSubst T) : Continuous (subst (R := ℂ_[p]) T) :=
  continuous_pi fun α ↦ .congr (by simp [finsum_eq_sum_of_support_subset_of_finite _ _
    ((@mk ℤ 1).coeff_subst_finite h α)]; fun_prop [coeff]) (coeff_subst h · α |>.symm)

include h

lemma IsSeriesGenerator.exists_subst_inverse : ∃ Z :
    ℂ_[p]⟦X⟧, constantCoeff Z = 0 ∧ subst Z T = X ∧ subst T Z = X ∧ ∀ {f}, f ∈ B ↔ subst Z f ∈
    seriesToCp.range :=
  ⟨T.substInvOfIsUnit (by aesop), h.elim (by aesop (add safe (by apply exists_congr)))⟩

lemma IsSeriesGenerator.generator_mem : T ∈ B := (h.2.2 T).2 ⟨X, by simp_all [← map.eq_def]⟩

lemma IsSeriesGenerator.smul_mem : ‖c‖ ≤ 1 → f ∈ B → c • f ∈ B :=
  h.exists_subst_inverse.elim (by simp_all [↓mem_range_seriesToCp])

lemma IsSeriesGenerator.norm_coeff_le_one : f ∈ B → ‖f.constantCoeff‖ ≤ 1 ∧ ‖f.coeff 1‖ ≤ 1 := by
  simp_all; use fun g _ ↦ ⟨(g 0).2, (g _).2⟩

lemma IsSeriesGenerator.of_mem : f ∈ B → f.constantCoeff = 0 → f.coeff 1 = 1 →
  IsSeriesGenerator B f := by
  simp_all [coeff]; introv _ _ _
  rw [(id (⟨subst (substInvOfIsUnit x _) ·, _⟩) : (subst x).Surjective).exists] <;>
    simp_all [constantCoeff, map]

lemma IsSeriesGenerator.exists_mul_eq_one : f ∈ B → ‖f.constantCoeff‖ = 1 → ∃ v ∈ B, f * v = 1 := by
  simp_all; use fun _ _ _ ↦ (isUnit_iff_exists_inv.1
    (by simpa)).imp (by simp_all [← coe_substAlgHom, ← map_mul])

lemma IsSeriesGenerator.rescale_mem : rescale a T ∈ B → f ∈ B → rescale a f ∈ B := by
  simp_all; use fun u e g _ ↦ ⟨g.subst u, have := e ▸ constantCoeff_rescale
    by simp_all [constantCoeff, map, rescale_subst]⟩

variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) [PadicPlace p]

/-- The subring 𝔬[[φ]] of ℂ_p[[z]]: integral power series in the Taylor series of φ read through
ι. -/
noncomputable def CMLattice.phiSeriesRing : Subring ℂ_[p]⟦X⟧ :=
  ((substAlgHom (a := taylorVia ιₚ C.translatedWpDeriv) (by simp)).1.comp (@seriesToCp p ..)).range

omit h

omit [PrimeSevenModEight d] in
lemma CMLattice.isSeriesGenerator_translatedWpDeriv : IsSeriesGenerator C.phiSeriesRing
  (taylorVia ιₚ C.translatedWpDeriv) := by simp [phiSeriesRing, eq_comm]

lemma CMLattice.taylorVia_translatedWp_mem_phiSeriesRing : taylorVia ιₚ C.translatedWp ∈
  C.phiSeriesRing := by apply (HenselianRing.is_henselian (I := .span {X}) _
  (@Cubic.monic_of_a_eq_one' _ 0 (1 - .C ⟨_, C.norm_a₁_le_one⟩ * X) (-X * X) _) 0 ..).imp fun _ h ↦
  IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub h.1.map .. <;> simp_all [translatedWp,
  ← map.eq_def,
  Cubic.toPoly, Ideal.mem_span_singleton'] <;> grind [taylorVia_curve_eq, C, map_X, constantCoeff_X]

/-- The ring 𝔬[[φ]] of integral power series in φ, viewed as series in z over ℂ_p, is stable
under d/dz. -/
lemma CMLattice.deriv_mem_phiSeriesRing : f ∈ C.phiSeriesRing → d⁄dX f ∈ C.phiSeriesRing :=
  fun ⟨_, e⟩ ↦ by aesop (add 1% [taylorVia_translatedWp_mem_phiSeriesRing,
  C.isSeriesGenerator_translatedWpDeriv.generator_mem,
  C.isSeriesGenerator_translatedWpDeriv.smul_mem, norm_a₁_le_one, (by simp [derivative_subst,
  ← smul_eq_C_mul]), (by erw [← map_pderiv, C.isSeriesGenerator_translatedWpDeriv.2.2]; tauto)])
