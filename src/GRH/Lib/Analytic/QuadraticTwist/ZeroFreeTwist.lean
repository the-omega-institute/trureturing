import GRH.Lib.Analytic.Primes.AuxiliaryPrimes
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Zero density for quadratic twists by mean values over real characters. This file
only finds one prime in a given class whose quadratic twists have no zero up to a given height right
of a line beyond the critical line. The proof uses a three-lines argument and a smoothed mean square
of Jacobi symbol sums. Source: Jutila, On mean values of Dirichlet polynomials with real characters,
Acta Arith. 27 (1975) 191-198.

This file: Some prime in a class has quadratic twists zero-free on a half-strip; three lines. -/
seal Finset.univ Finset.sum Finset.prod

open ArithmeticFunction DirichletCharacter Complex Moebius Finset Real ZMod vonMangoldt LSeries
  Filter jacobiSym legendreSym MeasureTheory Nat NumberTheorySymbols


variable {N : ℕ} [NeZero N] (ξ : DirichletCharacter ℂ N) (j : Fin 2) {η : ℝ}

omit [NeZero N] in
lemma norm_mul_moebius_le_one (n : ℕ) : ‖ξ n * μ n‖ ≤ 1 := by by_cases Squarefree n <;> simp [*]

open Set HadamardThreeLines in
/-- Three lines: for j ≤ 1, some C gives |Γ_j(s)|² ≤ C T^(−2η) whenever χ ≠ 1 is primitive mod q
≤ T² of parity j, L(s, χ) = 0, 1/2 + 9η ≤ re s ≤ 1, and the integrals `thetaTailIntegral` from 1/T
of the theta series of χ and μχ total at most T^(2η). -/
lemma three_lines_bound_of_LFunction_eq_zero : ∃ C,
  ∀ {η T : ℝ} {q} [NeZero q] {χ : DirichletCharacter ℂ q} {s}, 0 < η → χ.IsPrimitive → χ ≠ 1 →
  χ (-1) = (-1) ^ j.1 → 0 < T → q ≤ T ^ 2 → thetaTailIntegral j (χ ·) T⁻¹ + thetaTailIntegral j
  (fun n ↦ χ n * μ n) T⁻¹ ≤ T ^ (2 * η) → χ.LFunction s = 0 → 1 / 2 + 9 * η ≤ s.re → s.re ≤ 1 →
  ‖gaussianMellin j s‖ ^ 2 ≤ C / T ^ (2 * η) := (@gaussianMellin_differentiableOn_and_bdd j).2.imp'
  (9 + · ^ 2) fun G g η T q _ χ s _ hχ h1 hp hT hq J Z _ _ ↦ by
  have T1 := (one_le_sq_iff₀ hT.le).1 (hq.trans' (by simp [succ_le_iff]))
  obtain ⟨n, X⟩ := norm_mul_moebius_le_one χ,
    one_le_pow₀ (one_le_rpow T1 (by bound : 0 ≤ 2 * η)) (n := 2)
  -- `mellin f` is the Mellin transform of `f`, the series for `χ μ` cut at `1 / T`; `B` bounds it
  let f := (Ioi T⁻¹).indicator (gaussianTheta j fun n ↦ χ n * μ n)
  obtain ⟨⟨p, _, A⟩, b, _, B⟩ := mellin_differentiableOn_and_bounded
    (norm_gaussianTheta_char_le h1 hp), mellin_differentiableOn_and_bounded (D := 3 * T) (f := f)
    fun {t} k ↦ by
    by_cases i : T⁻¹ < t <;> simp [f, i, hT.le, exp_pos]
    grw [(summable_and_norm_gaussianTheta_le n k).2, mul_right_comm, ← div_inv_eq_mul _ T, i]
  let a := (9 + G ^ 2) * (T ^ (2 * η)) ^ 2
  have e w : mellin f w = _ := @indicator_smul .. ▸ setIntegral_indicator (by simp)
  refine .trans (.trans_eq' (norm_le_interp_of_mem_verticalClosedStrip' (z := s) (a := a) (b := a /
    T) (by bound) ⟨by bound, by bound⟩ (((gaussianMellin_differentiableOn_and_bdd.1.fun_pow
    2).fun_sub (p.fun_mul b)).mono (closure_preimage_re _ ▸ by grind [closure_Ioo])).diffContOnCl
    ⟨_, forall_mem_image.2 fun z k ↦ norm_sub_le_of_le (by simp; grw [g z k]) (norm_mul_le_of_le
    (A z k) (B z k))⟩ ?_ ?_) (by simp [mellin_gaussianTheta_char, *, show 0 < s.re by bound])) ?_
  any_goals intro z (hz : _ = _)
  -- on `re z = 1/2`: bound `mellin f` and `Γ_j L` by tail integrals; then use `J`
  · have N r g (k : 0 ≤ r) : _ ≤ thetaTailIntegral j g r := (norm_integral_le_integral_norm fun t ↦
      ofReal t ^ (z - 1) • gaussianTheta j g t).trans_eq (setIntegral_congr_fun (by simp) fun t
      i ↦ by norm_num [hz, rpow_neg, k.trans_lt i, le_of_lt, sqrt_eq_rpow]; ring)
    grw [norm_sub_le, norm_mul, norm_pow, g, e, inter_eq_right.2, N, mellin, N,
      thetaTailIntegral_zero_le_two_mul h1 hp hχ
      hT, two_mul_le_add_sq, pow_add_pow_le, J] <;> norm_num [hz] <;> first | positivity | nlinarith
  -- on `re z = 2`: `Γ_j² - Γ_j L · mellin f = Γ_j L ∫_0^{1/T} θ^μ(t) t ^ z dt / t`
  · have I := (integrableOn_exp_neg_Ioi 0).const_mul 3
    have P {c} h t k : ‖ofReal t ^ (z - 1) • gaussianTheta j c t‖ ≤ 3 * rexp (-t) :=
      (norm_mul_le_of_le
      le_rfl (summable_and_norm_gaussianTheta_le h k).2).trans_eq (by norm_num [k, hz]; field)
    erw [sq, ← mul_one (_ * _), ← mul_mu_eq_one χ, mul_mul_mul_comm, ← mellin_gaussianTheta,
      ← mellin_gaussianTheta n]
    grw [← mul_sub, e, norm_mul, mellin, norm_integral_le_of_norm_le I (ae_restrict_of_forall_mem _
      (P _)), integral_const_mul, integral_exp_neg_Ioi_zero, mellin, ← setIntegral_sdiff _
      (I.mono' (by fun_prop [gaussianTheta, gaussianMonomial]) (ae_restrict_of_forall_mem _ (P n))),
      norm_setIntegral_le_of_norm_le_const _ fun t j ↦ by grw [P n t j.1, ← j.1.out]]
    all_goals simp [hT.le, field] <;> nlinarith
  simp (disch := positivity) [← log_le_log_iff, a, field]
  nlinarith [log_nonneg T1]

/-- If m ≥ 1 and neither m nor 2m is a square, then |∑_{1 ≤ v ≤ X} (−v/m)| ≤ 2√m (1 + log m) for
all X; the factor at 2 of the Jacobi symbol is the principal character. -/
lemma norm_sum_jacobiSym_le {m} (hm : m ≠ 0) (h : ¬IsSquare m) (h' : ¬IsSquare (2 * m)) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, (J(-v | m) : ℂ)‖ ≤ 2 * √m * (1 + .log m) := by
  choose ψ E using @induction_on_primes (fun b ↦ ∃ ψ : DirichletCharacter ℂ b, b ≠ 0 → ∀ v : ℤ,
    ψ v = J(v | b)) (by simp) ⟨1, by simp [@Subsingleton.eq_one (ZMod 1)]⟩ fun p _ hp ⟨ψ, _⟩ ↦
    mul_comm _ p ▸ ⟨@quadTwist _ ψ _ ⟨hp⟩, by simp_all [quadTwist_apply, mul_right', to_jacobiSym]⟩
  grw [← @polya_vinogradov m ⟨hm⟩ (ψ m) (fun e ↦ ?_) X]
  · obtain k | k := (ψ m).even_or_odd <;> simp [← E, hm, k.eval_neg]
  obtain ⟨a, c, rfl, ha⟩ := m.sq_mul_squarefree
  obtain ⟨_ | _ | k, rfl⟩ | ⟨p, hp, ⟨b, rfl⟩, o⟩ := a.eq_two_pow_or_exists_odd_prime_and_dvd
  exacts [h ⟨c, by ring⟩, h' ⟨2 * c, by ring⟩, by grind [squarefree_pow_iff],
    @quadTwist_ne_one b (ψ b) p ⟨hp⟩ (by grind) (by grind [Nat.squarefree_mul_iff])
    ((@changeLevel_eq_one_iff _ _ _ _ ⟨hm⟩ _ (by simp [mul_comm])).1 (MulChar.ext fun u ↦ by
    have := congr($e (u.1.cast : ℤ))
    rw [changeLevel_eq_cast_of_dvd, ← intCast_cast, quadTwist_apply]
    simp_all [to_jacobiSym, ↓E, mul_right', sq, ← Int.cast_mul]; grind [trichotomy]))]

/-- Mean value estimate. For j ≤ 1, η > 0, t ≥ 1/T > 0, X ≤ T² and |c| ≤ 1: ∑_{1 ≤ v ≤ X} |∑_{n
≥ 1} c(n) (−v/n) g(nt)|² ≤ C T² t^{−1−2η}, with g = `gaussianMonomial` j and C = C(j, η). -/
lemma sum_sq_gaussianTheta_jacobiSym_le (hη : 0 < η) : ∃ C, ∀ T > (0 : ℝ), ∀ t ≥ T⁻¹,
    ∀ X : ℕ, X ≤ T ^ 2 → ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ 1) → ∑ v ∈ Ioc 0 X,
    ‖gaussianTheta j (fun n ↦ c n * J(-v | n)) t‖ ^ 2 ≤ C * (T ^ 2 * t ^ (-1 - 2 * η)) := by
  have b v m : ‖(J(v | m) : ℂ)‖ ≤ 1 := mod_cast by grind [trichotomy]
  have R l (hl : 0 < l) : ∃ C > 0, ∀ x > 0, |gaussianMonomial j x| ≤ C * x ^ (-l : ℝ) :=
    ⟨3 * l ^ l, by bound, fun x hx ↦ (norm_gaussianMonomial_le hx.le).trans (by
    have := log_le_self (div_pos hx hl).le
    simp (disch := positivity) [← log_le_log_iff, le_div_iff₀] at *; linarith)⟩
  obtain ⟨⟨A, _, hA⟩, ⟨B, _, hB⟩, Z, w⟩ := R (1 / 2 + η) (by bound), R (3 / 2 + η) (by bound),
    summable_pnat_iff_summable_nat.2 (summable_nat_rpow.2 (by bound : -1 - η / 2 < _)).norm,
    (fun v ↦ v.mul_norm (v.mul_norm v)) (summable_nat_rpow.2 (by bound : 2 * -(1 / 2 + η) < _)).norm
  -- the majorant: a sum over the triples `(a, b, u)` with `k n = a b²`, `m = a u²`, and a product
  refine ((summable_sum (s := {1, 2}) fun (k : ℕ+) _ ↦ ((w.hasSum.tsum_fiberwise fun (a, b, u) ↦
    ((b * (b * a) / k).toPNat', (a * u ^ 2).toPNat')).summable.mul_left (A ^ 2 * k ^ (1 / 2 + η))
    ).norm).add ((Z.mul_norm Z).mul_left ((2 * B) ^ 2 * rexp η / η))).imp
    fun K L T hT t h X hX c hc ↦ ?_
  have ht : 0 < t := by grw [h]; bound
  -- expand the square
  refine .trans (by simpa [mul_conj'] using mod_cast le_norm_self _) ((hasSum_sum
    (s := Ioc 0 X) fun v _ ↦ (fun s ↦ s.hasSum.mul s.hasSum.star (s.norm.mul_norm s.star.norm
    ).of_norm) (@summable_and_norm_gaussianTheta_le j _ t (fun n ↦ mul_one (1 : ℝ) ▸
    norm_mul_le_of_le (hc n) (b (-v) n)) ht).1).norm_le_of_bounded (L.mul_right _) fun (n, m) ↦ ?_)
  conv_lhs => simp [mul_right_comm _ _ (ofReal _), mul_mul_mul_comm _ (Int.cast _), ← Int.cast_mul,
    ← mul_right, ← mul_sum]
  -- if `k n m` is a square, `k = 1` or `2`, the trivial bound; else Pólya–Vinogradov
  obtain ⟨k, i, r, e⟩ | k := em (∃ k ∈ ({1, 2} : Finset ℕ+), IsSquare (k * (n * m) : ℕ))
  obtain ⟨g, p, u, o, s, f, rfl⟩ := exists_coprime' (by simp : 0 < gcd (k * n) r)
  obtain ⟨a, rfl⟩ : p ∣ g := (s.pow_right 2).dvd_mul_left.1 ⟨m, Nat.mul_left_cancel o (by grind)⟩
  map_tacs [grw +useKAbstract [hc, hc, hA, hA, norm_sum_le_of_le _ fun _ _ ↦ b .., show ∑ _ ∈ _, _ ≤
    T ^ 2 by simpa, ← norm_nonneg, ← single_le_sum _ i, ← le_norm_self, ← Summable.le_tsum (by apply
    w.subtype) ⟨(a, p, u), by simp [← f, show a * u ^ 2 = m from Nat.mul_left_cancel (mul_pos o o)
    (by grind)]⟩, ← mul_rpow, ← mul_rpow, rpow_mul, show _ ^ (2 : ℝ) = (k * (n * m) : ℝ) by
    rify at e; simp; grind]; (simp at k; grw +useKAbstract [hc, hc, hB, hB,
    norm_sum_jacobiSym_le _ k.1
    k.2, show 1 + _ = (rexp 1 * (n * m)).log by simp, log_le_rpow_div (ε := η / 2), ← sum_nonneg])]
  all_goals simp (disch := positivity) [← log_le_log_iff, mul_nonneg] <;>
    linarith [T.log_inv, log_le_log (by bound) h]

/-- For j ≤ 1, η > 0, T > 0, X ≤ T² and |c| ≤ 1: ∑_{1 ≤ v ≤ X} ∫_{1/T}^∞ |∑_{n ≥ 1} c(n) (−v/n)
g(nt)| dt/√t ≤ C T^{2+η}, with g = `gaussianMonomial` j and C = C(j, η). -/
lemma sum_thetaTailIntegral_le (hη : 0 < η) : ∃ C, ∀ T > (0 : ℝ), ∀ X : ℕ, X ≤ T ^ 2 → ∀ c : ℕ → ℂ,
    (∀ n, ‖c n‖ ≤ 1) → ∑ v ∈ Ioc 0 X, thetaTailIntegral j (fun n ↦ c n * J(-v | n)) T⁻¹ ≤ C * T ^
  (2 + η) := (sum_sq_gaussianTheta_jacobiSym_le j hη).imp' (√· / η) fun C H T hT X hX c hc ↦ by
  grw [← sum_filter_of_ne fun _ _ ↦ mt integral_undef, ← integral_finsetSum,
    setIntegral_mono_of_nonneg _ (fun t ht ↦ ?_) ((integrableOn_Ioi_rpow_of_lt (a := -1 + -η)
    ..).const_mul (√C * T ^ 2)), integral_const_mul, integral_Ioi_rpow_of_lt]
  any_goals have := (inv_pos.2 hT).trans ht; nth_grw 1 [filter_subset, ← sum_div,
    le_sqrt_of_sq_le sq_sum_le_card_mul_sum_sq, show #_ ≤ T ^ 2 by simpa, H T hT t ht.le]
  all_goals simp (disch := positivity) [inv_rpow, rpow_sub, rpow_neg, two_mul, rpow_add, field, *]
  intros; positivity

/-- Zero-density bound for quadratic twists: for ξ mod N, η > 0 and real y, only O(x^{1−η/2})
primes d ≤ x, d ≡ 7 mod 8, d ∤ N, have a zero of L(s, ξ·(·/d)) with Re s ≥ 1/2 + 9η, |Im s|
≤ y.

Known result: Zero density for quadratic twists by mean values over real characters. -/
lemma zero_density_quadTwist (hη : 0 < η) (y : ℝ) : (fun x : ℕ ↦ (#{d ∈ Ioc 0 x |
    ∃ _ : Fact d.Prime, d % 8 = 7 ∧ N.Coprime d ∧ ∃ s, 1 / 2 + 9 * η ≤ re s ∧ |im s| ≤ y ∧
    entireL (quadTwist ξ d) s = 0} : ℝ)) =O[atTop] fun x ↦ (x : ℝ) ^ (1 - η / 2) := by
  obtain ⟨M, f, ψ, _, e, rfl⟩ := exists_isPrimitive_changeLevel_eq ξ
  obtain ⟨j, hp⟩ : ∃ j : Fin 2, ψ (-1) = -(-1) ^ j.1 := by simpa using! ψ.even_or_odd.symm
  obtain ⟨⟨K, hK⟩, ⟨C, hC⟩, c, c0, hc⟩ := three_lines_bound_of_LFunction_eq_zero j,
    sum_thetaTailIntegral_le j hη, @exists_pos_le_norm_gaussianMellin j
    (.Icc 2⁻¹ 1 ×ℂ .Icc (-y) y) (isCompact_Icc.reProdIm isCompact_Icc) (by grind [mem_reProdIm])
  refine .of_bound (2 * C * M ^ (1 - η / 2)) ((((tendsto_rpow_atTop hη).eventually_gt_atTop
    (K / c ^ 2)).natCast_atTop.and (Ioi_mem_atTop 0)).mono fun x ⟨hx, x0⟩ ↦ ?_)
  obtain ⟨T, T0, hT⟩ : ∃ T > 0, T ^ 2 = (M * x : ℝ) := ⟨√_, by simpa, sq_sqrt (by simp)⟩
  have hX : x ≤ T ^ 2 := by simp [succ_le_iff, *]
  rw [Real.norm_natCast, ← mul_le_mul_iff_left₀ (rpow_pos_of_pos T0 (2 * η)), ← nsmul_eq_mul,
    ← sum_const, sum_filter]
  refine .trans (sum_le_sum fun d hd ↦ ?_) ((sum_add_distrib.trans_le (add_le_add (hC T T0 x hX
    (ψ ·) (by simp)) (hC T T0 x hX _ (norm_mul_moebius_le_one ψ)))).trans_eq (by simp (disch :=
    bound) [mul_assoc, abs_of_nonneg, ← mul_rpow, ← hT, ← rpow_natCast_mul, ← rpow_add]; ring_nf))
  split <;> [obtain ⟨_, h8, co, s, s₀, s₁, z⟩ := ‹_›; positivity]
  contrapose! hx
  obtain ⟨h, r⟩ := co.of_dvd_left f, le_of_not_ge (entireL_ne_zero _ · z)
  have h1 ξ := quadTwist_ne_one ξ d (by omega) h
  simp [entireL, h1, show quadTwist (ψ.changeLevel f) d = (quadTwist ψ d).changeLevel (by gcongr) by
    simp [quadTwist, ← changeLevel_trans], LFunction_changeLevel,
    prod_euler_factor_ne_zero _ (by bound : s.re ≠ 0)] at z
  grw [hX, ← rpow_natCast_mul, le_div_comm₀, hc s ⟨⟨by bound, r⟩, abs_le.1 s₁⟩, hK hη _ (h1 ψ) (by
    simpa (disch := omega) [hp, legendreSym.at_neg_one, ↓χ₄_nat_three_mod_four] using
    quadTwist_apply ψ d (-1)) T0 (by simp [hT, mem_Ioc.1 hd])] <;> try bound
  -- reciprocity and `(2/d) = 1` give `(n/d) = (-d/n)`
  · have E {n : ℕ} (h : n ≠ 0) : quadTwist ψ d n = ψ n * J(-d | n) := by
      let ⟨k, m, hm, e⟩ := exists_eq_two_pow_mul_odd h
      simpa [hm.pos.ne', mul_left, pow_left, at_two, qrSign, mul_right', pow_right, mod_left (-d) 2,
        *, Int.odd_iff.1, jacobiSym.neg, to_jacobiSym, quadratic_reciprocity' hm, ← natCast_mod,
        odd_iff, (by omega : d % 2 = 1 ∧ d % 4 = 3)] using quadTwist_apply ψ d n
    simpa [thetaTailIntegral, gaussianTheta, E, mul_right_comm] using hx.le
  -- the twist of a primitive character by the Legendre symbol of a new prime is primitive
  clear * - e h h1
  have H B := (conductor_mul_dvd_lcm_conductor (quadTwist ψ d) B⁻¹).trans (Nat.lcm_dvd_mul ..)
  obtain := H (quadTwist 1 d), H (ψ.changeLevel ⟨d, rfl⟩), h1 1,
    (@quadTwist 1 1 d _).conductor_dvd_level, (quadTwist ψ d).conductor_dvd_level.antisymm
  simp_all [quadTwist, dvd_prime Fact.out, mul_comm, h.dvd_mul_left, eq_one_iff_conductor_eq_one,
    h.symm.dvd_mul_left, conductor_inv, h.mul_dvd_of_dvd_of_dvd, conductor_changeLevel, IsPrimitive]

/-- Let β > 1/2, y real, and a a unit mod N whose primes are ≡ 7 mod 8 and prime to N. For some
prime d ≡ a, no L̃(s, ξ·(·/d)), ξ mod N, vanishes on re s ≥ β, |im s| ≤ y; L̃ is `entireL`.

Known result: Zero density for quadratic twists by mean values over real characters. -/
lemma exists_entireL_quadTwist_ne_zero {β} y {a : ZMod N} (hβ : 1 / 2 < β) (ha : IsUnit a) (H :
  ∀ d : Primes, d = a → d.1 % 8 = 7 ∧ N.Coprime d) : ∃ d : Primes, d = a ∧ ∀ ξ s,
  β ≤ re s → |im s| ≤ y → entireL (@quadTwist
  N ξ d _) s ≠ 0 := (exists_pos_mul_lt (lt_min one_pos (sub_pos.2 hβ)) 9).elim fun η ⟨hη, h⟩ ↦ by
  by_contra!
  refine not_summable_residueClass_prime_div ha ((LSeriesSummable_logMul_of_lt_re (s := 1)
    ((LSeriesSummable_of_sum_norm_bigO (s := 1 - η / 2 / 2) (f := fun n ↦ ite (n.Prime ∧ n = a) 1 0)
    (.trans (.of_norm_le fun x ↦ ?_) (.fun_sum (s := ⊤) fun ξ _ ↦ @zero_density_quadTwist N _ ξ _ hη
    y)) (by grind) (by simpa)).abscissaOfAbsConv_le.trans_lt (mod_cast by simpa))
    ).norm.of_norm_bounded (by simp +contextual [Set.indicator, term, apply_ite, ite_and,
    ← natCast_log, vonMangoldt_apply_prime]))
  simp [apply_ite norm, ← cast_sum]
  grw [← card_biUnion_le, card_le_card]
  simp_all [Primes, subset_iff]; grind
