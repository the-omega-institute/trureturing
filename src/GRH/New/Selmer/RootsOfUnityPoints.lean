import GRH.Lib.General.NumberTheory.Valuation
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Roots of unity keeping polynomial valuations low, in any degree. One polynomial in the values of
a twist on tame inertia bounds the twisted Selmer length at all points and is sharp at a chosen one,
and finitely many integral polynomials of any degree that are little divisible at points near 1 stay
so at powers of one tuple of ℓ-power roots of unity, which then defines the twist. A degree-free
bound at some ℓ-power root of unity for one element is known and the determinant step is base change
of Fitting ideals. Related work: Kriz–Nordentoft, Horizontal p-adic L-functions, 2023; Serban, An
infinitesimal p-adic multiplicative Manin–Mumford conjecture, 2018; Kurihara, The structure of
Selmer groups of elliptic curves and modular symbols, 2014.

This file: ℓ-power roots of unity keep valuations of polynomials of any degree low. -/
seal Finset.univ Finset.sum Finset.prod

open Polynomial Filter Finset Real IsUltrametricDist NeZero Function Fint CoeffRing
variable {ℓ} [p : ThePrime ℓ] {κ : Type}

/-- Fix 0 < r < 1 with |ℓ| < r^{ℓ−1} and finitely many y_k > 0. For large N, then large O:
polynomials F_k over O of any degree with Gauss norm of radius r at least y_k have all
|F_k(ζ − 1)| ≥ r y_k for one ζ ∈ O, ζ^{ℓ^N} = 1. -/
lemma exists_root_of_unity_eval_large [Fintype κ] (y : κ → ℝ) {r} (hy :
  ∀ k, 0 < y k) (h0 : 0 < r) (h1 : r < 1)
  (e : ‖(ℓ : PadicAlgCl ℓ)‖ < r ^ (ℓ - 1)) : ∀ᶠ N in atTop, ∀ᶠ O : CoeffRing ℓ in atTop, ∀ F : κ →
  O.1[X], (∀ k, ∃ i, y k ≤ ‖((F k).coeff i).1‖ * r ^ i) → ∃ ζ : ↑O, ζ ^ ℓ ^ N = 1 ∧ ∀ k, r * y k ≤
  ‖((F k).eval (ζ - 1)).1‖ := (exists_pow_lt_of_lt_one (by simp [ne] : 0 < ‖(ℓ : PadicAlgCl ℓ)‖)
  h1).rec fun a ha ↦ ((tendsto_sum_range_one_div_nat_succ_atTop.atTop_mul_const_of_neg (log_neg
  h0 h1)).eventually_lt_atBot _).mono fun N J ↦ .mono (.all fun j : range N ↦
  eventually_primitiveRoot (ℓ ^ j.1.succ)) fun O η F h ↦ by
  contrapose! J
  let ρ j := r ^ (↑(ℓ ^ j) : ℝ)⁻¹
  let ⟨m, ρ1⟩ : Monotone ρ ∧ ∀ j, ρ j ≤ 1 := by
    simp [ρ, Monotone, rpow_le_one_iff_of_pos, *]; bound [pos ℓ]
  let g j := (@gaussNorm_isAbsoluteValue (ρ j) O _ (.comp (NormedField.toAbsoluteValue _)
    O.1.subtype_injective) isNonarchimedean_norm (by bound)).toAbsoluteValue
  have U {j F x} : g j F ≤ x ↔ ∀ i, ‖(F.coeff i).1‖ * _ ≤ x := ⟨swap (F.le_gaussNorm _
    (by bound) · |>.trans), (exists_eq_gaussNorm ..).choose_spec.trans_le ∘ (· _)⟩
  have G k t : y k ≤ g t (F k) := (h k).rec (by grw [← U.1 le_rfl ·, ← m bot_le]; simp [ρ])
  choose Q hQ using (dvd_prod_of_mem F <| mem_univ ·)
  have Z t : 0 < ∏ k, g t (F k) := prod_pos (by grind)
  grw [sum_mul, ← sum_le_sum fun j _ ↦ ?_, sum_range_sub' fun j ↦ a * (∏ k, g j (F k)).log, ← G,
    U.2 (by bound)] <;> simp [prod_pos, le_of_lt, *]
  choose η hη using η ⟨j, ‹_›⟩
  choose k u using fun i ↦ J (η ^ i) (by grind [hη.pow_eq_one_iff_dvd, pow_dvd_pow, =_ pow_mul])
  have W := congr(($(X_pow_sub_C_eq_prod hη one_le (one_pow _)).comp (X - C (-1))).derivative).symm
  choose S s using (range (ℓ ^ j.succ)).dvd_sum fun i hi ↦ prod_erase_mul _ (fun i ↦ X - C (η ^ i -
    1)) hi ▸ mul_dvd_mul_left _ ((sub_mul _ (F (k i)) _ ▸ (dvd_modByMonic_sub ..).mul_right
    (Q (k i))).trans (sub_dvd_pow_sub_pow _ _ (a * j.succ)))
  simp [-map_neg, -map_sub, -map_pow, Polynomial.prod_comp, sub_sub, ← map_add, ← hQ, mul_sub,
    derivative_prod_finset, derivative_pow, neg_add_eq_sub, ← sum_mul] at W s
  have K t (ht : j ≤ t) := (by
    have n : IsNonarchimedean (g t) := isNonarchimedean_gaussNorm _ isNonarchimedean_norm (by bound)
    have l b : g t (X - C b) = ‖b.1‖ ⊔ ρ t ∧ g t (C b) = ‖b.1‖ := ⟨eq_of_forall_ge_iff (by
      simp [U, ← Nat.and_forall_add_one, coeff_X]; bound [norm_nonneg b.1]), gaussNorm_C ..⟩
    have z i := (norm_pow_sub_one_le_norm_sub_one (norm_le_one η) i).trans
      ((lt_of_pow_lt_pow_left₀ _ (by bound) (by rwa [norm_zeta_sub_one_pow (by simpa),
      Nat.totient_prime_pow_succ p.out, pow_mul, rpow_inv_natCast_pow h0.le out])).le.trans (m ht))
    have V a b := congr(g t $s) ▸ n.add_eq_right_of_lt (map_neg_eq_map _)
      ((n.apply_sum_le_sup a).trans_lt b)
    simp [map_neg_eq_map, -map_neg, -map_sub, -map_natCast, ne, *] at V
    use (eq_inv_mul_iff_mul_eq₀ (by positivity)).2 (V fun _ _ ↦ by
      grw [ρ1, (u _).le, G, mul_assoc, ← map_mul, ← hQ, mul_pow, pow_mul, ha] <;> simp [*]))
  have V := log_le_log (by simp [ne, field, *]) ((@U j S _).2 (by grw [m j.le_succ, ← U]))
  simp [log_mul, rpow_def_of_pos, ρ, pow_add, field, ne_of_gt, ne, *] at V ⊢
  grind [nsmul_le_nsmul_left_of_nonpos (log_neg h0 h1).le p.out.two_le]

/-- Fix δ > 0, m, L, a, q and finitely many bounds B_k. For large N, then large O: given F_{k,d}
(1 ≤ d ≤ m) in ≤ q variables with valuation ≤ B_k at points u_{k,d}, ℓ ∣ (u − 1)^a coordinatewise,
and monic D_n of total degree ≤ L, some tuple ζ in O of ℓ^N-th roots of unity has
v(F_{k,d}(ζ^d)) ≤ δ + B_k and all v(D_n(ζ_j)) ≤ δ.

Roots of unity keeping polynomial valuations low, in any degree. -/
lemma exists_roots_of_unity_ellVal_le [Finite κ] {δ : NNReal} (hδ : 0 < δ) (m L a q : ℕ) (B : κ →
  NNReal) : ∀ᶠ N in atTop, ∀ᶠ O : CoeffRing ℓ in atTop, ∀ (σ T : Type) [Fintype σ] [Fintype T],
  Fintype.card σ ≤ q → ∀ (D : T → O.1[X]) (F : κ × Set.Icc 1 m → MvPolynomial σ _) (u : _ → _ → ↑O),
  (∀ n, (D n).Monic) → ∑ n, (D n).natDegree ≤ L → (∀ k j, ↑ℓ ∣ (u k j - 1) ^ a) → (∀ k,
  ellVal ((F k).eval (u k)).1 ≤ B k.1) → ∃ ζ : σ → ↑O, (∀ k, ellVal ((F k).eval (ζ · ^ k.2.1)).1 ≤
  ↑(δ + B k.1)) ∧ ∀ j, ζ j ^ ℓ ^ N = 1 ∧ ∀ n, ellVal ((D n).eval (ζ j)).1 ≤ δ := by
  choose r r0 e r1 using exists_pow_btwn (x := ‖(ℓ : PadicAlgCl ℓ)‖ ⊔ ℓ ^ (-δ.toReal)) (q + L + ℓ +
    m * a).succ_ne_zero (by simp [norm_p_lt_one, rpow_lt_one_iff, Fact.out, *]) one_pos
  simp [pow_lt_one_iff_of_nonneg r0.le] at r1
  have R n (h : n ≤ _ := by grind) := max_lt_iff.1 (e.trans_le (pow_le_pow_of_le_one r0.le r1.le h))
  refine .mono (.all fun n : Set.Iic q ↦ exists_root_of_unity_eval_large (Option.rec (r ^ L) fun k :
    κ × Set.Icc 1 m ↦ ℓ ^ (-B k.1 : ℝ) * r ^ n.1) (by rintro ⟨⟩ <;> bound [pos ℓ]) r0 r1 (R _).1)
    fun N Y ↦ .mono (.all Y) fun O Y σ T _ _ hq D F u hD hL hu hB ↦ (univ.induction_on (motive :=
    (fun T s ↦ ∃ ζ, (∀ k, ℓ ^ (-B k.1 : ℝ) * r ^ #s ≤ ‖((F k).eval (s.piecewise (ζ · ^ k.2.1) (u
    k))).1‖) ∧ ∀ j ∈ s, T ζ j) (_ : _ → Set σ)) ⟨1, by simp [← ellVal_le_iff, *]⟩ fun j s _ ⟨ζ, H,
    h⟩ ↦ ?_).imp fun ζ ↦
    .imp (by grw [← (R _).2.le]; simp [rpow_add, pos, ↓ellVal_le_iff]) (· · (by simp))
  have p d x y (h : x ^ d = (y j).1) G : (MvPolynomial.eval y G : ↑O).1 = aeval (x - 1)
    (G.aeval fun i ↦ ite (i = j) ((1 + X) ^ d) (C (y i)))
  apply G.induction_on <;> simp +contextual [*, apply_ite]
  choose z Z W using Y ⟨_, s.card_le_univ.trans hq⟩ (Option.rec (taylor 1 (univ.prod D)) _) (·.rec
    ⟨(univ.prod D).natDegree, by simp [leadingCoeff_prod, natDegree_prod_le, hL.trans',
    pow_le_pow_iff_right_of_lt_one₀, *]⟩ fun k ↦ (not_forall₂.1 (mt (pow_le_norm_aeval ((X ^ k.2.1 -
    C (u k j).1) ^ a) (O.1.val 1) r0.le) (by simpa [leadingCoeff_X_pow_sub_C k.2.2.1, norm_sub_rev]
    using ((dvd_iff_norm_le ..).1 (hu ..)).trans_lt (R _ (by grw [k.2.2.2]; lia)).1))).rec
    fun w ⟨hw, W⟩ ↦ (exists_norm_finsetSum_le ..).imp fun i h ↦ by
      simp [norm_sub_rev] at hw W ⊢
      grw [H, p k.2 w, aeval_eq_sum_range, h.2, O.1.smul_def] <;> simp [*]
      gcongr)
  have V n := ellVal_le_iff.2 <| ((dvd_iff_norm_le ..).1 (eval_dvd (dvd_prod_of_mem D
    (mem_univ n)))).trans' (by grw [(R L.succ).2, pow_succ', W none, taylor_eval_sub])
  refine ⟨update ζ j z, fun k ↦ ?_, by grind⟩
  simpa +contextual [pow_succ, mul_rotate' r, p k.2 z, piecewise, *] using
    (W k).trans congr(‖$(aeval_algebraMap_apply _ (z - 1) _)‖).ge
