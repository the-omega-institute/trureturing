import GRH.New.TwistedHecke.InterlacingCone
import GRH.New.TwistedHecke.FrobeniusFactors
import GRH.Lib.LocalGL.Green.CuspidalAtScalars
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Dimension bounds mod p from flags and a cone volume. For the elementary divisor bound, counting
flags against the volume of a cyclic interlacing cone shows that, mod p, forms whose exponents
nearly obey the Frobenius inequalities in all Levi frames fill at most about one part in the Hecke
operator's degree, and that forms its scaling makes divisible in all frames are rare. Volumes of
interlacing regions, Frobenius amplification and counting by leading terms along flags are known.
Related work: Forrester–Zhang, Corank-1 projections and the randomised Horn problem, 2021 (after
Dixon, 1905; Anderson, 1991); Bombieri, Counting points on curves over finite fields, Sém. Bourbaki
430, 1973; Okounkov, Brunn–Minkowski inequality for multiplicities, 1996.

This file: Flag count; amplification bounds dimension of conditioned forms by flags times lattice
points. Parahoric index times dim `TwistingData.excessCond` is at most (1+κ)m^N; size conditions.
Forms deep in all frames are rare: their mean depth is small. -/

open Module Nat Subgroup Filter Finset Finsupp Fintype Matrix MeasureTheory MvPolynomial Real
  MeasureTheory.Measure

variable {N k W K} [NeZero N] [CommRing W] [IsLocalRing W] [Field K] (T :
  TwistingData N W K) {a a' : Fin k}

instance [Finite (IsLocalRing.ResidueField W)] (τ) :
    (@parahoric k W _ _ τ).FiniteIndex := finiteIndex_of_le (ker_le_comap ..)

/-- For a finite field K with q elements, the index of the lower triangular subgroup in GL_k(K),
the number of full flags, is at most ∏_{l=1}^{k} (q^l − 1)/(q − 1). -/
lemma index_borel_le [Finite K] : (parabolic (R := K) (OrderDual.toDual ∘ @Fin.val k)).index ≤ ∏ l :
    Fin k, ((Nat.card K : ℝ) ^ (l.1 + 1) - 1) / (Nat.card K - 1) := by
  set A := @parabolic ..
  simpa [card_GL_eq_prod, Nat.card_pi, Nat.card_units, prod_range, Finite.one_lt_card,
    prod_pow_eq_pow_sum,
    field] using mono_cast (α := ℝ) (A.index_mul_card.le.trans' (mul_le_mul_left _
    (card_le_card_of_injective (fun x : ∀ i, Kˣ × (Set.Iio i → K) ↦ ⟨.mkOfDetNeZero (of fun i j ↦
    ite _ 0 (dite _ ((x i).2 ⟨j, ·⟩) fun _ ↦ (x i).1)) (by simp +contextual [BlockTriangular,
    det_of_isLowerTriangular, univ.prod_eq_zero_iff]), fun _ _ ↦ (ite_eq_left ·)⟩) fun x y h ↦ by
    ext i j <;> [simpa using congr($h.1 i i); simpa [lt_asymm, j.2.out] using congr($h.1 i j)])))

variable (a) in
/-- The real vectors β whose excess `TwistingData.excessWeight` i b (b+1) is, for all letters i, at
most h if b + 1 = a and at most 0 otherwise. -/
def TwistingData.excessCone (h : ℝ) :=
  {β | ∀ i (b b' : Fin k), b.1 + 1 = b' → T.excessWeight i b b' ⬝ᵥ β ≤ ite (b' = a) h 0}

/-- For K of characteristic p, a' = a + 1: dim `TwistingData.excessCond` n a a' 0 h ≤ [L : ℐ ∩
L]·vol(`TwistingData.excessCone` a' (h + N(k+1)) ∩ Σ), L the block diagonal group (blocks a', k −
a'), ℐ the lower Iwahori subgroup, Σ = `slab` of degrees in [n+k, n+k+1]. -/
lemma TwistingData.finrank_excessCond_le_volume [CharP K T.p] (ha : a.1 + 1 = a') n h :
    finrank K (T.excessCond n a a' ⊥ h) ≤ (parahoric W (↑)).relIndex (levi W (twoBlock k a')) *
  volume.real (T.excessCone a' (h + N * (k + 1)) ∩ slab k fun _ ↦ n + k + 1) := by
  -- the set is convex, so its points over `m ^ (k N)` tend to its volume; take `m = q ^ t`
  refine ge_of_tendsto_of_frequently (.const_mul _ (tendsto_card_div_pow_atTop_volume _ ?B (by
    unfold excessCone slab dotProduct; measurability) (Convex.addHaar_frontier _
    (by exact fun _ ⟨X, _, A⟩
    _ ⟨Y, _, B⟩ _ _ s t e ↦ ⟨fun _ _ _ _ ↦ by simp; grw [X .., Y ..] <;> simp [↓← add_mul, *],
    by positivity, fun j ↦ by simpa [univ.mul_sum] using convex_Icc _ _ (A j) (B j) s t e⟩))))
    (frequently_atTop'.2 fun t ↦ let m := T.q ^ t; ⟨m, t.lt_pow_self (mod_cast T.one_lt_q), ?_⟩)
  apply isBounded_inter_slab
  obtain ⟨_, _, p0, R, hR, h1⟩ := T.finite_residueField, Fact.mk T.prime, CharP.cast_eq_zero K _,
    ((parahoric W (↑)).subgroupOf (levi W (twoBlock k a'))).exists_isComplement_right 1
  set Λ := @Inter.inter ..
  obtain ⟨m1, _, _⟩ := NeZero.pos m, hR.finite_right.fintype, ((ZSpan.setFinite_inter _ ?B).subset
    (inf_le_inf_left _ (ZSpan.smul _ (NeZero.ne _)).le) : Λ.Finite).fintype
  field_simp
  norm_cast
  -- `p F = ∑ F_u (x ^ m) x ^ γ u`, `γ u ≡ u` modulo `m` of degree in `[k m, (k + 1) m)`
  let γ (u : _ × ZMod N → Fin m) := equivFunOnFinite.symm fun x ↦
    u x + m * ite (x.1 = a) (k - (∑ b, (u (b, x.2)).1) / m) 0
  let p := ∑ u, .mulRight K (monomial (γ u) 1) ∘ₗ (expand m).toLinearMap ∘ₗ polyOfCoeffs ∘ₗ
    (T.excessCond n a a' ⊥ h).subtype ∘ₗ .proj u
  -- `p F` is determined by its coefficients at these exponents, one translate per flag
  convert (LinearMap.pi fun x : R × Λ ↦ lcoeff K (equivFunOnFinite.symm (⌊x.2.1 · * m⌋₊)) ∘ₗ
    (T.polyAction x.1).toLinearMap ∘ₗ p).finrank_le_finrank_of_injective (.of_ker _ fun F f0 ↦ ?_)
  iterate 2 simp [relIndex, ← hR.card_right, mul_comm]
  ext u β; by_contra
  -- a monomial of least weight among the translates
  let w (x : Fin k × _) : ℝ := ite (T.isEven x.2) x.1 (-x.1)
  have ⟨⟨x, α⟩, hα, H⟩ := (univ.sigma fun x : R ↦ (T.polyAction x (p F)).support).exists_min_image
    (weight w ·.2) ⟨⟨⟨1, h1⟩, m • exponentOf β + γ u⟩, by
    simp [p, polyOfCoeffs, coeff_sum]
    rw [Fintype.sum_eq_single u fun v n ↦ Finset.sum_eq_zero fun _ _ ↦ ite_eq_right fun e ↦ n (by
    ext x; simpa [γ, mod_eq_of_lt, -mul_ite] using congr($e x % m))]; simpa [m1.ne']⟩
  refine absurd (congrFun f0 ⟨x, (α · / m), ?_, BoxIntegral.unitPartition.mem_smul_span_iff.2
    (⟨α ·, by simp [field]⟩)⟩) (by simpa using hα); clear f0
  -- its exponent is `m δ + ε`, with `δ` in a translate of some `F_u`, `ε` of the degrees of `γ u`
  obtain ⟨u, δ, ⟨ε, ⟨⟩⟩, hu, hv⟩ := by
    simp [p, ← AlgHom.mul_apply, (algHom_ext
      (by simp [m, ↓← pow_mul, polyAction_X, sum_pow_char_pow, mul_pow, ← C_pow, letterMatrix,
      ← (by simpa [← pow_mul, p0] using T.frobenius_pow_congr (N * t))]) : Commute (T.polyAction _)
      (expand m)), (expand m).mul_apply, polyAction_polyOfCoeffs, monomial_eq, polyAction_X] at hα
    simp [coeff_sum, polyOfCoeffs, univ.sum_mul, ← sum_prod_type'] at hα
    simpa [coeff_monomial_mul', le_iff_exists_add] using exists_ne_zero_of_sum_ne_zero hα
  have he s : ∑ b, ε (b, s) ∈ Set.Icc (m * k) (m * k + m) := by
    apply IsWeightedHomogeneous.prod _ _ _ fun j _ ↦ .pow (.sum _ _ (ite (j.2 = s) 1 0) fun b _ ↦
      (isWeightedHomogeneous_X K (if ·.2 = s then 1 else 0) (b, _)).C_mul (T.letterMatrix _ x b _))
      _ at hv
    simp [γ, weight_eq_sum, sum_prod_type, Nat.mul_sub] at hv
    grind [(by grw [Fin.is_le']; simp : ∑ b, (u (b, s)).1 ≤ k * m), mul_div_self_eq_mod_sub_self,
      mod_lt (∑ b, (u (b, s)).1) m1]
  refine ⟨fun i b b' e ↦ ?_, fun _ ↦ by positivity, fun s ↦ by simp [← univ.mul_sum, exponentOf,
    field, ← cast_sum, ← degree_eq_sum, Monomials.degree_eq, ← sum_div]; norm_cast; grind [he s]⟩
  simp_rw [dotProduct, mul_div, ← sum_div, ← nsmul_eq_mul', ← weight_eq_sum, field, mul_ite_zero]
  split
  grw [map_add, map_nsmul, (by omega : b = a), ‹b' = _›, not_lt.1 (hu <| (F u).2 _ x.1.2 δ ⟨i, ·⟩),
    weight_eq_sum, T.excessWeight_mem_Icc.2, ← univ.sum_smul, sum_prod_type_right,
    (he _).2]; simp [field]
  -- the root lemma at the other roots
  apply T.root_lemma i _ _ w 0 (fun g hg ↦ (hR.2 (⟨g, hg⟩⁻¹ * x)).elim fun b hb ↦
    Set.mem_of_eq_of_mem (by simpa using congr(T.polyAction ($hb.symm).1 (p F)))
    (aeval_sub_mem_of_gaussFiltration _ _ (mem_adicFiltration_of_nonpos <| by
    simpa using H ⟨_, ·⟩) fun y ↦ by simpa [polyAction_X, C_mul_X_eq_monomial] using
    (sum_mem fun i _ ↦ monomial_mem_gaussFiltration (mem_adicFiltration_of_nonpos (by
    unfold w; split <;> simpa [weight_single, *] using (T.p_dvd_letterMatrix_of_mem_parahoric y.2
      b.1.2 i _).mt)))).1) <;> grind [w_sq, dvd_def, twoBlock, rootVar, congr(($e : ℝ))]

/-- For β = `permStep` ν (signs by the parity of the letter, trivial permutations), the excess
`TwistingData.excessWeight` i a a' of β equals (1 − 1/q)·(β(u) − (ν(a,i) − ν(a',i))), where
u = `TwistingData.rootVar` a a' i. -/
lemma TwistingData.excessWeight_dotProduct_permStep i ν :
  T.excessWeight i a a' ⬝ᵥ permStep T.isEven T.P 1 ν = (1 - 1 / T.q) *
  (permStep T.isEven T.P 1 ν (T.rootVar a a' i) - (ν (a, i) - ν (a', i))) := by
  let F s := T.P ^ (1 + (s - i).val) * (ν (a, s + 1) - ν (a', s + 1)) / T.q
  rw [dotProduct, sum_prod_type_right, ← add_sub_cancel_right (∑ _, _), ← sum_add_distrib,
    ← (Equiv.subRight 1).sum_comp F, ← sum_sub_distrib, Fintype.sum_eq_single i] <;> intros <;>
    by_cases T.isEven ‹_› <;> simp [F, excessWeight, ↓one_add_val_sub_one_sub, rootVar,
    division_def, sub_mul, *] <;> field [T.prime.ne_zero]

/-- For a' = a + 1 there is a vector σ in `TwistingData.excessCone` a' (−1) with all coordinates in
[0, P^{3a'}]. -/
lemma TwistingData.exists_mem_excessCone_mem_Icc (ha : a.1 + 1 = a') :
    ∃ σ ∈ T.excessCone a' (-1), σ ∈ Set.Icc 0 fun _ ↦ (T.P ^ (3 * a'.1) : ℝ) := by
  obtain ⟨h5, hq, e⟩ := T.five_le_P, le_self_pow (NeZero.ne N) T.P,
    @T.excessWeight_dotProduct_permStep _ k
  rify at h5 hq e ⊢
  generalize (_ ^ T.o₀ : ℝ) = P at *
  let u b := ite (b ≤ a) (P ^ (2 * (a.1 - b)) * 2) 0
  have s b : (P ^ 2 - 1) * u b ∈ Set.Icc 0 (P ^ (3 * a'.1)) := by
    simp [u]; split <;> constructor <;> try bound
    grw [sub_le_self, (by bound : 2 ≤ P), ← pow_succ, ← pow_add, pow_le_pow_right₀] <;> grind
  refine ⟨permStep T.isEven P 1 fun x ↦ ite (T.isEven x.2) 1 P * u x.1, fun i b b' _ ↦ ?_,
    forall_and.1 fun (b', i) ↦ ?_⟩ <;> by_cases T.isEven i <;> simp [T.isEven_succ, *, field]
  iterate 2 rw [show u b = P ^ 2 * u b' + ite (b' = a') 2 0 by by_cases b = a <;> simp [u, *, ←
    mul_assoc, ← pow_add] <;> grind]; split <;> nlinarith [(s b').1, (by bound : P ≤ P * P ^ N)]
  all_goals grind [s b']

/-- For d ≤ D, the set of y ≥ 0 in ℝ^{n+1} with coordinate sum in [d − 1, d] has volume at most
|D^n/n!|. -/
lemma volume_sum_mem_Icc_le {n} {d D : ℝ} (hd : d ≤ D) : volume
    {y : Fin n.succ → ℝ | (∀ b, 0 ≤ y b) ∧ univ.sum y ∈ Set.Icc (d - 1) d} ≤ ‖D ^ n / n !‖ₑ := by
  cases n
  grw [measure_mono, volume_pi_pi ![Set.Icc (d - 1) d]] <;> simp [Set.pi]
  grw [← (volume_preserving_piFinSuccAbove _ 0).symm.measure_preimage_equiv, volume_eq_prod,
    prod_apply_le (by measurability), ← setLIntegral_eq_of_support_subset (s := .uIcc D 0) fun x
    h ↦ (nonempty_of_measure_ne_zero h).elim _, ← setLIntegral_congr uIoc_ae_eq_interval,
    lintegral_mono ((measure_mono _).trans <| volume_sum_mem_Icc_le <| sub_le_sub_right hd ·),
    ← ofReal_integral_norm_eq_lintegral_enorm (Continuous.integrableOn_uIoc (by fun_prop))] <;> simp
    [← ofReal_norm, integral_div, abs_sub_comm D, integral_pow_abs_sub_uIoc,
    @Fin.forall_fin_succ (succ _), factorial] <;> grind [Finset.sum_nonneg, Set.mem_uIcc]

/-- Size conditions, with c = 2k(k+1)dN²+2: 0 < 2r ≤ k, κ ≤ 1 ≤ y, 2ℓ = N, Nnk(ℓ+2)+n+k < P^ℓ,
6c+2 ≤ y, 2(N+2)k/y ≤ κ, (y+N(k+1))kP^{3r}+k+2 ≤ n/y, Nn(P^{−2r}+r²/(kP)) ≤ z. -/
def HeckeSizes (P d N k n r ℓ : ℕ) (κ y z : ℝ) := 0 < r ∧ 2 * r ≤ k ∧ κ ≤ 1 ∧ 1 ≤ y ∧ ℓ + ℓ = N ∧
  N * (n * (k * (ℓ + 2))) + n + k < P ^ ℓ ∧ 6 * (2 * ((k + k ^ 2) * (d * N) * N) + 2 :) + 2 ≤
  y ∧ 2 * (N + 2) * k / y ≤ κ ∧ (y + N * (k + 1)) * k * P ^ (3 * r) + k + 2 ≤ y⁻¹ * n ∧ N * n *
  (1 / P ^ (2 * r) + r ^ 2 / (k * P)) ≤ z

/-- Let K have characteristic p, a' = a + 1, and assume `HeckeSizes` with r = a', y = h. Then
[GL_k(W) : 𝒫]·dim `TwistingData.excessCond` n a a' ⊥ h ≤ (1 + κ)·m^N, where 𝒫 is the parahoric of
`twoBlock` a' and m counts degree-n monomials in k variables.

Dimension bounds mod p from flags and a cone volume. -/
lemma TwistingData.index_mul_finrank_excessCond_le [CharP K T.p] (ha : a.1 + 1 = a') {n ℓ h κ z}
  (big : HeckeSizes T.P T.o₀ N k n a' ℓ κ h z) : (parahoric W (twoBlock k a')).index * finrank K
  (T.excessCond n a a' ⊥ h) ≤ (1 + κ) * Fintype.card (Monomials (Fin k) n) ^ N := by
  obtain ⟨_ | k, ⟨σ, σ1, _, σ2⟩, _, -, -, _, _, _⟩ := k, T.exists_mem_excessCone_mem_Icc ha,
    T.finite_residueField, big
  lia
  let τ := (h + N * (k + 2)) • σ
  -- shift by `τ` into `excessCone a' 0` ∩ `slab`; cosets of `𝒫` times flags of the Levi subgroup
  -- are at most all flags, and flags times the volume of `excessCone a' 0` ∩ `slab` is the volume
  -- of `slab`
  grw [T.finrank_excessCond_le_volume ha, Measure.real, (measure_mono _).trans_eq
    (measure_preimage_add _ τ _), ← Measure.real, relIndex_le_of_le_right, mul_left_comm,
    ← mul_assoc, ← cast_mul, relIndex_mul_index, parahoric, index_comap, relIndex_le_of_le_right,
    relIndex_top_right, index_borel_le, T.card_residueField, cast_pow, @prod_mul_volume_inter_slab _
    _ _ T.isEven _ T.one_lt_P (n + k + 2 + ∑ b, τ ⟨b, ·⟩) (T.excessCone a' 0) (by simp [excessCone,
    pieriCone, excessWeight_dotProduct_permStep, ← le_div_iff₀', inv_lt_one_iff₀,
    ↓one_lt_q, -cast_pow, -cast_npow]), Measure.real, (measure_mono (by exact fun β g j _ ↦
    ⟨(g.1 ⟨·, j⟩), g.2 j⟩)).trans
    (((measurePreserving_flip.comp measurePreserving_curry).measure_preimage_le _).trans
    ((volume_pi_pi _).trans_le (prod_le_pow_card _ _ _ fun j _ ↦ volume_sum_mem_Icc_le (show _ + _
    ≤ h⁻¹.exp * n by simp [τ]; grw [σ2 _, ← add_one_le_exp]; simp; grind))))] <;> try simp [
    relIndex, card_finsuppAntidiag_nat_eq_choose, mul_pow, mul_div_assoc, -enorm_mul, ← exp_nat_mul,
    (isBounded_inter_slab (T := ZMod N) ..).measure_lt_top.ne]
  grw [← choose_symm_add, ← pow_le_choose, ← le_add_right, exp_bound' (n := 1)] <;> (try gcongr) <;>
    simp [field] at * <;> nlinarith
  -- the Levi subgroup and the Iwahori subgroup lie in `𝒫`
  iterate 2 intro; simp [parahoric, parabolic, levi, BlockTriangular]; grind [twoBlock,
    not_isUnit_zero]
  -- the shift by `τ`
  exact ⟨fun β g _ _ _ _ ↦ by simp [τ]; grw [g.1 .., σ1 ..] <;> bound, fun β ⟨_, _, g⟩ ↦
    ⟨by positivity, (by simp; grind [g ·])⟩⟩

/-- Let K have characteristic p and assume `HeckeSizes`. Then for every M, ∑_{d<M} dim
V_d ≤ (1 + z)·m^N, where V_d = `TwistingData.deepForms` n r d and m is the number of monomials of
degree n in k variables.

Dimension bounds mod p from flags and a cone volume. -/
lemma TwistingData.sum_finrank_deepForms_le [CharP K T.p] {n r ℓ κ h z} (big :
  HeckeSizes T.P T.o₀ N k n r ℓ κ h z) M : (∑ d ∈ range M, finrank K (T.deepForms k n r d) : ℝ) ≤
  (1 + z) * Fintype.card (Monomials (Fin k) n) ^ N := by
  -- `3 r < ℓ`, as `P ^ (3 r) ≤ n < P ^ ℓ` and powers of `P` increase
  obtain ⟨_ | k, _, _, hk, -, hy, _, _, -, -, h2, h3⟩ :=
    k, (pow_right_mono₀ T.one_lt_P.le).map_sup ℓ (3 * r), big; lia
  grw [← hy, inv_one] at h2
  -- a form in `V_d` is determined by its coefficients at the monomials of cost at least `d`
  grw [((LinearMap.funLeft K K Subtype.val).domRestrict _).finrank_le_finrank_of_injective
    (.of_ker _ fun F e ↦ F.ext (Not.imp_symm (T.exists_le_weight_of_mem_deepForms hk
    (by norm_cast at *; lia) F.2) fun ⟨β, h, H⟩ ↦ h congr($e ⟨β, lt_succ_of_le (le_floor H)⟩)))]
  -- count each monomial for the `d` up to its cost
  simp [Fintype.card_subtype, ← sum_boole, (range M).sum_comm, ↓← mem_range, weight_eq_sum]
  -- take the mean, by the symmetry of the rows: average over the permutations `a ↦ b - a`
  grw [min_le_right, floor_le (by positivity), sum_add_distrib, ← h3, le_expect univ_nonempty
    fun b ↦ imp_intro ((Equiv.Perm.subtypePerm (equivCongrLeft (.subLeft b)).symm (by
    simp [↓mem_finsuppAntidiag'])).bijective.comp_left.sum_comp _).ge]
  simp [↓expect_sum_comm, Finset.expect_eq_sum_div_card, ← univ.sum_mul, *, ← univ.mul_sum,
    exponentOf, field, ↓sum_prod_type, ← cast_sum, sum_deepIndicator, apply_ite, sum_ite,
    Fin.card_filter_val_lt,
    ← degree_eq_sum, Monomials.degree_eq, ← translate_apply, sum_translate, div_eq_mul_inv]
  grw [card_finset_fin_le, cast_succ, cast_div_le]
  ring
  bound
