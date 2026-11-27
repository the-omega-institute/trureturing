/- GID: D5/S3/Zeros/GRH/New/Curve/TightFrameExists
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Curve/TightFrameExists
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Curve.TightFrameExists. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/TightFrameExists.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Curve.PeriodDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Tight frames and an integral standard theta function (see New.Curve.FrameSections).

This file: For each prime p, tight frames of every large length with a vector v such that every
s₁·conj τ(v) is a p-adic unit, s₁ = `Parameters.periodFactor`. -/

open ComplexConjugate Finset Ideal NeZero Polynomial ZMod

variable {P : Parameters} {s} {p : ℕ} [Fact p.Prime] [ι : PadicPlace p]

lemma Parameters.coe_trace_eq_sum z : Algebra.trace P.K (P.E s) z = ∑ τ, Φ τ z := P.phi_algebraMap
  s 1 _ ▸ by simp [← phi_mul, trace_eq_sum_automorphisms, reindex_equiv (P.galOfPlace s)]

lemma Parameters.herm_mem_quadInt {y} x (h : finiteImage id x ∈ Ô (P.E s)) (k :
  finiteImage id y ∈ Ô _) : ∑ τ, Φ τ x * conj (Φ τ y) ∈ quadInt P.d :=
  .imp (by simp_all [coe_trace_eq_sum, Algebra.smul_def]) ((differentialIdeal_le_iff
  (K := P.K) (by simpa using mod_cast P.relDifferentGen_ne_zero s)).1
  (relDifferent_spec isPrimitiveRoot_zetaInt).2.1.ge ⟨x * star y, by
  simpa [Submodule.mem_span_singleton, -map_inv₀] using ⟨⟨_, algebraMap_mem_Ô.1 (by
  convert mul_mem (mem_Ô.2 (v_alpha_mul_relDifferentGen · |>.le))
    (mul_mem h (star_mem_Ô k)); simp [finiteImage, WeilData.α]
  grind [Units.mul_inv, star_mul, star_one])⟩, div_eq_of_eq_mul (by simp) rfl⟩, rfl⟩)

omit [PadicPlace p] in
/-- For φ : E → ℂ_p, the component of the idele α at the place induced by φ, read through φ, is
1/φ(P′(ζ)) (P the N₁-th cyclotomic polynomial) if that place divides (1 + √−d)/2, and 1
otherwise. -/
@[local simp] lemma Parameters.adeleExtension_alpha (φ : _ →+* ℂ_[p]) : adeleExtension φ (P.α s).1 =
  ite (P.c₀InE s ∈ (placeOfEmb φ).1)
  (φ (P.relDifferentGen s))⁻¹ 1 := by split <;> simp [α] <;> simp [adeleExtension, *]

/-- For every ring map ι : ℂ → ℂ_p and every place τ, |ι(s₁)|, s₁ = `Parameters.periodFactor`,
is the inverse of the absolute
value of the component of the idele α along the embedding x ↦ ι(τ(x̄)) of E into ℂ_p. -/
lemma Parameters.norm_iota_periodFactor τ : ‖ιₚ (P.periodFactor s)‖ = ‖adeleExtension
  (weightEmbedding ιₚ τ) (P.α s).1‖⁻¹ := by
  have A u := (isEquiv_placeOfEmb (weightEmbedding ιₚ 1)).eq_iff.2
    (@valuation_map_relDifferentGen P s (galOfPlaceInt u) (MulAction.injective _) _)
  rw [← pow_left_inj₀ _ _ (ne (Fintype.card (P.Φ s))), ← norm_pow, ← map_pow] <;> simp_all
    [periodFactor, div_pow, P.cmCurve.chowla_selberg.choose_spec, NNReal.eq_iff,
    WeilData.norm_map_chiFin, vacuumRoot, apply_ite, @starRingEnd_apply (P.E s), ← phi_mul,
    (show Φ · (P.c₀InE s).val = _ from phi_algebraMap ..)]

lemma Parameters.norm_periodFactor_mul_conj_le_one {y} (h :
  finiteImage id y ∈ Ô (P.E s)) τ : ‖ιₚ (P.periodFactor s * conj (Φ τ y))‖ ≤ 1 := by
  simpa [finiteImage, -adeleExtension_alpha, norm_iota_periodFactor τ, starRingEnd_apply y] using!
    norm_adeleExtension_le_one (weightEmbedding ιₚ _) h

variable (P s)

lemma Parameters.norm_iota_periodFactor_eq_one (h : ¬p ∣ P.N₁ s) : ‖ιₚ
  (P.periodFactor s)‖ = 1 := by simp [norm_iota_periodFactor 1, apply_ite, -RingHom.coe_comp,
  (norm_ringOfIntegers_le ..).eq_of_not_lt (h ∘ (FinPlace.natCast_mem_iff_dvd _
  (natCast_mem_placeOfEmb _)).1 ∘ mem_of_dvd _ relDifferentGen_dvd_N₁ ∘ (mem_placeOfEmb ..).2)]

/-- The powers ζ^i, 0 ≤ i < N₁, of the primitive N₁-th root of unity ζ in E, each taken k times,
form a tight frame of length kN₁ in the sense of `IsTightFrame`. -/
lemma Parameters.isTightFrame_zeta_pow k :
  IsTightFrame (fun i : Fin (N₁ P s) ↦ P.ζ s ^ i.1) (fun _ ↦ k) (k * P.N₁ s) :=
  ⟨fun _ ↦ mul_mem inv_α_mem (algebraMap_mem_Ô.2 ((zetaInt ..).2.pow _)), fun σ τ ↦ by
  split <;> simp [*, starRingEnd_apply, ← map_star_complex, -inv_pow, ← mul_pow, ↓← mul_sum,
    ← sum_range, isPrimitiveRoot_zeta.ne_zero out]
  erw [geom_sum_eq fun h ↦ ‹¬_›
    (Function.LeftInverse.injective mk_Φ congr($((isPrimitiveRoot_zeta.powerBasis P.K).algHom_ext
    (eq_of_mul_inv_eq_one h)).1))]; simp [mul_pow, ← map_pow, isPrimitiveRoot_zeta.1]⟩

/-- Let ζ be a primitive N-th root of unity in a domain R of characteristic 0, l a prime factor
of N = lr. Some M ≤ N, divisible by every prime factor of N but l, and some V dividing M in
R have Φ_N′(ζ)(ζ^r − 1)M = NV. -/
lemma Parameters.exists_cyclotomic_different_factor {R N} [CommRing R] [IsDomain R] [CharZero R] {ζ}
  (hζ : IsPrimitiveRoot ζ N) (l : N.primeFactors) : ∃ r, ∃ M ≤ N, N = l * r ∧ (∀ p ∈ N.primeFactors,
  p ∣ M ↔ p ≠ l) ∧ ∃ V, V ∣ ↑M ∧ (cyclotomic N R).derivative.eval ζ * (ζ ^ r - 1) * M = N * V := by
  have ⟨hl, ⟨r, e⟩, hN⟩ := N.mem_primeFactors.1 l.2
  obtain ⟨⟨q, hq⟩, a, M, hM, rfl⟩ := @X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd R _ r N
    (by simp_all [hl.one_lt, zero_lt_iff]), r.exists_eq_pow_mul_and_not_dvd (by lia) _ hl.ne_one
  have := by simpa [← expand_mul, expand_pow_cyclotomic hl, ← e, M.mul_comm, mul_assoc, hζ.1,
    derivative_expand, (hζ.isRoot_cyclotomic hN.bot_lt).eq_zero, pow_sub_one_mul hN,
    derivative_X_pow, -Nat.cast_mul] using congr(((expand R (l ^ a)
    $(cyclotomic_expand_eq_cyclotomic_mul hl hM R)).derivative.eval ζ, (derivative $hq).eval ζ * ζ))
  refine Dvd.elim ?_ (⟨_, M, by grw [e, ← hl.one_le]; lia, e, by grind [Nat.Prime.dvd_mul,
    Nat.prime_eq_prime_of_dvd_pow, Nat.prime_dvd_prime_iff_eq], ·, ⟨q.eval ζ * ζ,
    nsmul_right_injective hN (by grind)⟩, ·⟩)
  convert mul_dvd_mul_right ((dvd_of_mul_right_dvd (Dvd.intro_left _ this.1)).trans
    (mul_dvd_mul_left _ (eval_dvd (cyclotomic.dvd_X_pow_sub_one ..)))) _ <;> simp [e] <;> ring

/-- Tight frames: for m ≥ (dN₁)⁶(R + 1) and ι: ℂ → ℂ_p there is a finite tight frame (v_i) of length
m with multiplicities c_i ≥ R (`IsTightFrame`) in which, for some i, ι(s₁·conj τ(v_i)) is a p-adic
unit at every place τ; s₁ = `Parameters.periodFactor`. -/
lemma Parameters.exists_isTightFrame {m R} (hR : (P.d * P.N₁ s) ^ 6 * (R + 1) ≤ m) :
    ∃ I, ∃ (_ : Fintype I) (v c : I → _), IsTightFrame v c m ∧ (∀ i, R ≤ c i) ∧ ∃ i, ∀ τ, ‖ιₚ
    (P.periodFactor s * conj (Φ τ (v i : P.E s)))‖ = 1 := by
  obtain ⟨hϵ, hζ, h0, hG⟩ := P.c₀InE_mul_one_sub s, @isPrimitiveRoot_zetaInt P s, ne (P.N₁ s),
    P.isTightFrame_zeta_pow s 1
  set N := N₁ ..
  set n := _ / 4
  choose r M hN hr _ V hV _ using exists_cyclotomic_different_factor hζ
  have ⟨f, hf⟩ : N ∣ n ^ N := by grind [N.dvd_pow_self_iff, dvd_norm_c₀, lt_d]
  have ⟨z, hz, e, he⟩ : ∃ z < N, N ∣ n * z ^ 2 + z + 1 := (@Finite.surjective_of_injective
    (ZMod N) _ (fun y ↦ n * y ^ 2 + y) (fun a b h ↦ (IsNilpotent.isUnit_add_one (r := n *
    (a + b)) ⟨N, by simp [mul_pow, ← n.cast_pow, hf]⟩).mul_left_cancel (by linear_combination h))
    (-1)).elim (⟨_, val_lt ·, by simp [← natCast_eq_zero_iff, ·]⟩)
  let t := 1 - P.c₀InE s + n * z
  set c := ∑ l, (N + M l * (1 + 2 * n * (z + l * (M l * e)))) with E
  replace hR : R * (c + N) + N.pred * c.pred ≤
    m := by grw [← hR, c.pred_le, ← (by grind [lt_d] : n + 2 ≤ P.d),
    E.trans_le (by grw [hN, N.le_of_mem_primeFactors (coe_mem _),
    ← he, hz]), sum_const, univ_eq_attach, card_attach, card_le_card fun _ ↦ mem_Iic.2
    ∘ N.le_of_mem_primeFactors, N.card_Iic, N.pred_le]; cases N <;> lia
  have ⟨B, A, _⟩ := N.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le c _ ((N.coprime_of_dvd
    fun p _ _ ↦ by rw [← natCast_eq_zero_iff, Nat.cast_sum, Fintype.sum_eq_single ⟨p, by grind⟩] <;>
    grind [natCast_eq_zero_iff, dvd_norm_c₀]).dvd.trans (one_dvd _)) (le_tsub_of_add_le_left hR)
  let a := (P.zetaInt s ^ r ·)
  let u : (Σ l, Fin (r l) × Fin l × Fin l) → P.E s | ⟨l, ⟨j, _⟩, ⟨k, _⟩, i, _⟩ => P.zetaInt s ^ j *
    (0 ^ k * a l ^ i + t * M l / N * (a l ^ i - a l ^ k))
  refine ⟨_, inferInstance, Sum.elim u _, (cond ·.isLeft A B + R), ⟨Sum.rec (fun ⟨l, j, k, i⟩ ↦
    mem_Ô.2 fun v ↦ ?m) hG.1, fun σ τ ↦ ?_⟩, by simp, by_cases (⟨.inr 0, ·⟩) fun h ↦ ?_⟩
  · simp [← mul_sum, by simpa using hG.2]
    rw [Fintype.sum_sigma, sum_congr rfl fun l ↦ ?_, ← ite_sum_zero (σ = τ), ← Nat.cast_sum, ← E]
    split <;> norm_cast; lia
    have := Fact.mk (N.prime_of_mem_primeFactors l.2)
    have C := (hζ.pow h0.bot_lt (hr l ▸ mul_comm ..)).geom_sum_eq_zero Fact.out
    have := congr((Φ τ $hϵ, ($he : ℂ), Φ τ $(P.star_c₀InE s), $(hr l ▸ hG.2 σ τ), Φ σ $C,
      conj (Φ τ $C)))
    simp [sum_range, pow_add, pow_mul, ← hr, mul_assoc, ← mul_sum, reindex_equiv finProdFinEquiv,
      Fintype.sum_prod_type_right] at this
    simp [*, u, a, Fintype.sum_prod_type, @zero_pow_eq ℂ, apply_ite conj, mul_assoc, -nsmul_eq_mul,
      ← smul_sum, mul_left_comm (_ ^ _) (_ / _), mul_add, add_mul, sub_eq_add_neg,
      ← mul_sum, ← sum_mul]
    split <;> simp [t, field]; grobner
  · let l : N.primeFactors := ⟨p, by grind [norm_iota_periodFactor_eq_one, Fact, by simpa using h]⟩
    use .inl ⟨l, ⟨0, by grind⟩, ⟨1, Fact.out⟩, 0⟩, fun τ ↦ ?_
    simp [norm_iota_periodFactor τ, apply_ite, -mem_placeOfEmb] at h ⊢
    erw [ite_eq_left h.1, ← norm_mul, ← Complex.star_def, ← map_star_complex,
      ← map_mul (weightEmbedding ..)]
    convert! (norm_ringOfIntegers_le (weightEmbedding ιₚ τ) (-t * V l)).eq_of_not_lt fun g ↦ by
      grind [FinPlace.natCast_mem_iff_dvd, natCast_mem_placeOfEmb, mem_of_dvd _ (hV l) (by
    convert sub_mem (mul_mem_right ((1 - z + P.c₀InE s * z) * V l) _ h.1) (by simpa); grind)]
    simpa [field] using mod_cast by grind
  obtain ⟨⟨g, _⟩, w, _⟩ := (sub_one_dvd_pow_sub_one (a l) i).sub (sub_one_dvd_pow_sub_one _ k),
    sub_dvd_pow_sub_pow (P.c₀InE s) (n * -z) N
  have I y : ↑N ∣ y * t * (M l * (a l - 1)) → v.valuation _ (y * u ⟨l, j, k, i⟩) ≤ 1
    | ⟨c,
      _⟩ => by convert v.valuation_le_one (P.zetaInt s ^ j.1 * (y * 0 ^ k.1 * a l ^ i.1 + c * g))
               simpa [field, -coe_zetaInt] using mod_cast by grobner
  by_cases g : P.c₀InE s ∈ v.1 <;> [convert I (relDifferentGen ..) ⟨t * V l, by grind⟩; convert I
    (P.c₀InE s ^ N) (.mul_right ⟨n * e * w + f * (-z) ^ N * t, by grind [mul_pow, congr((t + $he,
    t + $hf))]⟩ _)] <;> simp [finiteImage, WeilData.α, α, g, v.valuation_eq_one_iff_notMem.2]
