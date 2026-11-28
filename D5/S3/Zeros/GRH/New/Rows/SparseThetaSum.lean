/- GID: D5/S3/Zeros/GRH/New/Rows/SparseThetaSum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/SparseThetaSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.SparseThetaSum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/SparseThetaSum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Weil.FockCoeffDecay
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Holomorphic.NearMaximum
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Products of theta forms detect all good forms (see New.Rows.Separation).

This file: Crude formal degree bound; rotation argument isolating a value at a point where |F| is at
least half its supremum. Sparse
theta sums approximate a matrix coefficient; first minimum of Hom lattices. -/

open MeasureTheory Matrix Norms.L2Operator Finset Fintype AddCircle NumberField
variable {E n} [Field E] [NumberField E] [Fintype n] [Nonempty n] {s m} {B : ℝ} (hn :
  numInfPlaces E * (2 * card n ^ 3) ≤ m) (hm : m ≤ B) (hB : 10 ^ 13 ≤ B) {o} {k w : InfinitePlace
  E → _} (ho : @IsPosFirstOrder n s o) (hu : ∀ τ, IsKDominant s o (w τ)) (hd : ∀ τ,
  IsKDominant s o (k τ)) (hw : ∀ τ,
  HasHolGap s (w τ) (300 * m)) (hk : ∀ τ, HasHolGap s (k τ) (300 * m)) (hk' : ∀ τ i, |↑(k τ i)| ≤ B)

attribute [fun_prop] IsHolOfWeight IsHolOfWeight.continuous

attribute [local simp] maxOpNorm abs_of_pos Measure.real

@[bound] lemma one_le_maxOpNorm (h : GInf E s) : 1 ≤ maxOpNorm h :=
  (norm_le_pi_norm _ Classical.ofNonempty).trans' (U.one_le_norm _)

include hn hm hB ho hu hd hw hk hk'

/-- Let w, k be dominant with gap 300m, |k| ≤ B, 2f|n|³ ≤ m ≤ B, B ≥ 10¹³ (f infinite places).
Then ∫|mh_k|² > 0
(`holMinorsPi`); if A is continuous, |A(h)| ≤ C‖h‖^N, N ≤ 6m, then A·mh_w is integrable and
|∫A·mh_w| ≤ C·B^{7m}∫|mh_k|². -/
lemma integral_mul_holMinorsPi_le : 0 < ∫ h, ‖holMinorsPi s k h‖ ^ 2 ∧ ∀ A, Continuous A → ∀ᵉ (C)
  (N ≤ 6 * m), (∀ h, ‖A h‖ ≤ C * maxOpNorm h ^ N) → Integrable (A * holMinorsPi s w) ∧
  ‖∫ h, A h * holMinorsPi s w h‖ ≤ C * B ^ (7 * m) * ∫ h, ‖holMinorsPi s k h‖ ^ 2 := by
  obtain ⟨_, _, q, _⟩ := @card_pos n _ _, le_of_mul_le_of_one_le_right hn card_pos,
    (card n).pow_le_pow_right card_pos (2).le_succ, (card n).le_mul_self
  let c := 2 * card n ^ 3 * 5; choose b e using
    (dsCoeff_eq_holMinors ho (8 * m) (300 * m) · · · (by lia))
  choose i t using fun τ ↦ integral_tail_le (hg := b _ (hd τ) (hk τ)) (L := 2 * ⌊B⌋₊ + card n)
    (fun a ↦ by grw [Pi.add_apply, abs_add_le, abs_twoRho_le, ← Nat.le_floor (n := (k τ a).natAbs)]
    <;> simp [*]) c (by lia)
  obtain ⟨_, P⟩ := (isHolOfWeight_holMinorsPi ho hu).continuous, univ.prod_pos fun τ _ ↦
    formalDegree_pos (b _ (hd τ) (hk τ))
  refine have I := by simp [holMinorsPi, formalDegree, prod_pow,
      ← integral_fintype_prod_volume_eq_prod, *]
    ⟨(inv_pos.2 P).trans_eq I, fun A a C N hN H ↦ have := by simpa using (norm_nonneg _).trans (H 1)
      have j := (Integrable.fintype_prod i).const_mul (C * 2 ^ N * ∫ h, ‖holMinorsPi s k h‖ ^ 2)
      (imp_and.2 ⟨j.mono' (by fun_prop), (norm_integral_le_of_norm_le j · |>.trans ?_)⟩) (.of_forall
      fun h ↦ (IsGreatest.pi_norm (h · |>.1.1)).1.elim fun a z ↦ (norm_mul_le ..).trans ?_)⟩
  grw [integral_const_mul, (integral_fintype_prod_eq_prod _).trans_le (prod_le_prod₀ (by
    intros; rw [formalDegree]; positivity) fun τ _ ↦ t τ), mul_right_comm, mul_assoc C, prod_const,
    q, pow_mul' 2, le_self_pow₀ (a := 8), ← mul_pow, ← mul_pow, ← pow_mul', card_univ,
    hn, hN, pow_mul, ← mul_pow, pow_mul B, (?_ : _ + 1 ≤ 5 * B)] <;> try bound
  gcongr; field; bound
  rify at *; grind [Nat.floor_le]
  grw [H, holMinorsPi, norm_prod, fun τ ↦ (e _ (hu τ) (hw τ) _ ▸ norm_dsCoeff_le_pow (by tauto)
    (c := c + ite (τ = a) N 0) (by rify at *; grind) _ :)]
  simp [pow_add, ← z, div_pow, field, -mul_ite, ← I]

/-- Isolation, for k, w as in `integral_mul_holMinorsPi_le`. Let F be continuous, holomorphic of
weight k,
|F| ≤ 2|F(z)| ≠ 0, K₀ bounded. If each x with |F(x)| ≥ |F(z)| has ∫conj F(xh)·K·mh_w = 0 for
some K holomorphic of weight k − w, |K − K₀| ≤ ε‖h‖^{6m}, then |K₀(1)| ≤ (4B^{7m} + 1)ε. -/
lemma isolation [IsCMField E]
    {F z C ε} {K₀ : _ → ℂ} (hF : Continuous F) (c : IsAdelicHol o k F) (ha : F z ≠ 0)
    (h2 : ∀ x, ‖F x‖ ≤ 2 * ‖F z‖) (g : ∀ h, ‖K₀ h‖ ≤ C) (H : Integrable (holMinorsPi s w) → ∀ x, ‖F
  z‖ ≤ ‖F x‖ → ∃ K, IsHolOfWeight s o (k - w) K ∧ (∀ h, ‖K h - K₀ h‖ ≤ maxOpNorm h ^ (6 * m) * ε) ∧
  ∫ h, star (F (x * (h, 1))) * K h * holMinorsPi s w h = 0) : ‖K₀ 1‖ ≤ 4 * ε * B ^ (7 * m) + ε := by
  have ⟨I, i⟩ := integral_mul_holMinorsPi_le hn hm hB ho hu hd hw hk hk'
  choose K hK r _ using fun θ ↦ H (by simpa using i 1 continuous_one 1 0 : _ ∧ _).1
    _ (by simpa using congr(‖$((c z).apply_mul_diagTorus 1 (@toCircle 1 θ ^ o ·))‖).ge)
  refine let W θ h := _; have v h : ∫ θ, W θ h = _ :=
        (c z).circle_mean_holMinorsPi ho hd h ▸ integral_conj; ?_
  have hf := ((i (K 0) (by fun_prop) (C + ε) _ le_rfl fun h ↦ by
    grw [norm_le_insert' _ (K₀ h), r, ← g]; ring; bound).1.comp_snd volume).mul_bdd (g :=
    W.uncurry) (by fun_prop) (.of_forall (by simp [W]; tauto))
  obtain ⟨j, this⟩ := hf.integral_prod_right, integral_prod_symm _ hf ▸ integral_prod _ hf ▸
    norm_integral_le_of_norm_le_const (hf.prod_right_ae.mono fun θ X ↦ by
      have ⟨d, q⟩ := i (W θ * (K 0 - K θ)) (by fun_prop) (4 * ε * ‖F z‖) _ le_rfl fun h ↦ by
        simp [W]; grw [h2, ← sub_sub_sub_cancel_right _ _ (K₀ h), norm_sub_le, r, r]; linarith
      rwa [← sub_eq_zero.1 ((integral_sub d X).symm.trans _)]
      simp; ring_nf; simp_all [W, mul_right_comm _ _⁻¹, mul_assoc z, integral_neg])
  simp_all [← mul_assoc, integrable_mul_const_iff, -Pi.mul_apply]
  grw [norm_le_insert (K 0 1), r]
  simpa [↓(sub_add_cancel k w ▸ (hK 0).mul ho.1
    (isHolOfWeight_holMinorsPi ho hu)).integral_mul_conj_holMinorsPi ho hd j, I, field] using this

omit hn hm hB ho hu hd hw hk hk'

open BigOperators Circle ComplexConjugate Prod Space WeilData

attribute [local simp] EuclideanSpace.norm_eq Modulus.liftFn_apply Set.indicator firstMinimum_pos
  move_vecAtPoint vecToMat le_of_lt realCoord traceChar vacuumFn

variable {E n n' : Type} [Field E] [CMType E] [Fintype n] {s : _} [Fintype n'] {s'} [Nonempty n]
  [Nonempty n'] {S : Space E n s} (T : Space E n' s')

/-- For a nonzero integer N in the different of E, the shortest vector length of the lattice of
Hom(S,T) is at least λ_S·λ_T/(6N(fn)²n′n), with n, n′ the ranks and f the number of infinite
places. -/
lemma firstMinimum_mul_le_hom {N} [NeZero N] (hd : ↑N ∈ differentIdeal ℤ (𝓞 E)) :
    S.firstMinimum * T.firstMinimum / (shortBasisConst E n N * Fintype.card n' * Fintype.card n) ≤
  (S.hom T).firstMinimum := by
  rw [le_firstMinimum_iff]
  use by grw [firstMinimum_le_one, firstMinimum_le_one] <;> simp [Nat.cast_inv_le_one,
    ← Nat.cast_mul], fun z _ o ↦ ?_
  choose Y hY hY' using S.exists_short_basis hd
  choose a b using (T.mem_and_norm_le_of_vecAtPoint _ S · (vecToMat (vecAtPoint _ z)) 1 (fun w ↦
    l2_opNorm_le_of_apply ((archCoords _ z).norm_apply_le ⟨w, ·, ·⟩)) (by erw [one_smul,
    vecAtPoint_hom _ _ (vecToMat z), ratMap_mulVec_vecAtPoint]))
  have := S.firstMinimum_pos
  grw [firstMinimum_le (a _ (by simp_all [baseLattice]) (hY _)) (Function.ne_iff.1 fun H :
    (vecToMat z * Y.1)ᵀ = 0 ↦
    o (by simpa using! congr(matToVec ($Hᵀ * Y.2)))).choose_spec, b, hY']; simp [field]

omit [Nonempty n] [Nonempty n'] in
/-- For Ψ_t(y) = ψ(tr(yt)) modulo 𝔪 and an adelic vector z, ⟨v ⊗ Ψ_t ⊗ vac, ϱ(z)(w ⊗ Ψ_t ⊗ vac)⟩
is Ψ_t read at α⁻¹z_f (`Modulus.liftFn`) times ⟨v, ρ(z_∞)w⟩ times the vacuum at the finite
part z_f. -/
lemma dataInner_traceChar [WeilData E] {𝔪} t v w z : dataInner _ (modDatum S T 𝔪 (traceChar t) v)
  (ϱ _ z (modDatum S T 𝔪 (traceChar t) w)) = 𝔪.liftFn (traceChar t ∘ vecToMat) (finCoord z) *
  (realInner v (realHeisOp (realCoord z) w) * vacuumFn (0, z · |>.2)) := by
  obtain ⟨u, rfl : of _ = _⟩ := 𝔪.reduction_surjective.comp_left.comp_left t
  erw [rho_integrated_realCoord, dataInner_integrated, (_ : _ ∘ vecToMat = _),
    𝔪.name_char_eq_translate_projOn _ (matToVec u ∘ swap), ϱ_swap,
    map_smul] <;> simp +contextual [-Heisenberg.Rep.mul, funext_iff, finVec, ↓← rho_integrated,
    matToVec, finCoord, trace, adelicHeis, Matrix.mul_apply, ← map_mul, ← map_sum, stdForm,
    stdAddChar, dotProduct, fst_sum, snd_sum, ← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, two_mul,
    ← add_mul, ← map_add, mul_mem] <;> simp [stdLattice.psi₀_apply, Finset.mul_sum, sum_prod_type,
    mul_assoc, mul_left_comm, mul_comm (u ..).1]

/-- Sparse theta sums. Let c ≠ 0, cα𝔪Ô ⊆ Ô, 0 < m, m|τc| ≤ √(2π Im τȷ)·λ_{Hom(S,T)}(g,h) for all
τ, q > fnn′, Q homogeneous of degree d. Then for some Ψ mod 𝔪, θ[Ψ,Q](gu,hu′) is within
(100(d+2q)/m²)^q(‖u‖‖u′‖)^{3q}‖v_Q‖² of ⟨v_Q, Ω(u,u′)v_Q⟩ for all real u, u′. -/
lemma norm_modKernel_sub_realInner_le [WeilData E] {a b γ γ' ψ ψ' 𝔪 g} (ha : a.HasWeight γ ψ) (hb :
  b.HasWeight γ' ψ') {c : E} (c0 : c ≠ 0) (hc : ∀ z, 𝔪.reduction z = 0 → ↑c * (α.1 * ↑z) ∈ Ô E) h m
  q (m0 : 0 < m) (hm : ∀ w, m * ‖Φ w c‖ ≤ √(2 * .pi * (Φ w j).im) * ((S.move g).hom (T.move
  h)).firstMinimum) (hq : Fintype.card (InfinitePlace E × n' × n) < q) Q {v} (hv : v = polyVector _
  Q) (d : ℕ) (hQ : ∀ (c : ℝ) x, Q.eval (c • x) = c ^ d * Q.eval x) : ∃ Ψ, ∀ u u', ‖modKernel S T a b
  𝔪 Ψ Q (g * (u, 1)) (h * (u', 1)) - realInner v (realPairWeil γ γ' (u, u') v)‖ ≤ maxOpNorm u' ^
  (3 * q) * (100 * (d + 2 * q) / m ^ 2) ^ q * ‖realInner v v‖ * maxOpNorm u ^ (3 * q) := by
  use 𝔼 t, conj (modKernel S T a b 𝔪 (traceChar t) Q g h) • traceChar t, fun u u' ↦ ?_
  let L := (S.hom T).move (G.onHom (g, h))
  rw [show hom .. = L by simp [L, move, hom, Units.ext_iff, mul_kronecker_mul, G.onHom]] at hm
  have A (y : {y | c • y ∈ L.baseLattice ∧ y ≠ 0}) : m ≤ ‖WithLp.toLp 2
    (realCoord (L.vecAtPoint y))‖ := by grw [← mul_le_mul_iff_right₀ L.firstMinimum_pos,
    ← norm_smul_of_nonneg, firstMinimum_le y.2.1, mul_comm, ← norm_smul_of_nonneg] <;> simp [*,
    abs_of_nonneg, archCoords, val_scaleIdele_fst, ← mul_assoc, ← mul_rotate √_, y.2.2]; grw [hm]
  have ⟨p, r⟩ := tsum_inv_pow_le_of_separated (n := 2 * q) m0 (fun y z h ↦ by simpa [sub_div]
    using (A ⟨y - z, by grind [smul_sub, sub_mem]⟩)) A (by simp_all; omega)
  have h4 :=
    (hasSum_sum (s := ⊤) fun t _ ↦ let φ := ω _ (G.onHom (g, h)) ∘ modDatum S T 𝔪 (traceChar t)
    hasSum_dataInner _ (φ (realPairWeil γ γ' (u, u') v)) (φ v)).mul_left
    (Fintype.card (Matrix n n' 𝔪.ResRing) : ℂ)⁻¹
  simp [dataInner_omega_left, ω_ϱ, rep_apply_apply, dataInner_traceChar, finCoord, ← Finset.sum_mul,
    sum_addChar_trace_mul, Modulus.isPrimitive_primAddChar, ← ext_iff] at h4
  refine ((((hasSum_subtype_iff_of_support_subset ?_).2 (hasSum_ite_sub_hasSum h4
    0)).norm_le_of_bounded (p.hasSum.mul_left _) fun y ↦ .trans ?_ (norm_realInner_realHeisOp_le
    (pairHomInf (u, u')) hv hQ le_rfl (by simp) (m0.trans_le (A y)))).trans' ?_).trans ?_
  simp_intro y h
  simpa [L, baseLattice] using
    (hc _ <| (𝔪.reduction_idem_mul ⟨_, h.2.1 _ _⟩).symm.trans <| h.2.2.1.2 · ·)
  simp; split_ifs <;> simp [L, realPairWeil]
  rw [← modKernelBilin_apply]; simp [modKernel, pairTheta, ← mk_mul_mk, mul_comm (conj _),
    modDatum, *, pairWeil_integrated,
    Finset.expect, NNRat.smul_def, ← ZeroMemClass.zero_def, realCoord.eq_unfold, ← Pi.zero_def]
  simp [pairWeil, mul_mul_mul_comm _ _ (_ * _), ← coe_inv_eq_conj, mul_mul_mul_comm _ _⁻¹]
  nth_grw 1 [Complex.re_le_norm, r, hq, hq, pow_mul, mul_assoc,
    ← mul_pow, show ‖(pairHomInf _).1.1‖ ≤ maxOpNorm u * _ from
    (NonUnitalStarAlgHom.norm_apply_le ({ blockMatrix with .. } : _ →⋆ₙₐ[ℂ] Matrix (InfinitePlace E
    × n' × n) _ _) _).trans ((pi_norm_le_iff_of_nonempty _).2 fun w ↦ (norm_pairHom_le ..).trans (by
    gcongr <;> apply norm_le_pi_norm _ w))] <;> simp [U.one_le_norm, submatrix_smul, star]
  linear_combination
