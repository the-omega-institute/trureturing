/- GID: D5/S3/Zeros/GRH/New/Curve/JetDivisibility
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Curve/JetDivisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Curve.JetDivisibility. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/JetDivisibility.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Core.ModuleIndex
import D5.S3.Zeros.GRH.New.Curve.LiveSum
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Divisibility of matrix jets at non-split primes. The jet of a series Θ along a polynomial Q is
(Q(∂)Θ)(0); the partners of a place σ are the −p^eσ. For p inert or ramified in K, jets of theta
products along products of minors have valuation bounded below, since each derivative gains and
couplings with partner places take back, leaving about (a/p − w)₊ at inert p for order a against
partner order w; this is the weight of the prime sum, and scaled jets are integral at every p. One-
and two-variable divisibility at inert p over an imaginary quadratic field is known. Related work:
Katz, Divisibilities, congruences, and Cartier duality, 1981; Chellali, Congruences entre nombres de
Bernoulli–Hurwitz dans le cas supersingulier, 1990; Fujiwara, Divisibilities of special values of
real analytic Eisenstein series, 1988; Bannai–Kobayashi–Yasuda, Radius of convergence of the p-adic
sigma function, 2017.

This file: Tilting matrices that kill Frobenius pairings at controlled determinant cost. Lower bound
for valuations of Schur jets when Frobenius couplings are silenced. -/

open Finset Real Matrix Valuation MvPolynomial Fintype IsUltrametricDist NormedField PolyRep

/-- For Y over 𝔬, any θ ∈ 𝔬 (θ = 0 allowed) and q = |θ| there are M_{σ,h} ∈ M_h(𝔬), with ∏|det M|
over all columns ≥ q^{∑`couplingCount`}, such that the pairings ∑_a m_a^{p^j} m′_a (j ∈ S, m of
M_{σ,h}Y_σ, m′ of M_{pr_jσ,h′}Y_{pr_jσ}) vanish modulo p and θ, unless h = 1 and σ ∈ ev, or
h = h′ = 1 and pr_jσ ∈ ev. -/
lemma exists_null_coupling_frames {p : ℕ} [Fact p.Prime] {Φ n} [Fintype Φ] [Fintype n] (pr : ℕ → Φ →
  Φ) S N κ ev (Y : Φ → n → ℕ → valRingCp p) θ : ∃ M : ∀ _ h,
  Matrix (Fin h) (Fin h) _, ‖θ‖ ^ ∑ e ∈ S, ∑ σ, couplingCount p κ N
  ev σ (pr e σ) e ≤ ∏ j : Σ _, Fin N, ‖(M j.1 j.2).det‖ ^ κ j.1 j.2 ∧ ∀ {R} [CommRing R] [CharP R p]
  (g : _ →+* R), g θ = 0 → ∀ (j : S) σ {h} i {h'} i', ¬(h = 1 ∧ (σ ∈ ev ∨ h' = 1 ∧ pr j σ ∈ ev)) → g
  (∑ a, (M σ h i ⬝ᵥ (Y σ a ·)) ^ p ^ j.1 * M (pr j σ) h' i' ⬝ᵥ (Y (pr j σ) a ·)) = 0 := by
  delta couplingCount; extract_lets t r D
  choose ρ hρ using (@IsAIC.exists_pow_eq (valRingCp p) _ (.of_isIntegrallyClosedIn ℂ_[p]) <| p ^ ·)
  let A h e σ b s := (h = 1 → cond b σ (pr e σ) ∉ ev ∧ s = b) ∧ (ite (s ∧ h ≠ 1)
    ((D σ : ℝ) / p ^ e ≤ D (pr e σ)) (s = b → (t σ : ℝ) / p ^ e ≤ r (pr e σ) + t (pr e σ)) ↔ b)
  choose M hM v _ hA using fun τ h ↦ IndexDvd.of_det_dvd (det_diagonal (d :=
    fun ((e : S), σ, b, (o : Option (Fin h))) ↦ ite (cond b σ (pr e σ) = τ ∧
    A h e σ b o.isSome) (ρ (ite b e 0) θ) 1)).dvd le_rfl _ (fun j (e, σ, b, o) ↦ o.elim (∑ a,
    ite b (ρ e (Y (pr e σ) a 0)) (Y σ a 0 ^ p ^ ↑e) * Y τ a j) (diagonal 1 j)) (by simp)
  use M, ?_, fun g _ j σ h i h' _ _ ↦ ?_
  grw [← fun τ h ↦ show ‖(_ :
    valRingCp p)‖ ≤ ‖(M τ h).det‖ from (integer.integers _).le_of_dvd (hM ..)]
  simp (disch := intros; positivity) only [← rpow_mul_natCast, sum_mul, norm_prod,
    ← pow_boole, norm_pow, fun e ↦ show ‖ρ e θ‖ = ‖θ‖ ^ (p ^ e : ℝ)⁻¹ by
      simp [← congr(‖$(hρ e θ)‖), ← rpow_natCast_mul], ← S.sum_coe_sort, ← rpow_sum_of_nonneg,
    ← @sum_comm (Sigma _), min_def, Fintype.sum_prod_type]
  congr!
  split_ifs <;> simp [*, A, ite_and, Fintype.sum_sigma] <;> simp +zetaDelta [sum_range,
    sum_div, ← sum_add_distrib] <;> clear * - θ <;> grind [Nat.cast_eq_one]
  have D h b i o (_ : A h j σ b o.isSome) :=
    congr(g ($(hA (cond b σ (pr j σ)) h i) (j, σ, b, o) ^ p ^ ite b j.1 0)).symm
  simp [↓Option.forall, -pow_ite, @sum_comm n, hρ, mul_pow,
    @mul_sum n, mul_left_comm (M ..), ← mul_sum, ← map_pow _ (ρ ..), sum_pow_char_pow] at D
  obtain ⟨⟨⟩, ⟨⟩, H, ⟨⟩⟩ : ∃ b s, A (b.rec h' h) j σ b s ∧ 1 = s.rec (b.rec h h') 1; simp; lia
  repeat simp [sum_pow_char_pow, mul_pow, mul_assoc, mul_comm (∑ _, _), ← mul_sum, *, dotProduct]

attribute [local simp] sum_range prod_pow_eq_pow_sum prod_smul Finsupp.prod smul_pow ite_and
  linearSeries boxes

/-- Divisibility of Schur jets. Let κ fit, with B boxes, |ϖ| = p^{−ρ}, |θ| = p^ω, and let the
charges g be nonzero at one end of each coupling exempted by the even places ev. If
`IsIntegralOnNullCone` holds up to degree B, each entry of the jet matrix along S_κ has valuation ≥
(1/(p−1) − ρ)B + ω∑`couplingCount` − |Φ||n′|³(⌊log_p B⌋ + 1) − m, m the total charge of the boxes of
its row.

Divisibility of matrix jets at non-split primes. -/
lemma norm_schurJet_le {p : ℕ} [Fact p.Prime] {Φ n n'} [Fintype Φ] [Fintype n] [Fintype n']
    {κ} (hκ : FitsRanks n n' κ) {pr S ρ ω ϖ θ Θ ev} (hϖ : ‖ϖ‖ = p ^ (-ρ))
    (hπ : ‖(θ : valRingCp p).1‖ = p ^ ω) (g : Φ → ℕ → _ → ℕ) (hg : ∀ e ∈ S, ∀ σ h b,
    σ ∈ ev ∨ h = 1 ∧ pr e σ ∈ ev → g σ 1 b ≠ 0 ∨ g (pr e σ) h b ≠ 0) {i'} {i : WeylIndex n κ} :
  let N := card n'; let B := boxes κ N; let m := ∑ τ, ∑ h : Fin N, ∑ j, ∑ b, g τ h ((i' τ).1 h j b)
      IsIntegralOnNullCone pr S ϖ θ B Θ → ‖schurJet κ Θ i' i‖ ≤ p ^ (m - ((1 / (p - 1) - ρ) * B + ω
        * ∑ e ∈ S, ∑ σ, couplingCount p κ N ev σ (pr e σ) e - card Φ * N ^ 3 * (p.log B + 1))) := by
  intro N B m hV; let L := ((jet _).flip Θ).toAddMonoidHom
  refine (exists_val_coeff_le_val_eval valuation ![AddMonoidAlgebra.map L _]).elim fun (y : _ →
    valRingCp p) h ↦ .trans (coord_mem_of_coeff_mem ((valuation.leAddSubgroup _).comap L) _
    (sum_schur_smul_nablaBasis hκ ..) (h 0) _) ?_
  have : 1 < p := Fact.out
  choose M hM hA using exists_null_coupling_frames pr S N κ ev (y ⟨⟨·, ·⟩, ·⟩) θ
  let z := fun (τ, b, a) (o : (Σ h : Fin N, Fin h) × _) ↦
    ite (o.2 = (τ, b)) (p ^ g τ o.1.1 b * M τ _ o.1.2 ⬝ᵥ (y ⟨⟨τ, a⟩, ·⟩)) 0
  specialize hV (linearSeries ∘ z) (by simp) fun φ h0 j hj ↦ by
    simp [sum_pow_char_pow, Finset.sum_mul_sum, MvPowerSeries.smul_eq_C_mul, mul_pow,
      mul_mul_mul_comm _ (_ ^ _), @sum_comm _ _ (Φ × _), ← sum_mul]
    exact sum_eq_zero fun o _ ↦ sum_eq_zero fun q _ ↦
      flip id (hA (φ.comp _) h0 ⟨j, hj⟩ o.2.1 o.1.2 q.1.2) (by simp [apply_ite, CharP.cast_eq_zero,
      z, NeZero.ne, zero_pow_eq, sum_prod_type, Prod.ext_iff, ↓mul_comm (_ ^ _)]; grind +splitImp)
  have hc : _ * (‖ϖ‖ ^ B * (↑p)⁻¹ ^ m) ≤ ‖∏ τ, ∏ h : Fin N, ∏ j, (valRingCp p).subtype
    (M τ h)ᵀ.det * ∏ b, ϖ * p ^ g τ h ((i' τ).1 h j b)‖ := (mul_le_mul_of_nonneg_right hM
    (by positivity)).trans (by simp [B, m, Fintype.prod_sigma, norm_p_eq_inv, ← pow_mul])
  erw [(by simp [eval, eval₂, Finsupp.sum_mapRange_index, L, map_finsuppSum, C_eq_smul_one,
    mul_comm] : ∀ y f, eval y (AddMonoidAlgebra.map L f) = L (eval (C ∘ y) f)),
    ← mul_le_mul_iff_right₀ (hc.trans_lt' (hϖ ▸ hπ ▸ by positivity)), ← norm_smul,
      ← LinearMap.map_smul₂]
  grw [← hc, (?_ : _ • _ = linSubst (of (ϖ * z · ·)) (∏ τ, ∏ h : Fin N, ∏ j, (of fun b i ↦
    X (⟨h, i⟩, τ, (i' τ).1 h j b)).det)), ← jet_subst_linearSeries]
  simp only [det_apply, Fintype.prod_sum, X, ← monomial_sum_one, of_apply, prod_smul, map_sum,
    LinearMap.sum_apply]
  apply norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intros; set d : _ →₀ ℕ := Finset.sum ..
  have e : B = d.degree := by simp [d, B, mul_comm]
  apply flip id (d.support.sum_le_sum fun x _ ↦ (padicValNat_factorial_mem_Icc
    ((d.le_degree x).trans_lt (p.lt_pow_succ_log_self this _))).1)
  simp [norm_natCast_eq_inv_pow_padicValNat, smul_sum, smul_smul] at hV ⊢
  grw +useKAbstract [hV e.ge, card_le_univ, card_prod, Fintype.card_sigma,
    sum_le_card_nsmul _ _ N (by simp)]
  simpa [*, m, d.degree_apply, ← sum_div, ← rpow_mul, ← rpow_add, this.pos, ← rpow_neg,
    ← rpow_natCast p, ← rpow_mul_natCast] using (by linear_combination ·)
  simp only [nablaBasis, tableauPoly, minor, map_prod, AlgHom.map_det, RingHom.map_det, N,
    smul_eq_C_mul, ← prod_mul_distrib, map_mul, mul_rotate (det _), ← det_mul_column, ← det_mul]
  congr!; ext
  simp [z, linSubst, sum_prod_type, smul_eq_C_mul, mul_sum, rowSubst, sum_mul, entrywise,
    @sum_comm n, apply_ite, mul_assoc, mul_comm (X _), mul_left_comm (C (M ..).1)]
