/- GID: D5/S3/Zeros/GRH/New/Rows/Carrier
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/Carrier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.Carrier. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/Carrier.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.RealMatching
import D5.S3.Zeros.GRH.New.Exchange.ExchangeTheorem
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Exchange of theta kernels with explicit determinant polynomials. A fixed multiple of a theta
kernel summed over a definite unitary group equals a kernel integrated over a unitary group of no
larger rank, with explicit determinant polynomials on both sides, times a non-zero factor sized by
Hecke L-values and the conductor, and a block form moves the twist onto a square block. The first
term identity between theta integrals of complementary spaces and determinant harmonics are known.
Related work: Gan–Qiu–Takeda, The regularized Siegel–Weil formula, 2014 (after Kudla–Rallis, 1994;
Ichino, 2004); Kashiwara–Vergne, On the Segal–Shale–Weil representations and harmonic polynomials,
1978; Böcherer–Schulze-Pillot, Siegel modular forms and theta series attached to quaternion
algebras, 1991.

The carrier, one fixed form under all twists. The twisted theta kernel of an indefinite and a
definite unitary group of equal rank, summed against an explicit form, is a non-zero multiple of one
fixed non-zero holomorphic, rapidly decreasing form of level one, and the factor has modulus given
by Hecke L-values, so the twist survives only as a number. It is known that the theta lift of a
character in the stable range is non-zero and holomorphic. Related work: J.-S. Li, Non-vanishing
theorems for the cohomology of certain arithmetic quotients, 1992; Gan–Qiu–Takeda, The regularized
Siegel–Weil formula, 2014; T. Yang, Theta liftings and Hecke L-functions, 1997.

A class sum of a theta kernel as Hecke values. As the first step in turning the twist into a number,
the theta kernel of two definite unitary groups of the same even rank 2e with determinant data,
summed over the classes of one group, is a non-zero constant whose modulus is, up to a fixed factor
and conductor norms, a product of Hecke L-values at 1,…,e. In Rallis's formula at equal rank 2e for
a character, the central value folds by the functional equation into Hecke L-values at 1,…,e and a
conductor power, but the ramified local data need a computation. Related work: Yamana, L-functions
and theta correspondence for classical groups, 2014; C. Li, Geometric and arithmetic theta
correspondences (§2.4–2.5), 2024; Yang, Theta liftings and Hecke L-functions, 1997.

Part of: Twisted theta forms lie on one line (see New.Rows.LineArithmetic).

This file: Matched identity summed on a square block; datum reduces to one coset's class sum.
Exchange of theta kernels with explicit determinant polynomials and Hecke L-value constant. Twisted
theta class sums equal Hecke-value multiples of a constant and of the carrier. -/
seal Finset.univ Finset.sum Finset.prod

open Subgroup Fintype IsLevel MatMul Matrix MeasureTheory Space WeilData Ideal.Quotient

variable {E n b : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype b] {𝔪}

lemma isRapid_modKernel {s t} (S : Space E n s) (V : Space E b t) a β (h𝔪 : Nonempty 𝔪.places) {Ψ}
    (hΨ : ∀ y, Ψ y ≠ 0 → HasLeftInv y) P h : S.IsRapid (modKernel S V a β 𝔪 Ψ P · h)
  | B => let ⟨_, _, _, c⟩ :=
      pairTheta_modDatum_decay S V a β h𝔪 hΨ B; ⟨_, (c _ h · (weightedNorm_polyVector_ne_top _ P))⟩

/-- Let ββ′ be tame for (𝔪,χ), 𝔫 ∣ 𝔪, κΣ_hΞ(h)θ^{V,I_b}[χ∘det,1](x,h) = F(x), and κ′Σ_u
K(Φ,h,u) = ∫θ^{V,I_b⊕U}[Ψ,P](x,(h,g))dx for all χ⁻¹-partners Φ, Ψ. Then for Φ(x′,x″) = χ(det x″)Σ_k
f(x″⁻¹x′k), k in GL_b(O/𝔫): κκ′|GL_b(O/𝔫)|⁻¹Σ_uΣ_hΞ(h)K(Φ,h,u) = ∫F·θ^{V,U}[f,P](·,g).

Exchange of theta kernels with explicit determinant polynomials. -/
lemma explicit_matching_of_sum {s t} (V : Space E b t) {𝔪} (U : Space E n s) {a β β' e χ} (hχ :
  IsTameFor 𝔪 (β * β') e χ) {Ξ F : _ → ℂ} {κ} (hF : ∀ x, κ * stdClassSum (Kf ..) (fun h ↦
  Ξ h * modKernelI V a β 𝔪 (χ ·.det) 1 x h) = F x) 𝔫 (φ : 𝔪.ideal ≤ 𝔫.ideal) f {P g} {K : _ → _ →
  _} {κ'} (hK : ∀ Φ Ψ, IsPartner ⊤ (.refl _) χ⁻¹ Φ Ψ → ∀ h, κ' * stdClassSum (Kf E n) (K Φ h) = ∫ x,
  modKernel V ((stdSpace ..).sum U) a (β * β') 𝔪 Ψ (renameRowsCols .inr id P) x (.sum ((1, h),
  g)) ∂V.quotMeasure) : κ' * (κ / card (GL b 𝔫.ResRing)) * stdClassSum (Kf ..) (stdClassSum (Kf ..)
  fun h ↦ Ξ h * K (fun x ↦ χ x.toCols₂.det * ∑ k : GL b 𝔫.ResRing, f ((x.toCols₂⁻¹ * x.toCols₁).map
  (factor φ) * k.1)) h ·) = ∫ x, F x * modKernel V U a β' 𝔫 f P x g ∂V.quotMeasure := by
  simp_rw [modKernel, ← modDatum_factor φ, ← modKernel.eq_1, @classSum_comm (Gf E n), mul_classSum]
  let Ψ y := χ (toRows₁ y).det * f (y.toRows₂.map (factor φ))
  have d P h := (fun c ↦ And.intro ((isRapid_modKernel V ((stdSpace ..).sum U) a (β * β') hχ.1 (Ψ :=
    Ψ) (fun y h ↦ ⟨fromCols y.toRows₁⁻¹ 0, y.fromRows_toRows ▸ by simp_all [-fromRows_toRows, Ψ,
    χ.apply_eq_zero_iff]⟩) P h).integrable c) fun x : Kf E b ↦ V.integral_comp_mul_right x
    (pairThetaKer ..).theta_rat_mul c) (by fun_prop [modKernel])
  specialize hK _ (∑ i : GL b 𝔫.ResRing, (χ (𝔪.reductionK₀ (liftMod i)).det)⁻¹ •
    (Ψ <| · * (𝔪.reductionK₀ (liftMod i)).1)) ((funext (fromRows_toRows · ▸ by
    simp [-fromRows_toRows, ← mul_assoc, ← Finset.mul_sum, Ψ, χ.apply_eq_zero_iff, inv_mul_eq_div]
    use (em _).imp_left fun h ↦ Finset.sum_equiv (.mulLeft (.map (factor φ) (-.mk'' _ h)⁻¹))
      (by simp) (by simp [Matrix.map_neg]))).subst
    (partner_block _ _ (∑ g : GL b 𝔫.ResRing, (f <| ·.map (factor φ) * g.1))))
  simp_all [← mul_classSum, mul_left_comm κ', ← modKernel_sum_right, ← hF, mul_assoc, Ψ,
    modKernel_mul_Kf_left, ↓hχ.apply_det]
  simp_all [← modKernelBilin_apply, classSum, Rat.smul_def, Finset.mul_sum,
    Integrable.const_mul, ← mul_assoc, integral_finsetSum]; field

/-- Let α be tame with character χ mod 𝔪, v_P fixed by U(b)(ℝ), F left invariant under
H = `rowStabilizer`. The class sum at level K₀ of the kernel with datum χ(det x″)F(x″⁻¹x′) equals
that at level H with datum `columnDatum`(x″_e)·1[x″ is 1 off e]·F(x′). -/
lemma stdClassSum_rowStabilizer_eq {r c S} [Fintype r] [CommRing S] {s α β γ χ P g} {W : Space E _
  s} (hα : IsTameFor 𝔪 α γ χ) (hP : ∀ u, realPairWeil (s := s) (s' := 1) γ 0 (1, u) (polyVector _
  P) = polyVector _ P) (φ : 𝔪.ResRing →+* S) (w : Matrix c b S) (e : r ↪ b) {F : Matrix b n _ → ℂ}
  (hF : ∀ A ∈ rowStabilizer φ w e, ∀ y, F (A.1 * y) = F y) : stdClassSum
  (𝔪.levelOfSubgroup (rowStabilizer φ w e)) (modKernelI W α β 𝔪 (fun x ↦ columnDatum χ φ w e
  (x.toCols₂.submatrix id e) * ite (FixesColsOff e x.toCols₂) (F x.toCols₁) 0) P g) = stdClassSum
  (Kf E b) (modKernelI W α β 𝔪 (fun x ↦ χ x.toCols₂.det * F (x.toCols₂⁻¹ * x.toCols₁)) P g) := by
  rw [stdClassSum, ← (eq_inv_smul_iff₀ (by simp)).1 (classIntegral_eq_of_le ?l ?s le),
    ← classIntegral_eq_classSum (Subtype.forall'.2 fun k h ↦ ?_), eq_comm,
    classIntegral_sum Finset.univ (fun _ ↦ .id ℂ) (fun q : _ ⧸ rowStabilizer φ w e ↦
    ↑(liftMod q.out)) (fun _ ↦ ⟨?l, isOpen_mono ?s isOpen⟩) fun h ↦ ?_]
  simp [Rat.smul_def, 𝔪.stdLevelIndex_levelOfSubgroup, index]
  dsimp; rotate_left 2
  · rintro _ ⟨δ, rfl⟩ h; refine .trans ?_ ((pairThetaKer ..).swap.theta_rat_mul _ ⟨δ, rfl⟩ h)
    nth_rw 1 [modKernelI, modKernel, modDatum, ← hP (ratEmbed _ δ).1, ← pairWeil_integrated_right
      (ha := hα.2.choose_spec.1), ← pairTheta_mul]; simp [modDatum, pairTheta, embFin, Prod.mul_def]
  rintro _ ⟨k, m, rfl : k.1 = _⟩ h
  all_goals
    simp only [columnDatum_mul_ite_eq _ _ w e hF, ↓modKernel_mul_Kf_right, hα.apply_det,
      ← modKernelBilin_apply, ← LinearMap.sum_apply, ← map_sum]
    congr with x; rw [← x.fromCols_toCols]; generalize x.toCols₂ = y
    obtain _ | ⟨y, rfl⟩ := em' (IsUnit y) <;> simp_all [χ.map_nonunit, isUnit_iff_isUnit_det,
      ← mul_assoc (χ _), ← map_mul, ← det_mul] <;> norm_cast <;>
      simp_all [← QuotientGroup.eq, mul_mem_cancel_left]

/-- Explicit matching. W, V′ have |l| negative signs, |a| = rk V′ + 2d, rk W ≥ 2|l| + 2. For some C,
possibly 0,
each tame α of weight |l| − |ι_τ| has c, |c|² = C/`lValueProd`(α⁻¹υ^{rk V′+d}, d), with c·Σ_h
θ^{W,I_a}_{α,β}[Φ, stackedDetProd e η](g,h) = ∫θ^{V′,W}_{α/β,α}[Ψ, matchedPoly f j η](x,g)dx for all
β, η, g, χ⁻¹-partners Φ, Ψ.

Exchange of theta kernels with explicit determinant polynomials. -/
lemma explicit_matching {E} [Field E] [CMType E] [WeilData E] {n m a b p l} [Fintype n] [Fintype m]
  [Fintype a] [Fintype b] [Fintype p] [Fintype l] {s} (W : Space E n s) (f : p ⊕ l ≃ b) (V' : Space
  E _ (blockSigns f)) σ e (j : m ⊕ l ≃ n) (hj : s = blockSigns j) {d} (hd : card a = card b + 2 * d)
  (hn : 2 * card l + 2 ≤ card n) ι [∀ τ, Fintype (ι τ)] : ∃ C, ∀ {𝔪 α γ χ}, IsTameFor 𝔪 α γ χ →
  (∀ τ, γ τ = card l - card (ι τ)) → ∃ c, ‖c‖ ^ 2 = C / lValueProd 𝔪.places
  (α⁻¹ * upsilonU1 ^ (card b + d)) d ∧ ∀ η {Φ Ψ}, IsPartner ⊤ σ χ⁻¹ Φ Ψ → ∀ β g, c * stdClassSum
  (Kf E a) (modKernelI W α β 𝔪 Φ (renameRowsCols id (j ∘ .inl) (stackedDetProd e η)) g ·) = ∫ x,
  modKernel V' W (α / β) α 𝔪 Ψ (matchedPoly (ι := ι) f j η) x g ∂V'.quotMeasure := by
  subst_vars
  choose Q₀ κ hκ using real_matching f j e (ι := ι) rfl; have := card_congr σ ▸ card_sum
  apply (exchange_theorem W _ V' σ _ hd _ _ (weightedNorm_polyVector_ne_top · Q₀)).elim
  rintro C ⟨x, -, H⟩; constructor
  intro 𝔪 α _ χ hα@⟨o, _, _, _⟩ hγ; cases funext hγ
  choose c _ q hc using H 𝔪 _ _ (hα.inv.mul (hasWeight_upsilonU1_pow _))
  use κ x / c, by rw [norm_div, div_pow, q, div_div], fun η Φ Ψ hP β g ↦ ?_
  obtain ⟨⟨L, hL⟩, hv⟩ := (pairThetaKer W (stdSpace E a) α 1).swap.exists_clm_lift
    (isAutomorphic_const _ 1).mem_rapidFunctions, realPairWeil_stackedDetProd j e rfl η 1
  simp [rankTwist, Space.lift, ↓mul_inv,
    (by omega : card n / 2 = card b + d), -Prod.forall] at hc hL hv
  change ∀ f g, thetaIntegral .. = _ at hL; specialize hκ x
    ((L · ∘L .flip (integrated _) _) ∘ (g * ⟨·, 1⟩)) (c • ⟨⟨(∫ x, modKernelBilin V' W α α 𝔪 x g
    Ψ · ∂V'.quotMeasure), by simp [integral_add, map_add, (isRapid_modKernel V' W α α
    o (hP.2 · · |>.elim (by grind [invFirstRows_mul_firstCols σ ·])) _ g).integrable
    (by fun_prop [modKernel])]⟩, by simp⟩) (by simp [← hL, ← pairWeil_integrated _ _ α 1,
    thetaIntegral_pairWeil, mul_assoc]) (fun x Q h ↦ (hL .. ▸ hc _ _ hP _).trans
    (by simp [modKernel, modDatum, ← h, ← pairWeil_integrated_right α α, ← pairTheta_mul])) η
  erw [← hL, thetaIntegral, integral_quotMeasure_eq_classSum (f :=
    modKernelI W α 1 𝔪 Φ _ g) (pairThetaKer ..).swap.theta_rat_mul
    (fun _ ↦ integral_eq_const (.of_forall fun x ↦ ?_)) (Kf ..) ?_] at hκ
  rw [division_def α, ← one_mul β, ← mul_one α]
  simpa [↓modKernel_twist, ← mul_classSum, field] using hκ
  intro k m _; rw [modKernelI, modKernel_mul_Kf_right (k := ⟨k, m⟩), hα.apply_det]; congr with
  simpa [χ.inv_apply, Ring.inverse_inverse] using hP.left_mul (inv_mem (by simp [mem_intGL]))
  rw [modKernelI, modKernel, modDatum, ← hv x, ← pairWeil_integrated_right α, ← pairTheta_mul]
  repeat simp [negCount] <;> lia

attribute [local simp] carrierForm Modulus.disjoint_places_star Modulus.liftFn_one Space.lift
  name_boxIndicator carrierXi modDatum letterMinor stackedDetProd pairedDetProd matchedPoly
  pairTheta pairWeil

variable (E) {m : ℕ} [NeZero m]

/-- Let |m| = 2e > 0. Given c, some C works for all α of weight −c, tame for (𝔪, χ): some γ has
|γ|² = C/`lValueProd`(α⁻¹υ^e, e) and γ·Σ_h θ^{I_m,I_m}_{α,α}[χ∘det, ∏_τ det^{c_τ}](g, h) =
1 for all g (class sum, level K₀).

A class sum of a theta kernel as Hecke values. -/
lemma stdClassSum_det_modKernel_eq (he : Even m) (c : _ → ℕ) : ∃ C, ∀ {𝔪 α χ},
  IsTameFor 𝔪 α (-c ·) χ → ∃ γ, ‖γ‖ ^ 2 = C / lValueProd
  𝔪.places (α⁻¹ * upsilonU1 ^ (m / 2)) (m / 2) ∧ ∀ g, γ * stdClassSum (Kf E (Fin m))
  (modKernelI (stdSpace ..) α α 𝔪 (χ ·.det) (∏ τ, letterMinor τ id id ^ c τ) g) = 1 := by
  choose C H using explicit_matching (stdSpace E (Fin m)) (.sumEmpty Empty Empty) (stdSpace ..)
    (.emptySum ..) (.emptySum ..)
    (.sumEmpty ..) rfl (d := m / 2) (by simp; grind) (by simp; grind [NeZero]) (Fin <| c ·)
  refine' ⟨_, (H · (by simp) |>.imp' (· / ∫ _, 1 ∂quotMeasure (stdSpace E Empty)) fun γ ↦ .imp (by
    simpa [div_pow, ·] using div_right_comm ..) fun H g ↦ _)⟩
  field [measureReal_univ_ne_zero]
  convert! H 0 (partner_block _ _ 1) .. <;> simp [modKernel, vacElem_apply_eq_prod_lineTheta,
    @Subsingleton.eq_one (G ..), stackedDet,
    ← det_reindex_self (.emptySum ..), det_apply, ← Pi.one_def, funext_iff, prod_empty]

/-- Let m > 0 be even. For some C, every c of weight 0, tame for (𝔪, χ), has γ with
|γ|² = C/(nL(cυ^{m/2}, m/2)·nL(c⁻¹υ^m, m)) and γ·Σ_h `carrierXi`(h)·θ_{υ^m,c}[χ∘det, 1](x,
h) = `carrierForm`(x) for all x; nL = `lValueProd` at the places of 𝔪.

The carrier: one fixed form under all twists. -/
lemma stdClassSum_carrierXi_eq_carrierForm (he : Even m) : ∃ C, ∀ {𝔪 c χ}, IsTameFor 𝔪 c 0 χ →
  ∃ γ, ‖γ‖ ^ 2 = C / (lValueProd 𝔪.places (c⁻¹ * upsilonU1 ^ m) m * lValueProd 𝔪.places
  (c * upsilonU1 ^ (m / 2)) (m / 2)) ∧ ∀ x, γ * stdClassSum (Kf ..) (fun h ↦ carrierXi m c h *
  modKernelI (signedSpace ..) (upsilonU1 ^ m) c 𝔪 (χ ·.det) 1 x h) = carrierForm E m x := by
  let J := stdSpace E (Fin m)
  obtain ⟨⟨n, _⟩, ⟨C₁, H₁⟩, C₂, H₂⟩ := exists_modKernel_neg_left J J,
    stdClassSum_det_modKernel_eq E he 0, explicit_matching (J.sum (signedSpace
    E (1 ⊕ᵥ -1))) (.emptySum Empty _) J.neg 1 (.trans (.emptySum ..) (.sumComm ..)) (.sumAssoc _
    (Fin (2 * m)) _) (by aesop) (d := m) (by simp +arith) (by simp; grind [NeZero]) fun _ ↦ Empty
  use C₁ * C₂; introv h
  obtain ⟨_, ⟨γ₁, _, H₁⟩, γ₂, _, H₂⟩ :=
    (χ.isOfFinOrder 𝔪.normNegOne.isUnit.isOfFinOrder).norm_eq_one,
    H₁ h.inv, H₂ (h.mul (hasWeight_upsilonU1_pow m)) (by simp)
  use γ₂ * star γ₁ * n / χ 𝔪.normNegOne ^ m, by simp_all [pow_add, ↓mul_inv, field], fun x ↦ ?_
  have := explicit_matching_of_sum _ _ ((h.mul (hasWeight_upsilonU1_pow m)).mul .one) (P := ∏ τ,
    letterMinor τ Sum.inr id ^ (2 * m)) (by
    have := star_inj.2 <| H₁ <| G.neg.symm ·
    simp [J, map_classSum, *, Units.smul_def, ← χ.star_apply'] at this
    simpa [← smul_eq_mul, ← Pi.smul_def, ← modKernelBilin_apply, ← smul_assoc]) (unitModulus _)
    le_top 1 (by intros; simpa [det_apply, two_mul, ← tsub_tsub] using! H₂ 0 ‹_› 1 (.sum (_, x)))
  simpa [by simpa using (modKernel_sum_left J (stdSpace ..) c 1 _ · · 1 (χ ·.det) 1 1 · x),
    modKernel, mul_left_comm _ _⁻¹, mul_assoc, ← mul_classSum, field]
