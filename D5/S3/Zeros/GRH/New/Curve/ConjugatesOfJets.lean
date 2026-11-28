/- GID: D5/S3/Zeros/GRH/New/Curve/ConjugatesOfJets
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Curve/ConjugatesOfJets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Curve.ConjugatesOfJets. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/ConjugatesOfJets.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Curve.IntegralVacuum
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.TestRings
import D5.S3.Zeros.GRH.Lib.CM.Reciprocity.SemilinearWeilLaw
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Also holds known results stated on this proof's data: Galois action on CM theta functions and on
the finite Weil representation (known result; see Lib.CM.Reciprocity.SemilinearWeilLaw).

Part of: Tight frames and an integral standard theta function (see New.Curve.FrameSections).

This file: Standard data: stability, and p-adic bounds transfer from theta products to their jets.
Scaled jets of standard theta data are integral at every prime. One theta lift raises valuations by
the bound on jets of standard data. Galois conjugation of theta jets as semilinear map on Weil
space, with size bounds. -/

open CMLattice Fintype Function stdLattice LinearMap Matrix MvPowerSeries NeZero Real Space
  Submodule Subtype

variable {P s n n'} [Fintype n] [Fintype n'] {κ e ea eb c K} {a b : AutChar (Parameters.E P s)} {ψ
  ψ'} {ha : a.HasWeight ea ψ} {hb : b.HasWeight eb ψ'} {p : ℕ} [Fact p.Prime] [PadicPlace p] {hκ :
  IsLiftWeight n n' κ eb e} {S} [AddCommGroup S] [Module ℂ S] (k : Kernel n n' κ e ea K S) {ε :
  n → ℤˣ} (V : Space (Parameters.E P s) n ε)

namespace Parameters

lemma integralAfter.of_integral {n} [Fintype n] {δ S} : stdLattice (E P s) n ≤ integralAfter δ S :=
  fun _ h i w _ ↦ mem_Ô.1 (mul_mem (coe_mem_Ô (algebraMap _ _ δ)) (h i)) w

/-- The module `Parameters.standardData` of standard data for V and δ at a p-adic place is stable
under the operators `Space.finHeisOp` x, for finite adelic vectors x with δx integral at every place
above p. -/
lemma finHeisOp_mem_standardData {P s n} [Fintype n] {ε} {V : Space (E P s) n ε} {p : ℕ} [q :
  Fact p.Prime] [PadicPlace p] {δ f x} (h : x ∈ integralAfter δ (↑p ∈ ·.1)) : f ∈ standardData V δ →
  V.finHeisOp x f ∈ standardData V δ := by
  apply span_induction <;> simp_all [add_mem, smul_mem, finHeisOp_finHeisOp]
  use fun _ k ↦
    smul_mem _ (⟨_, (norm_map_psi₀ ..).le⟩ : embValRing) (subset_span ⟨_, add_mem h k, rfl⟩)

/-- If the finite adelic unitary element g is integral above p, then ω(1, g) maps the standard
data `Parameters.standardData` of V, for ι: ℂ → ℂ_p and δ, into itself. -/
lemma omega_mem_standardData {ε} {V : Space (E P s) n ε} {p : ℕ} [q : Fact p.Prime] [PadicPlace p]
  {δ f g} (hg : g ∈ integralAbove n p) (hf : f ∈ standardData V δ) : V.ω (1,
  g) f ∈ standardData V δ := have m {x} (h : x ∈ integralAfter ..) :
    g.1.1 *ᵥ x ∈ integralAfter .. := fun i w e ↦ by simpa [Finset.mul_sum,
    mulVec, dotProduct, mul_left_comm] using! (mulVec_mem_intVectors_iff (hg w e)).2 (h · w e) i
  span_induction (by simp [intVacuum, omega_vacElem_sum,
    smul_comm (_ ^ _)]; exact fun _ h ↦ smul_mem _ (⟨_, show ‖_‖ ≤ 1 by simp_all
    [norm_finMultiplier_eq_one, ← Complex.mul_conj', ← finMultiplier_inv]⟩ : embValRing) (by
    simpa only [← map_smul, smul_finsum] using! finHeisOp_mem_standardData (m h) (finsum_induction _
      (by simp) (by bound) fun q ↦ subset_span ⟨_, m (integralAfter.of_integral q.out.2), rfl⟩)))
    (by simp) (by aesop) (by aesop) hf

/-- Let V be standard, f standard data for ι and δ, and L a ℂ-linear form on power series. If |ι
L(Θ)| ≤ r whenever ιΘ is a theta product in `Parameters.thetaProducts` with scale c·s₁, then |ι L| ≤
r at the Taylor series of f scaled by c·per. -/
lemma norm_jetSeries_le {ε} {V : Space (E P s) n ε} {p : ℕ} [q : Fact p.Prime] [PadicPlace p] {δ f}
    [V.IsStd] (hf : f ∈ standardData V δ) c (L : _ →ₗ[ℂ] ℂ) {r : NNReal} (H : ∀ Θ,
  .map ιₚ Θ ∈ P.thetaProducts s δ ‖ιₚ (c * P.periodFactor s)‖ n → ‖ιₚ (L Θ)‖ ≤
  r) : ‖ιₚ (L (V.jetSeries (c * P.jetScale s) f))‖ ≤ r := by
  let M := p * (P.d * P.N₁ s) ^ 6 + 1
  obtain ⟨hM, _, _, w, k, hw, -⟩ := (by simp [M] : p.Coprime M), P.exists_isTightFrame s (by
    unfold M; grw [← q.1.one_le]; lia : _ * 1 ≤ M * M)
  obtain ⟨F, hW, hF, -, K, y, _, hy, _, hs⟩ := exists_finitePart_of_isTightFrame V M (by simp :
    M * M ≠ 0) (by simp) hw.repeat_vectors (fun _ ↦ (1, 0)) (by simp) omega₀_mem_cmCurve_lattice
    (by simp [QuadField.area_eq_of_eq_scaledIdeal latticeModule_cmCurve])
  apply span_le (p :=
    (Valuation.leSubmodule _ r).comap (.restrictScalars _ (L ∘ₗ V.jetSeries _))).2 _ hf
  rintro _ ⟨x, h, rfl⟩
  simp_rw [intVacuum, ← by simpa [by simpa [monomialSection] using hF 0, mul_div_cancel₀, *] using
         hs <| (P.vacuumScale s ^ card n / card K) • V.θ, map_sum, map_smul]
  refine sum_mem fun j _ ↦ smul_mem _ (⟨_, mul_mem (by simp) (by simpa [hM.norm_natCast_eq_one,
    intVacuum] using norm_intVacuum_le_one : ‖_‖ ≤ 1)⟩ : embValRing) (?_ : ‖_‖ ≤ r)
  have ⟨γ, hγ, e⟩ := exists_finiteImage_approx hW (x + -y j)
  simp [finHeisOp, semichar, ↓rho_finVec, ← e]
  have ⟨_, h', hN⟩ := exists_forall_mul_mem_Ô (finiteImage (algebraMap P.K _ δ * M • γ ·))
  obtain ⟨_, m, _, ⟨⟩⟩ := WfDvdMonoid.max_power_factor h' q.1
  use H _ ⟨_, _, _, _, m * M * M, _ / M / _ * (_ * _), _, hw.repeat_vectors, by
    simp [hF, PowerSeries.map_subst, linearSeries, smul_eq_C_mul, apply_ite, monomialSection]
    rfl, by grind [q.1.dvd_mul, q.1.coprime_iff_not_dvd], by simp [hM.norm_natCast_eq_one, jetScale,
    field], fun (i, t) ↦ by convert neg_mem (mul_mem_of_quadInt _ (herm_mem_quadInt (_ * m • M • _)
    (mem_Ô.2 fun w ↦ by_cases (by simpa [finiteImage, add_sub, -smul_eq_mul] using nsmul_mem
                                    (sub_mem (nsmul_mem (add_mem h (integralAfter.of_integral hγ))
    M) (integralAfter.of_integral (hy j))) m t w ·) (by simpa [by simpa using v_algebraMap_eq_one ·,
    finiteImage, (mul_left_comm _ m.cast)] using (mem_Ô.1 (hN t) w))) (hw.1 i.1))
    omega₀_mem_cmCurve_lattice); simp [← Finset.mul_sum, mul_assoc, field]⟩

/-- Integrality of jets: for V standard, 0 ≠ δ ∈ 𝓞_K, f in the module `Parameters.standardData` of δ
and Q' a complex polynomial with coefficients in ι⁻¹𝔬, the jet along Q' of the Taylor series of f
scaled by δ̄·d·per has |ι(·)|_p ≤ 1. -/
lemma norm_jet_jetSeries_le_one {P s n} [Fintype n] {ε} {V : Space (E P s) n ε} [V.IsStd] {p}
  [Fact p.Prime] [PadicPlace p] {δ} (h0 : δ ≠ 0) {f} (hf : f ∈ standardData V δ) {Q Q'} : .map
  embValRing.subtype Q = Q' → ‖ιₚ (jet ℂ Q' (V.jetSeries (star ↑δ * P.d * P.jetScale s) f))‖ ≤ 1
  | rfl => norm_jetSeries_le hf _ _ (r := 1) fun _ ⟨_, _, _, _, m, _, _, hw, _, hk, _, hy⟩ ↦ by
    have := hk.2.norm_natCast_eq_one ℂ_[p]
    simpa [map_jet, *] using! P.cmCurve.jet_theta_prod_integral (by simpa [apply_ite, ite_apply,
      field, *, ne] using (fun _ _ ↦ norm_periodFactor_mul_conj_le_one (hw.1 _))) ⟨m * δ,
      rfl⟩ (by clear * - h0 this; aesop) hy Q

/-- The additive monoid of data Φ such that, for all g, h, ξ, the gauge of ker(ω(g,h)Φ)ξ at hd'
is at most max(c,0) times the gauge of ξ at gd. -/
def _root_.Kernel.raises d d' c := show AddSubmonoid S by
  use! {Φ | ∀ g h ξ, weylGauge _ ea (h * d') (k.jetMatrix (k.ω (g, h) Φ) ξ) ≤ max c 0 * weylGauge κ
    e (g * d) ξ} <;> simp_all [weylGauge, (IsUltrametricDist.norm_add_le_max ..).trans, mul_nonneg]

/-- If the kernel of the datum Φ multiplies the gauges at ι, read at d and d', by at most c
(`Kernel.raises`), then that of zΦ multiplies them by at most ‖ι(z)‖·c. -/
lemma _root_.Kernel.smul_mem_raises {c' Φ d d' z} (h : Φ ∈ k.raises d d' c) (H : ‖ιₚ z‖ * c ≤ c') :
    z • Φ ∈ k.raises d d' c' := by intro _ _ _; simp [weylGauge_smul]; grw [h ..,
  ← H] <;> simp [weylGauge, mul_max_of_nonneg, ← mul_assoc]

/-- For characters a, b with given weights and tame parts, the action ω of a pair (g,h) of
finite points integral above p preserves the set Std_δ of data on Hom(I_n, I_{n'}) at ι. -/
lemma pairWeil_mem_standardData {δ f} (ha : a.HasWeight e ψ) (hb : b.HasWeight ea ψ') (hf :
  f ∈ standardData _ δ) {g h} (hg : g ∈ integralAbove n p) (hh : h ∈ integralAbove n' p) :
  pairWeil (stdSpace ..) (stdSpace ..) a b ((1, g), 1, h) f ∈ standardData _
  δ := (standardData ..).smul_mem ⟨_, show ‖_‖ ≤ 1 by simp [AutChar.HasWeight.norm_padic_det, *]⟩
  (G.onHom_fin g h ▸ omega_mem_standardData (by simp_all [localLevel]) hf)

/-- Theta kernel of scale c, Ψ in Std_δ, x, y integral above p, d equal to diag(u_τ) under
`adeleExtension` at each τ. If all jet entries of all f in Std_δ, weighted by the u_τ, have
p-adic norm ≤ B, then ω(1, xdy)Ψ multiplies gauges by at most max(B, 0). -/
lemma mem_raises_of_jet_bound {Ψ δ} (hΦ : Ψ.1 ∈ standardData _ δ) {x d y} (hx :
  x ∈ integralAbove _ p) (hy : y ∈ integralAbove _ p) {u : _ → _} (hu : ∀ τ, d.1.1.map
  (adeleExtension (weightEmbedding ιₚ τ)) = diagonal (u τ)) {B} (h : ∀ f ∈ standardData _ δ, ∀ i' i,
  (∏ τ, (∏ b, ‖u τ b‖) ^ ea τ * ∏ h, ∏ j, ∏ t, ‖u τ ((i' τ).1 h j t)‖) * ‖ιₚ (schurJet κ
  (((stdSpace _ n).hom (stdSpace ..)).jetSeries c f) i' i)‖ ≤ B) : let k := thetaKernel hκ c ha hb K
  k.ω (1, x * d * y) Ψ ∈ k.raises 1 1 B := fun g g' ξ ↦ by
  obtain ⟨⟨γ, k, -⟩, ε, _, hd⟩ := exists_mul_mem_integralAbove p g 1,
    exists_mul_mem_integralAbove p (g' * x * d) d
  rw [← weylGauge_embFin, ← Kernel.equivariant _ γ ε, ← weylGauge_mul _ (div_mem hx hd),
    ← weylGauge_embFin _ γ, ← weylGauge_mul _ (inv_mem k)]
  simp_all (maxDischargeDepth := 4) [-smul_mulVec, thetaKernel, rep_apply_apply, ιₚ.map_mulVec,
    ← mul_assoc, weylGauge, comp_def, weylRep, norm_mulVec_le, Units.smul_def, mul_mem,
    schur_diagonal_eq_prod, pairWeil_mem_standardData ha hb]

/-- For a theta kernel of scale c·per and δ ≠ 0, a datum Φ ∈ Std_δ multiplies gauges at ι by at
most |ι(c)/ι(δ̄d)|^L, L the number of boxes in columns of κ of height below the rank n'. -/
lemma mem_raises_of_standardData {Φ δ} (h0 : δ ≠ 0) (hΦ : Φ.1 ∈ standardData _ δ) :
  Φ ∈ (thetaKernel hκ (c * P.jetScale s) ha hb K).raises 1 1 ((‖ιₚ c‖ / ‖ιₚ (star ↑δ * P.d)‖) ^
  boxes κ (card n')) := by
  have := ne P.d; convert mem_raises_of_jet_bound hΦ (x := 1) (d := 1) (y := 1) (u := 1) _
    _ _ fun _ hf i' i ↦ .trans _ (mul_le_of_le_one_left (a := ‖ιₚ
    (schurJet κ _ i' i)‖) _ (norm_jet_jetSeries_le_one h0 hf (.trans (map_schur hκ.1 (.X ⟨·, ·,
    ·⟩) _ i' i) _))) <;> simp [field, *, mul_pow, div_pow, schurJet_jetSeries_eq_smul hκ (_ * _)]

/-- If d·f lies in `Parameters.standardData` N, c is p-adically integral, and d(N·P.d)^L divides M,
L = `boxes` κ |n′|, then the theta kernel of scale c·per with datum M·f does not increase
p-adic gauges (`Kernel.raises`). -/
lemma mem_raises_of_dvd {N d M : ℕ} [NeZero N] f (hf :
  (d : ℂ) • f.1 ∈ standardData _ N) (hc : ‖ιₚ c‖ ≤ 1) (hM : d * (N * P.d) ^ boxes κ (card n') ∣ M) :
  (M : ℂ) • f ∈ (thetaKernel hκ (c * P.jetScale s) ha hb K).raises 1 1 1 := by
  rw [hM.choose_spec, mul_rotate, Nat.cast_mul, mul_smul]
  use Kernel.smul_mem_raises _ (mem_raises_of_standardData out hf)
    (by have := @ne ℕ _; grw [hc]; simp [IsUltrametricDist.norm_natCast_le_one, mul_pow, field, *])

attribute [local simp] smul_eq_C_mul IsJetConjugate

/-- Conjugates of jets. For V standard of rank n, R ∩ R̄ = ∅ and σ ∈ Aut(ℂ/K), there are |t|² =
1/Ω, c ≠ 0, a norm-one finite adele z and a σ-semilinear L such that: for f in 𝒲_f and
finite g, σ(T_per f) = T_t(Lf) (places permuted) and Lω(g)f = (σΔ(g)/Δ(g))ω(g)Lf;
|Lϱ(αx)ω(g)θ°| ≤ exp(C(N₁n+1)²) everywhere, C = `Parameters.c`; L(Ψ⊗vac) = cω(z)(σΨ⊗vac) for Ψ
Schwartz–Bruhat above R. Here T_a = `Space.jetSeries` a and per = `Parameters.jetScale`.

Known result: Galois action on CM theta functions and on the finite Weil representation. -/
lemma exists_semilinear_isJetConjugate [i : V.IsStd] {R} (hR : Set.IsConjDisjoint R)
  (σ : Gal(ℂ/Parameters.K P)) : ∃ t c z, ∃ L : _ →ₛₗ[(σ : ℂ →+* ℂ)] _, ‖t‖ ^ 2 = (P.bigOmega s)⁻¹ ∧
  c ≠ (0 : ℂ) ∧ (∀ f ∈ V.finitePart, IsJetConjugate σ (placePerm s σ) (P.jetScale s) t f (L f)) ∧
  (∀ᵉ (f ∈ V.finitePart) (g), L (V.ω (1, g) f) = multiplierRatio σ g • V.ω (1, g) (L f)) ∧
  (∀ x g y, ‖L (V.ϱ (finVec x) (V.ω (1, g) (intVacuum V))) y‖ ≤
  exp (P.c * (P.N₁ s * card n + 1) ^ 2)) ∧ ∀ Ψ, IsSchwartzBruhat R Ψ → L (V.name R Ψ V.vacElem) =
  c • V.ω (1, scalarFin n z) (V.name R (σ ∘ Ψ) V.vacElem) := by
  cases i.1
  choose B _ _ W h₀ sp t _ W' ht hJ using P.exists_isJetConjugate_generator.choose_spec s
  let L := (((rename ((placePerm s σ).symm.prodCongr 1)).toLinearMap ∘ₗ V.jetSeries
    (t V σ)).domRestrict V.finitePart).leftInverse ∘ₛₗ .mk (R := ℂ) (σ :=
    σ) ⟨MvPowerSeries.map σ ∘ V.jetSeries (P.jetScale s), by simp⟩ (by simp)
  have key x : L _ = _ := (congrArg _ (hJ V σ x)).trans (leftInverse_apply_of_inj (ker_eq_bot'.2
    (coe_inj.1 <| eq_zero_of_jetSeries_eq_zero ·.2 (by grind [bigOmega_pos, norm_zero]) <|
    (renameEquiv ..).map_eq_zero_iff.1 ·)) ⟨_, rho_finVec_mem_finitePart _ (W' ..)⟩)
  have Wv : intVacuum V ∈ _ := V.finitePart.smul_mem _ (by simp)
  refine have hψ z := ?_; have hϱ := ?_; have h := ?_
        have e x := by simpa [hϱ, Wv, rho_finVec_mem_finitePart]
          using congr(constantCoeff $(h _ (rho_finVec_mem_finitePart x Wv)))
        (semilinear_intertwines_weil (B σ) hR hψ hϱ).elim fun hB ⟨k, o, hk, hω, hn⟩ ↦ ⟨_, k, o,
          V.finitePart.subtype ∘ₛₗ L, ht V σ, (exists_intVacuum_ne_zero.choose_spec <| by
          simpa [·, hk, intVacuum] using e _), h, hω, fun x g y ↦ ?_, hn⟩
  choose n h H using exists_natCast_smul_mem_of_isCompact (P.E s) (Set.toFinite {1,
    B σ • 1}).isCompact (((isLocallyConstant_rho_finVec (W (stdSpace _ Unit))).prodMk
    (isLocallyConstant_rho_finVec (W' (stdSpace ..) σ))).eventually_eq _)
  obtain ⟨⟨x, rfl⟩, e, e'⟩ := (isUnit_natCast_finAdele h).dvd (a := z), by simpa [eq_comm] using H
  have k := e.1 ▸ e'.2 ▸ hJ _ σ (x • 2)
  simp [↓rho_finVec, ← hJ, ← smul_add, smul_comm _ (B σ)] at k ⊢
  grind [eq_zero_of_jetSeries_eq_zero, rho_finVec_mem_finitePart, jetScale_ne_zero,
    Heisenberg.Rep.norm_map, norm_eq_zero]
  any_goals refine fun f h ↦ span_induction ?_ ?_ ?_ ?_ (sp V h) <;> simp +contextual [*,
    -Heisenberg.Rep.mul, rho_finVec, mul_left_comm half, mul_assoc]
  have k :=
    sqrt_le_sqrt (norm_dataInner_le (hB.smul_bijective.2.forall.2 (e · ▸ norm_intVacuum_le σ)))
  grw [c, ← le_add_of_nonneg_right (by positivity)]; set C := Exists.choose _
  simp [*, rep_apply_apply, intVacuum, omega_mem_finitePart, smul_smul, sqrt_mul_self_eq_abs, by
    simpa [WeilData.upsilonU1_hasWeight.norm_map_eq_one,
      funext_iff] using congr(√‖$(multiplierRatio_sq σ g)‖)] at k ⊢
  -- The supremum of the unit vacuum `ω g vacElem`.
  set g := (_, g * _); clear * - k
  let T := {γ | ∀ i, WeilData.α⁻¹.1 * ((V.move g).vecAtPoint γ i).2 ∈ Ô _}
  choose hs hl using tsum_le_of_separated (I := T) one_pos (Nat.cast_nonneg _)
    (fun γ δ _ ↦ (one_le_firstMinimum).trans (map_sub (V.move g).archCoords .. ▸ firstMinimum_le (by
    simpa [WeilData.α, baseLattice, ↓← nsmul_eq_mul, mul_sub] using fun i ↦ mul_mem P.N₁_mul_α_mem
      (sub_mem (γ.2 i) (δ.2 i))) (by simpa [-nsmul_eq_mul, ne, sub_ne_zero, coe_inj]))) (fun _ ↦
    one_le_exp (norm_nonneg _)) (by grw [map_nsmul, norm_nsmul_le, lt_add_one ‖archCoords _ ·‖,
    add_one_le_exp]) (lt_add_one _) (by simpa using add_one_le_exp _)
  set D : ℝ := Nat.cast _ + 1
  grw [k, ← θ_ϱ, norm_eq_sqrt_real_inner, Complex.inner, Complex.re_le_norm,
    (hasSum_dataInner ..).norm_le_of_bounded ((hasSum_extend_zero val_injective).2
    (hs.hasSum.mul_left (√P.d * D ^ 2).exp)) fun γ ↦ ?_, hl, add_comm, add_one_le_exp]
  simp [← exp_nat_mul, ← exp_half, ← exp_add, field]
  grw [← numInfPlaces, card_infinitePlace_E, Nat.totient_le, sqrt_le_self_iff.2 (mod_cast by lia),
    ← sub_nonneg]
  cases card n <;> rify <;> ring_nf <;> bound
  by_cases γ ∈ T <;> simp_all [T, -Heisenberg.Rep.mul, ϱ_swap _ _ (y + _),
    vacuumFn, -Complex.ofReal_exp, ← exp_mul, WeilData.j, dataInner_omega_left, ω_ϱ,
    rep_apply_apply, ← move_vecAtPoint, ← sum_prod_type_right',
    ← exp_add, ← Finset.mul_sum, extend_val_apply, sqrt_div_self]
  field [pos]
  erw [← (archCoords _ γ).norm_sq_eq]; nlinarith [two_le_pi,
    sq_nonneg (‖(V.move g).archCoords γ‖ - √P.d * D)]
