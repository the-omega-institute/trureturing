/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/FourierCoefficient
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/FourierCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.FourierCoefficient. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/FourierCoefficient.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.SiegelWeil.SingularForms.AdaptedHom
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.KernelDecay
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

Part of: Fourier coefficients of theta lifts as periods over stabilisers (known result; see
Lib.Shimura.ComplexTheta.PeriodVanishing).

This file: Real mixed model of an adapted splitting; slices factor into real and finite parts.
Mixed-model terms of a theta kernel: equivariance, moderate growth, integrability for onto data.
Fourier coefficient of a theta lift as sum over frames, unfolded by Witt. -/
seal Finset.univ Finset.sum Finset.prod

section

open Matrix NumberField WeilData Space Splitting Prod MatMul Heisenberg IsVacuum
variable {E} [Field E] [CMType E] [WeilData E] {n n₀ p : Type} [Fintype n] [Fintype n₀] [Fintype p]
  {s s₀} {V : Space E n s} {V₀ : Space E n₀ s₀} {D : V.Splitting V₀ p} {t} (h : D.IsAdapted 1 t)

@[simp] lemma scaleIdele_ne_zero v : (scaleIdele E).1.1 v ≠ 0 := Units.ne_zero _

/-- For an adapted splitting, the non-zero constant c by which the mixed model sends the vacuum
to c times a Gaussian factor times the vacuum of the smaller space. -/
noncomputable def vacuumFactor := Units.mk0 _ h.mixedTerm_omega_vacElem.choose_spec.1

include h

lemma eq_of_integrated_zeroTerm_eq {v u} (e : ∀ f, V₀.integrated v (D.zeroTerm (V.projReal f)) =
  V₀.integrated u (D.zeroTerm (V.projReal f))) :
  v = u := sub_eq_zero.1 (eq_zero_of_modelInner_self (by
  obtain ⟨⟨⟩, _⟩ := h.mixedTerm_omega_vacElem,
    V₀.dataInner_integrated (v - u) (v - u) V₀.vacElem V₀.vacElem, e V.vacElem
  simp_all [-sub_eq_zero, ← mixedTerm_zero, vacuumFn]))

attribute [local simp↓] realVec_realMatrix_mulVec integrated_realHeisOp mixedTerm fst_sum
  conjTranspose_nonsing_inv adelicHeis star_mulVec_dotProduct

/-- The mixed Schrödinger–Fock model at the real places of a splitting D whose frames, in the
basis t, are orthonormal at infinity and integral. -/
@[local simp] noncomputable def Space.Splitting.IsAdapted.mixedModel :
    MixedModel (realSigns E s) (realSigns E s₀) (InfinitePlace E × p) := by
  choose T e using by simpa using h.exists_real_zeroTerm isMixedLaw_mixedTerm
  use realMatrix (D.lAdelic * t⁻¹.1ᴴ), realMatrix (D.kAdelic * t.1), realMatrix D.iAdelic,
    (T.comp <| realHeisOp <| realMatrix (D.lAdelic * t⁻¹.1ᴴ) *ᵥ ·), ⟨realMatrix (t.1ᴴ * D.lCoord),
    realMatrix _, realMatrix (t⁻¹.1 * D.kCoord), fun y ↦ Function.Injective.of_ker realVec (by
    simp_all [realVec, funext_iff])
    (by simpa [↓map_add] using! congr($D.symm.sum_frame_mul_coord_eq_one *ᵥ _))⟩
  all_goals intros; apply eq_of_integrated_zeroTerm_eq h
  erw [← (by simpa using (adelicSum E (n := p) 1).2 ⟨·, 0⟩ ⟨·, 0⟩ :)]
  simpa [← e, -Rep.mul] using fun _ ↦ D.isMixedLaw_mixedTerm (t⁻¹.1ᴴ *ᵥ _) (D.lAdelic *ᵥ t⁻¹.1ᴴ *ᵥ
    _ + D.iAdelic *ᵥ _ + D.kAdelic *ᵥ t.1 *ᵥ _) _
  simpa [← e] using h.omega_projReal_of_isMixedLaw isMixedLaw_mixedTerm _

/-- For a splitting D with the point 1 adapted to t, the zero term of v ⊗ f is v[0] ⊗ ev(f°),
with v[0] the slice at 0 in the real mixed model and f° the real vacuum projection of f. -/
lemma zeroTerm_integrated : ∀ v f, D.zeroTerm (V.integrated v f) =
  V₀.integrated (h.mixedModel.slice 0 v) (D.zeroTerm (V.projReal f)) := by
  simpa using (h.exists_real_zeroTerm isMixedLaw_mixedTerm).choose_spec

lemma mixedTerm_integrated x v f : D.mixedTerm (t⁻¹.1ᴴ *ᵥ x) (V.integrated v f) =
  V₀.integrated (h.mixedModel.slice (realCoord x) v) (D.mixedTerm (t⁻¹.1ᴴ *ᵥ (0, x · |>.2))
  (V.projReal f)) := by simp (disch := simp [mulVec_eq_sum]) [← rho_integrated _ v, rho_integrated _
  IsVacuum.vacElem, ← by simpa using zeroTerm_integrated h, ← mulVec_add, realVec_realCoord_add]

end

namespace Space.Splitting

open Complex Matrix ENNReal ContinuousLinearMap MeasureTheory MatMul
variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n n' n₀ p} [Fintype n] [Fintype n'] [Fintype n₀] [Fintype p] {s s' s₀} {S : Space E n s} {S₀ :
  Space E n₀ s₀} (D : S.Splitting S₀ p) (T : Space E n' s') (a b f g γ) (x : Matrix n' p E) (h)

/-- For split S and a rational matrix x, the term θ((ω_{a,b}(g,h)f)[x_T⁻¹x]) of the theta
kernel, x_T the point of T, [·] being the mixed model along the isotropic subspace spanned by k. -/
noncomputable def thetaTerm :=
  θ _ (D.sourceTerm T (T.x⁻¹.1 * x.map toAdele) (pairWeil S T a b (g, h) f))

/-- The property that h ↦ Σ_x |θ((ω_{a,b}(g,h)f)[x_T⁻¹x])·y(h)|, summed over rational matrices x,
has finite integral over [U(T)]; by default y = 1. -/
abbrev HasIntegrableTerms (y : _ → ℂ :=
  fun _ ↦ 1) := ∫⁻ h, ∑' x, ‖(delta% D.thetaTerm T a b f g x h) * y h‖ₑ ∂T.quotMeasure < ⊤

/-- For split S and a rational n′×p matrix x put T_x(h) = θ((ω_{a,b}(g,h)f)[x_T⁻¹x]), x_T the
point of T (`Space.Splitting.thetaTerm`). Then T_{γx}(γh) = T_x(h) for every rational γ in U(T),
embedded in the adelic group, and every adelic h. -/
lemma thetaTerm_ratEmbed_mul : (delta% D.thetaTerm T a b f g (γ.1.1 * x)
  (T.ratEmbed γ * h)) = delta% D.thetaTerm T a b f g x h :=
  by erw [← one_mul g, ← Prod.mk_mul_mk, ← rep_apply_apply, ← div_mul_cancel a, ← D.levi.map_one,
  sourceTerm_levi, ← map_inv, map_smul, ratMap_mul_toAdele, pairWeil_of_mem_Gamma] <;> simp [Γ]

/-- For split S and fixed g, there are C ≥ 0 and B such that Σ_x |θ((ω_{a,b}(g,h)f)[x_T⁻¹x])| ≤
C‖f‖·ht(h)^B for all f and h, the sum running over rational matrices x. -/
lemma exists_tsum_thetaTerm_le : ∃ C B, ∀ f h, tsum (‖delta% D.thetaTerm T a b f g · h‖ₑ) ≤
  .ofReal (|C| * ‖f‖ * T.height h ^ B) := ⟨‖θ _‖ * (_ : NNReal) * _, _, fun f h ↦ by
  obtain ⟨_, ⟨δ, ⟨⟩⟩, e⟩ := ((pairThetaKer ..).exists_rat_norm_le_height g).exists.choose_spec h
  grw [abs_mul, abs_pow, abs_two, mul_right_comm, mul_assoc |_|, ← e]
  conv_rhs => simp [mul_assoc]
  grw [← le_opENorm, ← (D.homSource T).tsum_enorm_mixedTerm_le.choose_spec,
    ← tsum_comp_le_tsum_of_injective
  (Function.uncurry_injective.comp (mul_right_injective_of_invertible δ)), ← ENNReal.tsum_mul_left]
  gcongr; grw [← thetaTerm_ratEmbed_mul, sourceTerm_eq_mixedTerm, le_opENorm]; rfl⟩

/-- Let S be split, P ∩ P̄ = ∅, Ψ Schwartz–Bruhat above P, all moments of v finite, y·(g⁻¹x⁻¹(k,
i))_f right invertible after φ: 𝔸_f → R ≠ 0 whenever Ψ(y) ≠ 0. For f = v⊗Ψ⊗vac, h ↦ ∑_{ξ
rational} |θ((ω_{a,b}(g,h)f)[x_T⁻¹ξ])| has finite integral over [U(T)]. -/
lemma hasIntegrableTerms_integrated_name {P} (hP : P.IsConjDisjoint) {Ψ} (hΨ : IsSchwartzBruhat P Ψ)
  {v R} [CommRing R] [Nontrivial R] (φ : _ →+* R) (hv : IsRapidDatum v) {g} (h : ∀ y, Ψ y ≠ 0 →
  HasLeftInv ((vecToMat y * (S.coordMatrix g (D.k.fromCols D.i)).map (·.2)).map φ)ᵀ) :
  D.HasIntegrableTerms T a b (integrated _ v (name _ P Ψ (vacElem _))) g := by
  obtain ⟨⟨C, B, H⟩, d, hd, o⟩ := D.exists_tsum_thetaTerm_le T a b g, exists_forall_mul_mem_Ô
    (matToVec (S.coordMatrix g (D.k.fromCols D.i)) · |>.2)
  choose u _ e using exists_norm_eq_mul_self
  exact IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _ ⟨_, fun k ↦ tsum_le_of_sum_le'
  bot_le fun t ↦ .trans (by simpa [← ofReal_norm, ← ofReal_sum_of_nonneg] using ((re_le_norm
    _).trans_eq congr(‖∑ _ ∈ t, $(e _)‖)))
    (ofReal_mono ((exists_norm_name_le a b hP vacElem_mem_finitePart 0
  ..).choose_spec v g k (∑ _ ∈ t, u _ • θ _ ∘L _) 1 _ (hv _) le_rfl (height_pos k) (by
  simp_intro ..; grw [norm_sum_le, ← ofReal_le_ofReal_iff, ← H, ← ENNReal.sum_le_tsum t]
  simp [*, ofReal_sum_of_nonneg]; bound [T.height_pos k])
  (T.exists_short_isotropic · |>.imp fun _ ⟨h0, i, e⟩ ↦ ⟨(d : E) • _, _, _, e, fun j ↦ ⟨by
  intro; erw [LinearMap.map_smulₛₗ, move_vecAtPoint]; simpa using! o ⟨_, _⟩, by
    apply norm_le_pi_norm _ j⟩, by linarith, .inl i, by simp [← coe_units_inv, -conjTranspose_mul,
    sourceTerm_varrho, kAdelic, lAdelic, iAdelic, ratMap_mul_ratMap, ↓gram_at_point_eq_map,
    ← map_mul, Matrix.mul_add, ← AddMonoidHom.map_trace, ← map_add, Matrix.mul_assoc,
    ← S₀.vecAtPoint_hom, -matToVec_smul], .inl (by
    simpa [coordMatrix, Nat.cast_smul_eq_nsmul, Matrix.map_smul, ← ext_iff, (isUnit_natCast_finAdele
      hd).mul_right_eq_zero] using T.coordMatrix_mul_ne_zero h0 1 <| h · ·)⟩)))⟩

variable {E n n₀ : _} {m} {p : _} [Field E] [CMType E] [H : WeilData E] [Fintype n] [Fintype n₀]
  [Fintype m] [Fintype p] {s s₀ : _} {t} {W : Space E n s} {W₀ : Space E n₀ s₀} (D :
  W.Splitting W₀ p) {V : Space E m t} {a b f g : _} {y} (hi : D.HasIntegrableTerms V a b f g y)

/-- What acts on columns acts on frames. -/
instance (priority := low) {M R} [Monoid M] [MulAction M (m → R)] : MulAction M (Matrix m p R) :=
  (Equiv.piComm _).mulAction M

include hi

/-- For continuous y with absolutely convergent unfolded theta integral at g
(`Space.Splitting.HasIntegrableTerms`), the Fourier coefficient at ȷβ and g of its lift from U(V) to
U(W) is the sum, over rational x with xᴴJx = β, of the integrals of the x-term times y. -/
lemma centreCoeff_integral_eq_tsum β (hy : Continuous y := by fun_prop) :
  D.centreCoeff (H.j • β) (∫ h, pairTheta W V a b f ⟨·, h⟩ * y h ∂V.quotMeasure) g = ∑' x :
  {x | xᴴ * V.J * x = β}, ∫ h, (delta% D.thetaTerm V a b f g x.1 h) * y h ∂V.quotMeasure := by
  rw [isDualFamily_ratMatrices.tsum_coeff_eq_quotMean (fun x ↦ -H.j • (xᴴ * V.J * x) + H.j • β)
    (by simp [neg_add_eq_zero]) (hasSum_integral_of_lintegral hi).summable]
  simp_rw [centreCoeff, pairTheta, ← (D.hasSum_theta_sourceTerm ..).tsum_eq, ← tsum_mul_right,
    ← integral_const_mul, ← tsum_mul_left, isDualFamily_ratMatrices.2]
  congr with z; rw [(hasSum_integral_of_lintegral (by
    simp_all [← ofReal_norm])).tsum_eq]; congr! 4 with _ h
  erw [← one_mul h, ← Prod.mk_mul_mk, ← rep_apply_apply, sourceTerm_radicalElt,
    gram_at_point_eq_map]
  simp [trace_mul_comm z, ← mul_assoc, ← map_mul, ↓map_smul', field, mul_comm _ H.j]

/-- Unfolding: let y be continuous, left Γ-invariant, satisfying
`Space.Splitting.HasIntegrableTerms`, x₀ rational with invertible Gram matrix β, S the rational
stabiliser of x₀. The x₀-term times y is S-invariant, integrable modulo S, with integral the Fourier
coefficient at ȷβ and g of y's lift.

Known result: Fourier coefficients of theta lifts as periods over stabilisers. -/
lemma centreCoeff_eq_integral_stabilizer {x₀} (h₀ : IsUnit (x₀ᴴ * V.J * x₀)) {S : Subgroup _} (hS :
  ∀ k, k ∈ S ↔ ∃ γ, γ.1.1 * x₀ = x₀ ∧ V.ratEmbed γ = k) (hy : Continuous y := by fun_prop)
  (hΓ : V.Γ.FixesLeft y := by simp) : let F h := D.thetaTerm V a b f g x₀ h * y h
  S.FixesLeft F ∧ Integrable F S.qms ∧ D.centreCoeff (H.j • (x₀ᴴ * V.J * x₀))
        (∫ h, pairTheta W V a b f ⟨·, h⟩ * y h ∂V.quotMeasure) g = ∫ h, F h ∂S.qms :=
  (integral_tsum_orbit V.ratEmbed_injective (by rfl) (by fun_prop) (by
  intros; erw [thetaTerm_ratEmbed_mul]; tauto) (S.ext hS).symm fun z ↦ ⟨fun e ↦ V.witt
  (.of_isUnit_gram (e ▸ h₀)) (.of_isUnit_gram h₀) e,
  (·.choose_spec ▸ (U.gram_invariant ..).symm)⟩).imp (by bound)
  (· (.inl hi) |>.imp_right (D.centreCoeff_integral_eq_tsum hi _ ▸ ·.2))
