import GRH.Lib.Weil.Fock.FockTensor
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known
result; see Lib.Weil.Fock.OscillatorPair).

Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Weighted moments on Fock data; polynomial vectors dense in all moment norms. Mixed
Schrödinger–Fock model; rapid decay of mixed functions in weighted moment norms. -/

open Calc ENNReal Filter Matrix MeasureTheory Real Heisenberg.IsVacuum

variable {ι} [Fintype ι] {ε : ι → ℤˣ} (N : ℕ) (v : fockSpace ε) (c : ℂ) (v' : fockSpace ε)

section

attribute [local simp ←] Complex.ofReal_sub ContinuousLinearMap.integral_comp_comm Finset.mul_sum
  lintegral_const_mul' Real.exp_add Real.exp_nsmul mul_assoc mul_pow ofReal_norm

/-- The weighted norm mom_N(v) = ∫ (1 + ‖y‖)^N |v(y)| dy in [0, ∞], with ‖y‖ the sup norm and dy
Lebesgue measure divided by π^|ι|. -/
noncomputable def weightedNorm := ∫⁻ y, (1 + ‖y‖ₑ) ^ N * ‖v y‖ₑ ∂realMeasure ι

lemma weightedNorm_zero : weightedNorm 0 v = ‖v‖ₑ := by simpa [weightedNorm] using!
  v.2.1.enorm_toL1.symm

lemma weightedNorm_smul :
  weightedNorm N (c • v') = ‖c‖ₑ * weightedNorm N v' := by simp [weightedNorm, mul_comm]

lemma weightedNorm_eq : weightedNorm N v = ∫⁻ y, .ofReal ((1 + ‖y‖) ^ N * ‖v y‖) ∂realMeasure
  ι := by simp (disch := bound) [weightedNorm, ofReal_add]

lemma weightedNorm_realHeisOp_le y : weightedNorm N (realHeisOp y v) ≤
  (1 + ‖y‖ₑ) ^ N * weightedNorm N v := by
  grw [weightedNorm, weightedNorm, ← lintegral_add_right_eq_self _ y, enorm_add_le]
  simp; gcongr; ring; simp

/-- The Fock vector v has all weighted norms mom_N(v) finite. -/
def IsRapidDatum := ∀ N, weightedNorm N v ≠ ⊤

variable {v : fockSpace ε} {Y} [MeasurableSpace Y] {ν : Measure Y} [SFinite ν] {F : Y → fockSpace ε}

lemma norm_le_weightedNorm {S} {ℓ : _ →L[ℂ] ℂ} (h : ∀ z, ‖ℓ (realHeisOp z vacVector)‖ / (1 + ‖z‖) ^
  N ≤ S) : ‖ℓ v‖ₑ ≤ .ofReal S * weightedNorm N v := by
  grw [map_eq_integral, enorm_integral_le_lintegral_enorm]
  simp_all [field, weightedNorm_eq]; grw [h]; simp (disch := bound) [ofReal_mul', mul_comm]

lemma weightedNorm_polyVector_ne_top P : weightedNorm N (polyVector ε P) ≠ ⊤ :=
  (exists_norm_eval_le_exp P).elim fun k ⟨C, h⟩ ↦
  (((integrable_exp_mul_realVac (N + k)).const_mul |C|).lintegral_lt_top.trans_le' (by
    simp [weightedNorm_eq]; gcongr 2; grw [h, add_comm, add_one_le_exp,
      mul_left_comm]; simp [add_mul])).ne

lemma isRapidDatum_vacVector : IsRapidDatum (vacVector : fockSpace ε) :=
  polyVector_one.subst (weightedNorm_polyVector_ne_top · 1)

/-- For an s-finite measure ν and any map F to the Fock space, the weighted norm `weightedNorm`
of the Bochner integral satisfies mom_N(∫ F dν) ≤ ∫ mom_N(F(t)) dν(t) in [0, ∞]. -/
lemma weightedNorm_integral_le : weightedNorm N (integral ν F) ≤ ∫⁻ t, weightedNorm N (F t) ∂ν := by
  by_cases hF : Integrable F ν <;> simp_all [weightedNorm, ← modelInner_heisOp_vacElem,
    integral_undef, -ofReal_norm]
  grw [enorm_integral_le_lintegral_enorm, lintegral_lintegral_swap]; simp
  refine' .mul _ (Continuous.comp_aestronglyMeasurable₂ (g := (modelInner <| heisOp · vacElem)) _ _
    hF.1.comp_fst).enorm <;> fun_prop

lemma isRapidDatum_integral (hF : AEStronglyMeasurable F ν) (h : ∀ N, ∫⁻ y, weightedNorm N
  (F y) ∂ν ≠ ⊤) : Integrable F ν ∧ IsRapidDatum (integral ν F) := ⟨⟨hF, (h 0).lt_top.trans_eq'
  (by simp [weightedNorm_zero])⟩, (h · ∘ eq_top_mono (weightedNorm_integral_le _))⟩

/-- If F maps ℂ^ι to a Fock space with mom_{N'}(F(y)) ≤ C(1 + ‖y‖)^N for all y (sup norm), then
∫ mom_{N'}(v(y)F(y)) dy ≤ C·mom_N(v) for v in the Fock space on ℂ^ι; dy is Lebesgue measure
divided by π^|ι|. -/
lemma lintegral_weightedNorm_smul_le {κ} [Fintype κ] {η} {F : _ → @fockSpace κ _ η} {N N' C} (h :
  ∀ y, weightedNorm N' (F y) ≤ C *
  (1 + ‖y‖ₑ) ^ N) : ∫⁻ y, weightedNorm N' (v y • F y) ∂realMeasure ι ≤ C * weightedNorm N v := by
  grw [(weightedNorm_smul ..).le, h, weightedNorm, ← lintegral_const_mul]
  ac_nf; fun_prop

/-- If s, t ≥ 0 and s ≤ (‖u‖ + 1)t, with ‖u‖ the sup norm of u in ℂ^ι, then s^N · exp(−|u|²/2) ≤
exp(N²) · t^N. -/
lemma pow_mul_realVac_le {s t} {u : ι → ℂ} (h : s ≤ (‖u‖ + 1) * t) (hs : 0 ≤ s := by positivity)
    (ht : 0 ≤ t := by positivity) : s ^ N * ‖realVac u‖ ≤ .exp (N ^ 2) * t ^ N := by
  grw [h, add_one_le_exp, mul_comm, mul_pow]
  simp [realVac]; gcongr; nlinarith [norm_sq_le_re_star_dot u]

/-- If all weighted norms of v in 𝓕 are finite, there is one sequence of polynomials P_n such
that mom_N(v − v_{P_n}) tends to 0 for every N. -/
lemma exists_tendsto_weightedNorm (hv : IsRapidDatum v) : ∃ P :
    ℕ → _, ∀ N, Tendsto (fun n ↦ weightedNorm N (v - polyVector ε (P n))) atTop (nhds 0) := by
  obtain ⟨⟩ := isVacuum_realVac
  refine ⟨_, fun N ↦ tendsto_nhds_bot_mono' (tendsto_lintegral_norm_of_dominated_convergence ?_
    (((integrable_toReal_of_lintegral_ne_top ?_ (hv ((realMeasure ι).integrablePower +
    N))).const_mul _).mul_prod (realMeasure ι).integrable_pow_neg_integrablePower).2 (fun _ ↦
    .of_forall fun (y, w) ↦ by
    grw [norm_smul_of_nonneg, norm_mul, norm_sum_le]; simp [toReal_add]
    grw [sum_le_exp_of_nonneg, dotProduct, norm_sum_le, ← pow_mul_realVac_le (s := 1 + ‖w‖)
      (u := fun i ↦ ‖y i‖ - ‖w i‖) _ (by
      have := norm_le_insert (‖y ·‖) (‖w ·‖); simp_all [Pi.norm_def]; nlinarith)]
    simp [realVac, field, pow_add, star_dot_self_eq_sum, sub_sq, mul_assoc,
      -Complex.ofReal_sum]; repeat bound) (.of_forall fun p ↦ ((NormedSpace.expSeries_div_hasSum_exp
    (star (holCoord ε p.1) ⬝ᵥ holCoord ε p.2)).tendsto_sum_nat.const_mul
    (-v p.1 * realVac p.2 * realVac p.1)).const_smul ((1 + ‖p.2‖) ^ N))) fun n ↦ by
    trans weightedNorm N ((1 - ∑ k ∈ Finset.range n, ∑ p : Fin k →
      ι, let q := polyVector ε (∏ j, .X (p j))
      (k.factorial⁻¹ : ℂ) • (realInner q).smulRight q) v); simp; simp_rw [← map_smul,
      ← map_sum]; rfl
    simp_rw [← smul_sub, norm_smul]
    grw [map_eq_integral, weightedNorm_integral_le, lintegral_prod, (weightedNorm_eq ..).le,
      ← le_norm_self]; congr!
    simp [← conj_modelInner (heisOp _ _), ← valueAt_apply]
    simp_all [dotProduct, Fintype.sum_pow, mul_sub, Finset.mul_sum, div_eq_inv_mul,
      beta_mul_realVac, Complex.exp_eq_exp_ℂ]; ring; fun_prop⟩ <;> fun_prop

open Norms.Operator

lemma one_add_enorm_mulVec_le {p} [Fintype p] (A : Matrix ι p ℂ) y : 1 + ‖A *ᵥ y‖ₑ ≤ (1 + ‖A‖ₑ) *
    (1 + ‖y‖ₑ) := by grw [enorm_eq_nnnorm, linfty_opNNNorm_mulVec, mul_one_add, coe_mul]; bound

lemma weightedNorm_realWeil_le u : weightedNorm N (realWeil u v) ≤ ‖realMultiplier u‖ₑ *
  ((1 + ‖u.1.1‖ₑ) ^ N * weightedNorm N (vacVector : fockSpace ε) *
  weightedNorm N v) := by grw [← lintegral_weightedNorm_smul_le fun _ ↦ by grw [mul_right_comm,
  ← mul_pow, ← one_add_enorm_mulVec_le, ← weightedNorm_realHeisOp_le], ← weightedNorm_integral_le,
  ← weightedNorm_smul, realWeil, weilRep]; rfl

end

variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {ε' : ι' → _} {ε : ι → _} {p} [Fintype p]

/-- A mixed Schrödinger–Fock model along ℂ^ι′ = Lℂ^p + Iℂ^ι + Kℂ^p: maps v ↦ v[a] between Fock
spaces, with (ρ(La′+Iw+Kb)v)[a] = exp(i Im b*(2a+a′)) ρ(w)v[a+a′] and vac[a] = exp(−|a|²)
vac. -/
structure MixedModel (ε' : ι' → _) (ε : ι → _) (p) [Fintype p] where
  (L K : Matrix ι' p ℂ) I : Matrix _ ι ℂ
  slice : _ → fockSpace ε' →L[ℂ] fockSpace ε
  exists_decomp : ∃ A W B, ∀ y, L *ᵥ A *ᵥ y + I *ᵥ W *ᵥ y + K *ᵥ B *ᵥ y = y
  slice_realHeisOp a a' w b v : slice a (realHeisOp (L *ᵥ a' + I *ᵥ w + K *ᵥ b) v) =
    (realHeis 1).β (a + (a + a')) b • realHeisOp w (slice (a + a') v)
  slice_vac a : slice a vacVector = (-(Star.star a ⬝ᵥ a)).exp • vacVector

/-- Rapid decay in a mixed model: for all N, M there is a finite C with (1 + ‖a‖)^M mom_N(v[a])
≤ C mom_{N+M}(v) for all a and v. -/
lemma MixedModel.exists_weightedNorm_slice_le (h : MixedModel ε' ε p) N M : ∃ C ≠ ⊤, ∀ a v,
  (1 + ‖a‖ₑ) ^ M * weightedNorm N (h.slice a v) ≤ C * weightedNorm (N + M) v :=
  h.exists_decomp.rec fun _ ⟨_, _, e⟩ ↦ ⟨_, .symm ⟨fun a v ↦ by
    have g b := ofReal_le_ofReal (pow_mul_realVac_le M (by
      grw [norm_le_add_norm_add a b]; ring; bound : 1 + ‖a‖ ≤ _ * (1 + ‖b‖)))
    grw [mul_le_iff_le_inv, ← mul_assoc, isVacuum_realVac.map_eq_integral, weightedNorm_integral_le,
      lintegral_weightedNorm_smul_le]
    intro y
    rw [mul_assoc, ← mul_le_iff_le_inv, ← e y, slice_realHeisOp, e]
    all_goals simp (disch := bound) [ofReal_add, realVac, neg_div, weightedNorm_smul, slice_vac,
      ↓star_dot_self_eq_norm_sq, sq, ← @ofReal_norm ℂ, ← mul_assoc] at *
    grw [← half_le_self (mul_self_nonneg _), g, one_add_enorm_mulVec_le, mul_pow, ← mul_assoc,
      weightedNorm_realHeisOp_le, mul_left_comm, mul_right_comm, one_add_enorm_mulVec_le, mul_pow,
      mul_mul_mul_comm, pow_add], by simp [isRapidDatum_vacVector N, mul_eq_top]⟩⟩

/-- In a mixed model, if all weighted norms mom_N(v) are finite, then so are those of v[a] for
every point a. -/
lemma MixedModel.isRapidDatum_slice (h : MixedModel ε' ε p) a {v} (_ : IsRapidDatum v) :
    IsRapidDatum (h.slice a v) :=
  (by grind [h.exists_weightedNorm_slice_le · 0, IsRapidDatum, mul_ne_top])
