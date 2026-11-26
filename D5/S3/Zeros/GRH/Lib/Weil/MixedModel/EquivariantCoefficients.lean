/- GID: D5/S3/Zeros/GRH/Lib/Weil/MixedModel/EquivariantCoefficients
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/MixedModel/EquivariantCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.MixedModel.EquivariantCoefficients. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/MixedModel/EquivariantCoefficients.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.SiegelWeil.StrongApproximation.EqualRankConstant
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.ThetaIntegralLaws
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

Part of: Tower property: constant term of a theta lift along an isotropic line (known result; see
Lib.SiegelWeil.Tower.LargeSideConstantTerm).

Part of: Singular forms are governed by their coefficients at unimodular indices (known result; see
Lib.SiegelWeil.SingularForms.SingularForms).

This file: Archimedean Tate integral of slices of a rapid datum converges and is rapid. Mixed-model
slice of a Schwartz-Bruhat datum as partial Fourier transform at places S. Finite slices of standard
framed data along an isotropic subspace. Unit law of a tame character;
idele of inverse uniformisers and its modulus. Fourier coefficient as functional of local datum,
laws under shears and centre. -/

open ENNReal Fintype IntegralFrame G stdLattice MatMul Matrix MeasureTheory SemilocalField Space
  Splitting

variable {E} [Field E] [CMType E] [WeilData E] {n n' r r'} [Fintype n] [Fintype n'] [Fintype r]
  [Fintype r'] {s s' t t'} {W : Space E n s} {W' : Space E n' s'} {V : Space E r t}
  {V' : Space E r' t'} (A : W'.Splitting W Unit) (X :
  V'.Splitting V Unit) [IsBaseAdapted A] [IsBaseAdapted X] (μ : NumberField.InfinitePlace E → ℤ)

/-- The integrand of the cone integral at (k, t): ∏(t_x/|t_x|)^(2μ(x)) · (∏|t_x|²)^σ times the
real slice `lineTermReal` at t of v moved by the real part of k. -/
noncomputable def coneIntegrand β (σ : ℝ) v (p : maxCompact E t' × (_ → ℂ)ˣ) :=
    ((∏ x, (p.2.1 x / ‖p.2.1 x‖) ^ (2 * μ x)) * (ideleAbs (p.2.map (.inl ..)) ^ σ :)) • lineTermReal
  A X β p.2 (realPairWeil ((card n' / 2 :) + (-μ) ·) 0 (1, p.1.1.1) v)

open Real in
/-- For adapted splittings A, X along isotropic lines, σ ≥ 1 and a rapid real datum v, the
integrand F of the cone integral is integrable, its integral is rapid, and for each N the
N-th moments of F are dominated by an integrable function. -/
lemma integrable_coneIntegrand β {σ} (h : 1 ≤ σ) {v} (hv : IsRapidDatum v) :
    let F := coneIntegrand A X μ β σ v; let ν := Measure.haar.prod .haar; Integrable F ν ∧
                IsRapidDatum (integral ν F) ∧ ∀ N, ∃ φ : _ → ℝ, Integrable φ ν ∧ ∀ p,
        weightedNorm N (F p) ≤ ‖φ p‖ₑ := by
  choose _ _ H using @MixedModel.exists_weightedNorm_slice_le
  refine and_rotate.1 ⟨?H, isRapidDatum_integral (Continuous.aestronglyMeasurable ?_)
    (?H · |>.elim fun _ ⟨i, H⟩ ↦ (i.2.trans_le' (lintegral_mono H)).ne)⟩
  refine' fun _ ↦ ⟨_, .symm ⟨fun (_, a) ↦ _,
    .mul_prod (integrable_of_compactSpace _) integrable_prod_inv_one_add_log_sq⟩⟩
  simp [coneIntegrand]
  grw [enorm_toReal, weightedNorm_smul, (?_ : ‖_‖ₑ ≤ _ ^ _ * _), mul_right_comm, lineTermReal, H,
    realPairWeil_apply_apply, weightedNorm_smul, weightedNorm_realWeil_le]
  simp [← toReal_le_toReal, mul_eq_top, toReal_add, ideleAbs]
  grw [abs_of_nonneg, ← finsetProd_rpow, pow_mul, ← Finset.prod_const, le_mul_inv_iff₀,
    ← Finset.prod_mul_distrib]
  gcongr; have := norm_nonneg (a.1 x)
  grw [← sub_add_cancel σ 1, rpow_add_one, mul_assoc, abs_of_pos, lt_one_add ‖_‖, Nat.le_ceil
    (σ - 1), Real.rpow_natCast, ← pow_mul, ← norm_le_pi_norm _ (x, .inr 0), pow_add _ _ 4]
  simp; gcongr
  nlinarith [mul_le_mul_of_nonneg_left (log_le_self this) this, self_sub_one_le_mul_log this]
  any_goals first | positivity | simp [mul_eq_top, *, hv _, isRapidDatum_vacVector _, le_abs,
    toReal_add, pairHomInf, realMultiplier] <;> fun_prop [kroneckerMap]
  obtain := continuous_pi_iff.1 ((@Units.continuous_val (_ → ℂ)).snd' (X := maxCompact E t'))
  unfold coneIntegrand lineTermReal IsAdapted.mixedModel ideleAbs; dsimp; fun_prop
    (disch := simp [h.trans'])

variable {F : Type} [V : SemilocalField F] {S : Set (FinPlace E)} {π : 𝔸f E →+* F} {p : Type} {T :
  Space E r t}

section

attribute [-simp] Prod.smul_snd

/-- The additive character y ↦ ψ_f(ȷαᾱσ(y)) of F, σ a chosen section of π onto the adeles
supported on S. -/
noncomputable def ReadsAt.ψ (h : ReadsAt S π) := (psi₀ E).compAddMonoidHom h.3.2.choose

lemma ReadsAt.psi_apply (h : ReadsAt S π) z : h.ψ (π z) =
  psi₀ E (idem S * z) := congr(psi₀ E $(by grind))

lemma ReadsAt.hasIntegralConductor_psi (h : ReadsAt S π) :
  HasIntegralConductor h.ψ := have ⟨c, e, _⟩ := h.3.2.choose_spec; ⟨continuous_psi₀.comp c, by
    simp [Function.Surjective.forall (⟨_, e ·⟩), ← map_mul, psi_apply, h.2]
    use fun x ↦ .trans ⟨by simp_all [mul_assoc, mul_mem], by grind [idem_mul_self]⟩
      (forall_psi₀_mul_eq_one_iff _)⟩

/-- Let 1 be adapted to u, Φ Schwartz–Bruhat with Φ(lu*⁻¹x + kuz + ιy) = ∏1_O f_i(z_i)·Ψ(y). The
slice of v ⊗ Φ at u*⁻¹κx is 0 unless x is integral off S ∪ S̄; then it is
c∏∫_O ψ(x̄_i t)f_i(t)dt·(real slice) ⊗ Ψ, with c = `vacuumFactor`. -/
lemma mixedTerm_localDatum [Fintype p] (h : ReadsAt S π) {D : (W'.hom V').Splitting _ p} {u} (hu :
  D.IsAdapted 1 u) {Φ U} (k : Φ ∈ schwartzBruhat U) x v {Ψ} (f : _ → _ → _) (H : ∀ y z, Φ (vecToMat
  ((D.frameAt 1 u).map (π ·.2) *ᵥ ((π ·.2) ∘ x ⊕ᵥ z ⊕ᵥ matToVec y))) = (∏ i, ite (z i ∈ O) (f i
  (z i)) 0) * Ψ y) : D.mixedTerm (u⁻¹.1ᴴ *ᵥ WeilData.scaleIdele E • x) (localDatum _ _ v Φ h) = (ite
  (∀ i, idem S.conjClosureᶜ * (x i).2 ∈ Ô E) (vacuumFactor hu).1 0 * ∏ i, ∫ t in V.O, h.ψ (π (star
  (x i).2) * t) * f i t) • localDatum W T (hu.mixedModel.slice (fun p ↦ (x p.2).1 p.1) v) Ψ h := by
  rw [mixedTerm_integrated hu, projReal_of_mem_finitePart (name_mem_finitePart ..), ← map_smul,
    mul_smul, smul_name]
  congr!; simp [realCoord, Units.smul_def]
  refine .trans (by aesop)
    ((hu.omega_name_of_isMixedLaw isMixedLaw_mixedTerm _ _ h.1 (h.isSchwartzBruhat k)).trans ?_)
  rw [projOn_vacElem, hu.mixedTerm_omega_vacElem.choose_spec.2, map_smul]; rcongr
  split <;> simp_all [vacuumFn, finVec, ← conjTranspose_mul, vacuumFactor]
  simp [← integral_indicator isCompact_O.measurableSet, Set.indicator, ← mul_ite_zero, -mul_ite,
    ← H, ← integral_mul_const, ← integral_fintype_prod_volume_eq_prod, sliceDatum, finFrameVector,
    mul_assoc, ← h.psi_apply, ↓dotProduct_smul, vecToMat, Matrix.map, entrywise]
  obtain ⟨⟨_, σ, _, e, f⟩, _⟩ := h.3, k.1.continuous, h.hasIntegralConductor_psi.1; refine .trans
    (by rcongr; erw [← map_prod h.ψ.toMonoidHom]; rfl') ((MeasurePreserving.mk ?z (by
    simpa [volume_O, volume_pi] using! (map_restrict_addHaar_eq (latticeMeasure ..) volume
      (.compLeft π p) ?z isOpen_integralBox.measurableSet
      (⟨σ ∘ ·, by simp [mem_integralBox, idem_compl, sub_mul, ← f, e, funext_iff]⟩)
    (.univ_pi fun _ ↦ isCompact_O.measurableSet) (.trans (by simp [Set.ext_iff, h.2]; tauto)
    integralBox_compl_inter)).1)).hasLaw.integral_comp ?_) <;> fun_prop

/-- For an adapted splitting A, the images under π of the finite parts of the adelic frame (k,
ι, l) and its dual frame, as mutually inverse integral matrices over F. -/
noncomputable def adaptedFrame (h : ReadsAt S π) (A : W'.Splitting W r') [k : IsBaseAdapted A] :
  IntegralFrame F n' n r' := by
  constructor
  simp +arith [↓mul_eq_one_comm_of_card_eq _ n', A.card_eq, ← add_assoc]
  use ?_, ?_, by simpa [map_add, -RingHom.coe_comp] using
    congr((π.comp (.snd ..)).mapMatrix $A.sum_frame_mul_coord_eq_one)
  repeat cases k; simp_all [IsOrthoIntegral, IsIntMatrix, h.2, mul_mem, kCoord, iCoord, lCoord,
    star_mem_Ô, stdForm]

end

/-- Let D be adapted, y = x_f, Φ Schwartz–Bruhat, Φ(w) = 1_O(w)G(wk | wι) whenever wk = πy. The
slice of v ⊗ Φ at κx vanishes unless y is integral; then, with c = `vacuumFactor`,
it is c·(real slice of v) ⊗ (z ↦
1_O(z)G(πy | z)). -/
lemma ReadsAt.sourceTerm_localDatum {E} [Field E] [CMType E] [WeilData E] {n a b m} [Fintype n]
  [Fintype a] [Fintype b] [Fintype m] {s t r} {X : Space E m r} {W₁ : Space E n s} (D :
  X.Splitting W₁ b) (V : Space E a t) {F} [SemilocalField F] {S} {π : 𝔸f E →+* F} (h : ReadsAt S π)
  [IsBaseAdapted D] {G Φ U} (k : Φ ∈ schwartzBruhat U) x v : let y := x.map (RingHom.snd ..)
  (∀ w : Matrix .., w * (adaptedFrame h D).K = y.map π → Φ w = (adaptedFrame h D).stdDatum G w) →
    D.sourceTerm V (WeilData.scaleIdele E • x) (localDatum X V v Φ h) = ite (IsIntMatrix (Ô E) y)
    (vacuumFactor (isAdapted_homSource D V)).1 0 • localDatum _ V (realSlice D V x
    v) (fun z ↦ ite (IsIntMatrix O z) (G (fromCols (y.map π) z)) 0) h := by
  intro y e
  set A := adaptedFrame h D
  erw [sourceTerm_eq_adapted_mixedTerm,
    mixedTerm_localDatum h (isAdapted_homSource ..) k _ v (fun i _ ↦ ite (π (matToVec y i) ∈ O) 1 0)
    fun w z ↦ .trans (b := Φ (y.map π * A.K' + vecToMat z * A.L' + w * A.I')) ?_ ?_] <;> congr
  simp [↓integral_mul_const, volume_O, Measure.real, mul_add, h.ψ.map_add_eq_mul,
    h.hasIntegralConductor_psi.2, mem_Ô, by simpa using (@setIntegral_char F _ _ volume _
    O.toAddSubgroup _ _ _ isOpen_O ·), IsIntMatrix, h.2, prod_ite_zero, matToVec,
    y, ↓idem_mul_mem_Ô, ↓show ∀ x, π (Star.star x) ∈ O ↔ _ from h.star.2]; grind
  ext; simp [frameAt_homSource, stdForm, entrywise, vecToMat, sum_prod_type, diagonal,
    apply_ite]; ac_rfl
  simp [e, stdDatum, blocks_spec, ↓mul_fromCols, forall_and, prod_ite_zero, fun z ↦
    (⟨(·.mul A.spec.1), (by simpa [-mul_fromCols, A.spec] using IsIntMatrix.mul · A.spec.2.1)⟩ :
    IsIntMatrix O z ↔ ∀ i : a, _)]
  split_ifs <;> tauto

variable {E : Type} [Field E] [CMType E] {μ : NumberField.InfinitePlace E → ℤ} (𝔠 :
  SplitTameChar E μ)

lemma SplitTameChar.invOnUnits_mul_div_star {u} (hu : u ∈ idelesUnitOff ∅) : invOnUnits 𝔠.χ
  (evalPlaces _ u) * 𝔠.ν.baseChange.finPart u / invOnUnits 𝔠.χ (evalPlaces _ (star u)) = 1 :=
  congr(_ * $(𝔠.nu_apply_of_integral _ ((coe_idelesUnitOff_empty.le hu).elim (mul_mem · <|
  star_mem_Ô ·))) / _).trans (by simp [coe_divStar, invOnUnits, isIntegralUnit_iff_v_eq_one,
  mem_idelesUnitOff.1 hu, mul_assoc, ← map_mul, ← star_mul, 𝔠.χ.apply_eq_zero_iff, IsUnit.map])

lemma exists_idele_star_eq_unif : ∃ c, (∀ v, star v ∉ 𝔠.S → c.1 v = 1) ∧ evalPlaces 𝔠.S (star c.1) =
  ϖ.1 ∧ finIdeleAbs c⁻¹ = ∏ i : 𝔠.S, ↑i.1.q := by
  use star (∏ i : 𝔠.S, locIdele _ (uniformizer i)), ?_,
    funext (by simp_all [evalPlaces, Finset.prod_eq_single ·,
    eq_comm, ϖ]) <;> simp [← _root_.evalAt_apply, star_locIdele, norm_locField_eq_q_zpow]
  simp +contextual (disch := aesop)

variable {E n₀ a b m p : Type} [Field E] [CMType E] [WeilData E] [Fintype a] [Fintype m] {μ :
  NumberField.InfinitePlace E → ℤ} {𝔠 : SplitTameChar E μ} {r : m → ℤˣ} {X : Space E m r} {ρ M 𝒟}
  (h : IsEquivariantLift (b := b) 𝔠 X ρ M 𝒟) [Fintype p] [Fintype n₀] {s₀} {X₀ : Space E n₀ s₀}
  (H : X.Splitting X₀ p) (T : Matrix p p E)

include h

lemma IsEquivariantLift.centreCoeff_shear {Ψ} (hΨ : Ψ ∈ M) {ν} {c : Matrix m a (𝔸 E)} {k :
  Matrix a m (𝔸 E)} {B}
  (hν : let e : 𝔸 E := idemAdele 𝔠.S; mat ν = 1 + (e • (c * k) - star e • B)) (hc : k * c = 0) x :
  let Ψ' y := Ψ (y + (mat x⁻¹ * c).map (componentsAt 𝔠) * ((k * mat x).map (componentsAt 𝔠) * y))
  Ψ' ∈ M ∧ H.centreCoeff T (𝒟 Ψ') x = H.centreCoeff T (𝒟 Ψ) (ν⁻¹ * x) := by
  have e := by simpa [← mat_mul] using congr(x⁻¹.mat * $hν * x.mat)
  have ⟨_, i, o⟩ := (by simp +contextual [_root_.Gf.atPlace, Prod.ext_iff, funext_iff, atPlaces,
    𝔠.star_notMem, ← ext_iff, Units.ext_iff, Subtype.ext_iff]; bound : ∀ g, mat g = _ → g.2 = g ∧
    g.2 ∈ _root_.Gf.supportedOn m 𝔠.S ∧ (atPlaces _ g.2).1 =
    Matrix.map (1 + x⁻¹.mat * c * (k * x.mat)) (componentsAt 𝔠)) _ e
  have := (h.law_on hΨ _ i).imp_right (· <| · * ν⁻¹ * x)
  erw [o, ← RingHom.map_det, det_one_add_mul_comm] at this
  simp_all [Matrix.map_add, centreCoeff, ← Matrix.mul_assoc, k.mul_assoc, ← mat_mul, ← mul_assoc]

/-- At each point x, Ψ ↦ (T-th Fourier coefficient of 𝒟Ψ) is a linear functional L on M. The shear
of Ψ by z along the frame k at x stays in M and multiplies LΨ by ψ(tr(T_S z)), T_S = T divided by
the idele `invDifferentIdele`, read at the ramified places S of 𝔠. -/
lemma IsEquivariantLift.exists_linear_centreCoeff x : ∃ L : _ →ₗ[ℂ] ℂ, ∀ Ψ ∈ M, L Ψ =
  H.centreCoeff T (𝒟 Ψ) x ∧ ∀ z, let Ψ' y := Ψ (y + (x⁻¹.mat * H.kAdelic).map (componentsAt 𝔠) * z *
    ((H.lCoord * x.mat).map (componentsAt 𝔠) * y))
  Ψ' ∈ M ∧ L Ψ' = 𝔠.readsAt.ψ (((invDifferentIdele E)⁻¹.1 • T.map toAdele).map (componentsAt 𝔠) *
    z).trace • L Ψ := (LinearMap.exists_extend ⟨⟨fun Ψ : M ↦ H.centreCoeff T (𝒟 Ψ) x,
  fun a c ↦ by simpa using ((centreCoeff_sub (h.isAutFunction a.2) (h.isAutFunction c.2)
  (-1) 1).2 ..)⟩, by simp [centreCoeff, ← quotMean_const_mul, mul_left_comm]⟩).imp (by
  simp_all [DFunLike.ext_iff]; intro L hL Ψ hΨ z
  obtain ⟨N, rfl⟩ : ∃ N, Matrix.map N (componentsAt 𝔠) = z :=
    ⟨z.map (0, adeleOfLocal _ ·), Matrix.ext (by simp [componentsAt])⟩
  have := h.centreCoeff_shear H T hΨ
    ((H.mat_radicalCentre (@idemAdele E _ _ _ • N)).trans (by aesop)) (by simp) x
  erw [← Matrix.map_mul, ← AddMonoidHom.map_trace, ReadsAt.psi_apply, psi₀_apply,
    mul_left_comm (invDifferentIdele E).1.2, ← Prod.snd_mul]; simp_all [stdAddChar, -map_smul,
    ← H.centreCoeff_radicalCentre_mul (h.isAutFunction hΨ) (@idemAdele E _ _ 𝔠.S • N) (_ * _)])

omit [WeilData E] in
lemma IsEquivariantLift.comp_mul_mem_ker (g : GL m _) Ψ (a : Ψ ∈ M ⊓ 𝒟.ker) :
    (Ψ <| g.1 * ·) ∈ M ⊓ 𝒟.ker := (𝔠.exists_atPlaces_eq g).elim fun k ⟨i, e⟩ ↦
  e ▸ (h.law_on a.1 _ i).imp_right (funext fun x ↦ by convert · (x / k) <;> aesop)
