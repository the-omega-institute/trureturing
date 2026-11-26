import OmegaMath.NumberTheory.GRH.Lib.General.Analysis.HolomorphicIntegral
import OmegaMath.NumberTheory.GRH.Lib.Weil.Fock.FockAction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known
result; see Lib.Weil.Fock.OscillatorPair).

This file: L1 Fock space, polynomial vectors, derivative of the Heisenberg action on them. Transport
of the coefficient model along linear or conjugate-linear isomorphisms. Tensor products of Fock
vectors and block diagonal action over places. -/

noncomputable section

open Complex MvPolynomial Heisenberg IsVacuum Finset Int MeasureTheory Measure Matrix Sum
  OrthogonalSum Function Fintype
variable {ι} [Fintype ι] {ε : ι → _}

/-- The Fock space: integrable functions c on ℂ^ι with c(x) = ∫ c(y)β(y,x)e(x−y) dy, e the
Gaussian exp(−|x|²/2), under the L¹ norm. -/
abbrev fockSpace ε := Model (@realHeis ι _ ε)

/-- The Weil representation of U(ε) on the Fock space 𝓕: ω₀(u)c = conj(det d) ∫ c(y) ϱ(uy)e dy,
d the negative block of u, e the Gaussian. -/
abbrev realWeil : USign ε →* fockSpace ε →L[ℂ] fockSpace ε := weilRep (realAction ε)

/-- For x in ℂ^ι, the bounded operator on 𝓕 sending c to z ↦ β(x,z)c(z−x). -/
abbrev realHeisOp (x : ι → ℂ) : fockSpace ε →L[ℂ] fockSpace ε := heisOp x

/-- The Gaussian exp(−|x|²/2) regarded as an element of the space 𝓕. -/
abbrev vacVector : fockSpace ε := vacElem

/-- The bounded sesquilinear form on 𝓕, conjugate-linear in the first variable, (c, c′) ↦ ∫ c̄
c′. -/
abbrev realInner : fockSpace ε →L⋆[ℂ] fockSpace ε →L[ℂ] ℂ := modelInner

lemma differentiableAt_superposition ε {E} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]
  P (f : E → ℂ × _ → _) {a} (hf : ∀ x, Differentiable ℂ (f · x)) (cf : Continuous f.uncurry)
  (h0 : ∀ y, f a y = (holCoord ε y.2, -(star y.2 ⬝ᵥ y.2) / 2)) (h : ∀ z (r : ℝ) y, f z (r • y) =
  (r • (f z y).1, r ^ 2 • (f z y).2)) : DifferentiableAt ℂ (fun z ↦ ∫ x, (MvPolynomial.eval (f z (1,
  x)).1 P * exp (f z (1, x)).2) • realHeisOp x (vacVector : fockSpace ε) ∂realMeasure ι) a := by
  obtain ⟨_, k, A, hk⟩ := P.continuous_eval, exists_norm_eval_le_exp P
  exact (eventually_differentiableAt_integral (((integrable_exp_mul_realVac (2 * k)).comp_smul
    one_half_pos.ne').const_mul (|A| * .exp 1 * _)) (by fun_prop) (((isCompact_closedBall 0
    1).eventually_forall_mem (fun z y ↦ k * ‖y.1‖ * (‖(f z y).1‖ - ‖y.2‖) + (f z y - f a y).2.re)
    (.Iio 4⁻¹) (by simp [*, Iio_mem_nhds])).mono fun z H x ↦ ⟨by fun_prop, by
  specialize H ((1 ⊔ ‖x‖)⁻¹ • (1, x))
  grw [norm_smul, mul_comm, norm_mul, hk]
  simp [↓h, *, norm_smul, sq, field, realVac, mul_assoc, ← Real.exp_add] at *
  gcongr 2; grind [sq_nonneg, sq, norm_sq_le_re_star_dot]⟩)).self_of_nhds

/-- If v_P = P(ζ)exp(−|x|²/2) lies in the Fock space, then for v in ℂ^ι so does v_Q, Q = ∑_i
(conj(ζ_i(v)) X_i − ζ_i(v) ∂_i)P, and v_Q is the derivative at t = 0 of t ↦ ϱ(tv)v_P, t
real. -/
lemma exists_hasDerivAt_realHeisOp {P} v hu : ∃ h,
  HasDerivAt (fun t : ℝ ↦ realHeisOp (t • v) ⟨(P.eval <| holCoord ε ·) *
  realVac, hu⟩) (⟨((heisDeriv ε v P).eval <| holCoord ε ·) * realVac, h⟩ : fockSpace ε) 0 := by
  let f | t, (s, w) => (holCoord ε w + t • s • -holCoord ε v,
    -(star w ⬝ᵥ w) / 2 + t * s * (star (holCoord ε v) ⬝ᵥ holCoord ε w - s * star v ⬝ᵥ v / 2 * t))
  have e (t : ℝ) w : realHeisOp (t • v) ⟨_, hu⟩ w = P.eval (f t (1, w)).1 * (f t (1, w)).2.exp := by
    erw [heisOp_apply, mul_left_comm, beta_mul_realVac]
    simp [star_trivial, f, realVac, ← exp_add]; ring
  have' H :=
    (differentiableAt_superposition ε P f ..).hasDerivAt.scomp 0 (hasDerivAt_id 0).ofReal_comp
  simp_rw [Function.comp_def, ← e, ← Rep.integrated_apply, integrated_vacElem] at H
  refine (funext fun w ↦
    ((H.map_clm (modelEval ..)).unique (funext (e · w) ▸ (((hasFDerivAt_mvPolynomial_eval P
    _).hasLineDerivAt _).mul (.cexp (.const_add _ (.mul (hasDerivAt_mul_const _) (.const_sub _
    (hasDerivAt_const_mul _)))))).comp_ofReal)).trans ?_ : _ = _ * _) ▸ ⟨_, H⟩
  simp [heisDeriv, realVac, dotProduct, sum_mul, mul_sum, holCoord_eq, neg_add_eq_sub,
    ← sum_sub_distrib]; congr! 1
  split <;> simp_all [units_ne_iff_eq_neg, raiseOp, lowerOp] <;> ring
  repeat fun_prop
  repeat simp [star_trivial, f, funext_iff, field]

/-- The linear map P ↦ v_P from complex polynomials to the Fock space, v_P(x) =
P(ζ(x))exp(−|x|²/2), where ζ(x)_i is x̄_i at positive and x_i at negative coordinates. -/
def polyVector ε : MvPolynomial ι ℂ →ₗ[ℂ] @fockSpace ι _ ε := .codRestrict _ (.pi fun x ↦
    (aeval (holCoord ε x)).toLinearMap.smulRight (realVac x)) (by
  induction · using induction_on
  convert (‹_› • vacVector).2; ext; simp; aesop
  convert have D c := (IsVacuum.modelSubmodule _).smul_mem (c / 2) (exists_hasDerivAt_realHeisOp
      (holCoord ε (Pi.single ‹_› c)) ‹_›).1
    add_mem (D 1) (D I)
  ext; simp_all [heisDeriv, holCoord_eq, Finset.sum_eq_single ‹ι›]
  split <;> simp_all [units_ne_iff_eq_neg, raiseOp, lowerOp] <;> grind [I_sq])

/-- A polynomial as the vector it gives with the vacuum. -/
instance : Coe (MvPolynomial ι ℂ) (fockSpace ε) := ⟨polyVector ε⟩

@[simp] lemma polyVector_apply P x : polyVector ε P x =
  MvPolynomial.eval (holCoord ε x) P * realVac x := rfl

/-- The Fock vector v_1 of the constant polynomial 1 is the Gaussian vacuum exp(−|x|²/2). -/
@[simp] lemma polyVector_one : polyVector ε 1 = vacVector := by aesop

lemma hasDerivAt_realHeisOp v P : HasDerivAt (fun t : ℝ ↦
  realHeisOp (t • v) (polyVector ε P)) (heisDeriv ε v P) 0 := (exists_hasDerivAt_realHeisOp ..).2

attribute [irreducible] polyVector

@[simp] lemma polyVector_injective : (⇑(polyVector ε)).Injective :=
  fun _ _ h ↦ funext (by simpa +contextual [realVac, holCoord_eq] using congr($h <| holCoord ε ·))

namespace Heisenberg.IsVacuum

variable {W W' : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] [LocallyCompactSpace W]
  [AddCommGroup W'] [TopologicalSpace W'] [MeasurableSpace W'] [IsTopologicalAddGroup W']
  [BorelSpace W'] [SecondCountableTopology W'] {H μ e H' μ' e'} [IsAddHaarMeasure μ]
  [IsAddHaarMeasure μ'] [he : IsVacuum H μ e] [he' :
  IsVacuum H' μ' e'] {σ : ℂ →+* ℂ} [RingHomIsometric σ]
  {φ : W' ≃ₜ+ W} (hβ : ∀ x y, σ (H.β (φ x) (φ y)) = H'.β x y) (hφ : ∀ x, e (φ x) = e' x)
include he he' hφ

variable (H H') in
omit [SecondCountableTopology W'] in
/-- Let e, e' be vacua (`Heisenberg.IsVacuum`) for Haar measures μ on W and μ' on W'. An isomorphism
of topological groups φ : W' → W with e ∘ φ = e' carries μ' to μ. -/
lemma measurePreserving_equiv : MeasurePreserving φ μ' μ :=
  ⟨by fun_prop, addHaar_eq_of_integral_eq_one he.integral_norm_sq_eq_one
  (he'.integral_norm_sq_eq_one ▸ _root_.funext hφ ▸ φ.isClosedEmbedding.integral_map _)⟩

include hβ

omit [SecondCountableTopology W'] in
lemma map_integral_and_map_vacuum : (∀ f, σ (integral μ f) = ∫ x, σ (f (φ x)) ∂μ') ∧ ∀ x, σ (e
  (φ x)) = e' x := have _ := hβ; by
  cases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous <;> simp_all
  [integral_conj, he'.4, (measurePreserving_equiv H H' hφ).integral_comp φ.measurableEmbedding]

/-- For a topological isomorphism φ: W′ → W matching the vacua and, up to σ, the bicharacters,
the continuous σ-semilinear map v ↦ σ∘v∘φ between the reproducing spaces. -/
def transport : Model H →SL[σ] Model H' := have m := measurePreserving_equiv H H' hφ
  LinearMap.mkContinuous (by use! fun v ↦ ⟨_, (σ.toSemilinearMap.mkContinuous 1
                (by simp)).integrable_comp (m.integrable_comp_of_integrable v.2.1), by
              simpa [map_integral_and_map_vacuum hβ hφ, ← map_sub, hβ] using
                (congrArg σ <| v.2.2 <| φ ·)⟩ <;> aesop)
    1 fun v ↦ by erw [norm_eq, m.integral_comp φ.measurableEmbedding (‖σ <| v ·‖), norm_eq]; simp

@[simp] lemma transport_apply v x : transport hβ hφ v x = σ (v (φ x)) := rfl

end Heisenberg.IsVacuum

variable {ι : _} [Fintype ι] {ε : _} {ι₁ ι₂ T : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype T] {ε₁ ε₂}
  {e : ι₁ ⊕ ι₂ ≃ ι} (he : ε ∘ e = ε₁ ⊕ᵥ ε₂) (u : T → USign ε) (v : T → fockSpace ε)

attribute [local simp] modelInner_apply realVac add_div exp_add dotProduct eval_rename signMatrix
  holCoord_eq integral_map_equiv norm_eq sum_prod_type weilRep integrated_apply_eq_integral comp_def
  tmul_apply realMultiplier

attribute [local simp ←] exp_sum sum_div integral_fintype_prod_eq_prod volume_pi_pi norm_prod

/-- For coordinates split by e with signs ε₁ and ε₂, the bounded bilinear map sending two Fock
vectors to their external product in the Fock space of ε. -/
def realBoxProd : fockSpace ε₁ →L[ℂ] fockSpace ε₂ →L[ℂ] fockSpace ε := (realCoordSum he).tmul

@[local simp] lemma pi_realMeasure : .pi (fun _ ↦ realMeasure ι) =
  (realMeasure _).map (MeasurableEquiv.curry T ..) :=
  Measure.pi_eq (by simp [realMeasure, pow_mul', -inv_pow, Measure.map_smul,
    measurePreserving_curry.2, (MeasurableEquiv.measurable _).aemeasurable])

/-- The continuous multilinear map sending a T-indexed family of Fock vectors v_τ to the product
function x ↦ ∏ v_τ(x_τ) in the Fock space on T × ι. -/
def piTensor :
  ContinuousMultilinearMap ℂ (fun _ : T ↦ fockSpace ε) (fockSpace (ε <| @Prod.snd T _ ·)) :=
  MultilinearMap.mkContinuous (.codRestrict (.pi fun _ ↦ .compLinearMap (.mkPiAlgebra ..) fun _ ↦
  (modelEval _).1) _ fun v ↦ ⟨(integrable_map_equiv ..).1 (pi_realMeasure.subst (.fintype_prod
  (v · |>.2.1))), by simpa [realHeis] using! fun _ ↦ congr(∏ τ, $((v τ).2.2 _))⟩) 1 (by aesop)

@[simp] lemma piTensor_apply x : piTensor v x = ∏ τ, v τ (x ⟨τ, ·⟩) := rfl

lemma piTensor_polyVector (P : T → _) : piTensor (polyVector ε <| P ·) = ∏ τ,
  rename (τ, ·) (P τ) := by aesop

lemma realInner_piTensor w : realInner (piTensor v) (piTensor w) = ∏ τ,
  realInner (v τ) (w τ) := by aesop

/-- The ring homomorphism sending a T-indexed family of complex ι × ι matrices to the block
diagonal matrix with rows and columns indexed by T × ι. -/
abbrev blockMatrix := letI := @instDecidableEqProd ι T _ _
       (reindexRingEquiv ℂ (.prodComm ι T)).toRingHom.comp (blockDiagonalRingHom ..)

/-- The homomorphism from U(ε)^T to the unitary group of the signs (τ, i) ↦ ε_i on T × ι, by
block diagonal matrices. -/
@[simps! apply_coe_val] def blockU : (T → USign ε) →* USign (ε <| @Prod.snd T _ ·) :=
  .mk' (fun u ↦ U.of IsHermInvolution.isUnit (blockMatrix (u ·)) (by
  simpa [← submatrix_mul_equiv (e₂ := .prodComm ..), -Equiv.coe_prodComm]
  using congr(blockMatrix $(funext (u · |>.2))))) fun _ _ ↦ by ext : 2; apply map_mul

lemma realMultiplier_blockU : realMultiplier (blockU u) = ∏ τ, realMultiplier (u τ) := by simp

lemma realWeil_piTensor : realWeil (blockU u) (piTensor v) = piTensor fun τ ↦ realWeil (u τ)
  (v τ) := by ext; simp [realAction]; simp [mulVec, blockDiagonal, realHeis, diagonal]; tauto

lemma realBoxProd_polyVector P Q : realBoxProd he (polyVector _ P) (polyVector _ Q) =
  rename (e ∘ inl) P * rename (e ∘ inr) Q
  := by ext; simp [realBoxProd, reindex_equiv e, by simpa using congrFun he]; ring!
