/- GID: D5/S3/Zeros/GRH/Lib/Weil/Fock/OscillatorPair
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Fock/OscillatorPair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Fock.OscillatorPair. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Fock/OscillatorPair.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Fock.FockHarmonicCoeff
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.Kronecker
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Rigidity.AnalyticVectors
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: the Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q). The
space here is the L¹ (Feichtinger) space of vacuum coefficients instead of the Hilbert Fock space.
No kernel formula is proved, only the derivative and coefficients between harmonic polynomials, with
weighted moments in place of Schwartz seminorms. Source: M. G. Davidson, The harmonic representation
of U(p,q) and its connection with the generalized unit disk, Pacific J. Math. 129 (1987), §1 and
Prop. 2.2; G. B. Folland, Harmonic Analysis in Phase Space (1989), ch. 1, 4; H. Reiter, Metaplectic
Groups and Segal Algebras, LNM 1382 (1989).

This file: Derivative of oscillator representation on polynomial vectors is the quadratic
creation-annihilation operator. Real unitary dual pair on Fock space: unitarity, derivative,
positivity on harmonics. -/

open Finset Matrix Heisenberg.IsVacuum Norms.L2Operator

/-- If γ is a curve in U(ε) with γ(0) = 1 whose matrix has derivative Y at 0, then t ↦
ω₀(γ(t))v_P has derivative v_Q in 𝓕 at 0, where Q is the polynomial `weilDeriv` ε Y P.

Known result: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q). -/
lemma hasDerivAt_realWeil {ι : Type} [Fintype ι] {ε : ι → _} {γ : ℝ → _} {Y} (h0 : γ 0 = 1) (h :
    HasDerivAt (γ · |>.1.1) Y 0) P :
  HasDerivAt (fun t ↦ realWeil (γ t) (polyVector ε P)) (weilDeriv ε Y P) 0 := by
  obtain ⟨hd, hi, hY⟩ := hasDerivAt_det (by simp [*]) ((h.const_mul (1 - posProj ε)).const_add
    (posProj ε)), h.differentiableAt.inverse (by simp),
    ((h.star.mul_const (diagonal _)).mul h).unique (funext (γ · |>.2) ▸ hasDerivAt_const ..)
  have hD P : DifferentiableAt ℝ (fun t ↦ realWeil (γ t) (polyVector ε P)) 0 := by
    have' := hd.differentiableAt.star.smul (((differentiableAt_superposition ε P (fun (a, b) (_,
      y) ↦ (a *ᵥ y + posProj ε *ᵥ (star y ᵥ* b - a *ᵥ y), -(star y ᵥ* b ⬝ᵥ a *ᵥ y) / 2))
      ..).restrictScalars ℝ).comp 0 (hi.prodMk hi.star))
    simpa [star_mulVec, weilRep_eq_integral, ← principalMinor_sign_eq_det, holCoord, realVac] using!
      this
    repeat fun_prop [mulVec, vecMul, dotProduct]
    repeat simp [star_trivial, *, smul_vecMul, field, ← smul_sub, holCoord]
  let B := (modelInner.toLinearMap₁₂ ∘ₛₗ polyVector ε).compl₂ (⟨⟨fun P ↦ deriv ((realWeil ∘
    γ) · P) 0, by simp [*]⟩, by simp [*, deriv_fun_const_smul]⟩ - polyVector ε ∘ₗ weilDeriv ε Y)
  have hB Q P := (hD P).hasDerivAt.map_clm (modelInner (polyVector ε Q))
  have : B 1 1 = 0 := by
    have := (hB 1 1).unique (by simpa [principalMinor_sign_eq_det, *] using! hd.inv)
    simp_all [B, weilDeriv, trace, mul_apply, ← valueAt_apply, glOp, posProj, ← sum_neg_distrib]
    congr! 2; clear * -; aesop (add simp [raiseOp, lowerOp, realVac])
  have e j P Q : B Q (raiseOp ε j P) = ε j * B (lowerOp ε j Q) P ∧
      ε j * B Q (lowerOp ε j P) = B (raiseOp ε j Q) P := by
    obtain ⟨hγ, a⟩ := (hasDerivAt_pi.1 <| hasDerivAt_pi.1 h ·),
      fockMatrixCoeff_raiseOp_lowerOp (γ 0)
    have := ((hB Q _).prodMk ((hB ..).const_mul _)).unique ((funext fun t ↦ Prod.mk_inj.2
      (fockMatrixCoeff_raiseOp_lowerOp (γ t) ..)) ▸ (HasDerivAt.fun_sum fun _ _ ↦
      ((hγ _ j).mul_const _).mul (hB _ P)).prodMk (.fun_sum fun _ _ ↦ (hγ ..).star.mul (hB ..)))
    simp [h0, add_eq_zero_iff_eq_neg, ← ext_iff, forall_and] at *
    simp [B, canonical_commutation, this, hY, weilDeriv, glOp, DFunLike.ite_apply,
      apply_ite (DFunLike.coe _), mul_add, a.1, ← a.2, mul_sub, ← mul_assoc, mul_sum]; ring_nf; simp
  refine sub_eq_zero.1 (eq_zero_of_modelInner_self (isClosed_property denseRange_polyVector
    (modelInner.flip _).isClosed_ker (?_ : ∀ Q, B Q P = 0) _)) ▸ (hD P).hasDerivAt
  apply P.induction_on <;> intros
  induction ‹_› using MvPolynomial.induction_on
  all_goals (try specialize e ‹_›; have := e 1; cases Int.units_eq_one_or (ε ‹_›)) <;> simp_all
    [MvPolynomial.C_eq_smul_one, -mul_eq_zero, mul_add, raiseOp, lowerOp, mul_comm, @eq_comm ℂ 0]

open MvPolynomial ComplexOrder Kronecker MatrixOrder Fintype Algebra.TensorProduct
  NonUnitalStarAlgHom
variable {R C : Type} [Fintype R] [Fintype C] (ε : R → _) (ε' : C → _)

/-- The homomorphism (g, h) ↦ h ⊗ (g⁻¹)ᵀ, that is x ↦ hxg⁻¹ on R×C matrices, from U(ε′) × U(ε)
to the unitary group of the signs ε_rε′_c. -/
noncomputable def pairHom : USign ε' × USign ε →* USign (pairSign 1 ε ε') :=
  U.kron IsHermInvolution.mul_self (by simp [signMatrix, pairSign, diagonal]; aesop)

attribute [local simp] pairHom pairSign smul_smul kroneckerBilinear canonical_commutation

/-- For g in U(ε′) and h in U(ε), the ℓ² operator norm of the matrix of x ↦ hxg⁻¹ is at most
‖g‖·‖h‖. -/
lemma norm_pairHom_le g h : ‖(pairHom ε ε' (g, h)).1.1‖ ≤ ‖g.1.1‖ * ‖h.1.1‖ := by
  let k := (kroneckerStarAlgEquiv R C ℂ).toStarAlgHom
  convert! norm_mul_le_of_le ((norm_apply_le (k.comp ⟨includeRight.comp (transposeAlgEquiv
    ..).symm.toAlgHom, ?_⟩) _).trans_eq (U.norm_inv g)) (norm_apply_le (k.comp ⟨includeLeft, ?_⟩) _)
  erw [← mul_kronecker_mul]; repeat aesop

variable {ε ε'} (f : USign ε →* USign ε') (γ : ℤ)

/-- For a homomorphism f: U(ε) → U(ε′) and an integer γ, the representation g ↦ det(g)^γ
ω₀(f(g)) of U(ε) on the Fock space of ε′. -/
@[simps] noncomputable def detTwist := MonoidHom.mk ⟨fun g ↦
  g.1.1.det ^ γ • realWeil (f g), by simp⟩ (by simp [mul_zpow, mul_comm])

variable {f γ}

/-- For a continuous homomorphism f: U(ε) → U(ε′) with ‖f(g)‖ ≤ a‖g‖, ε′ indexed by C, the Fock
representation g ↦ det(g)^γ ω(f(g)) is strongly continuous, of norm O(‖g‖^{|C|}), and
preserves the positive definite hermitian form ∫ c̄c′. -/
lemma isUnitaryRep_detTwist {a} (hn : ∀ {g}, ‖(f g).1.1‖ ≤ a * ‖g.1.1‖) (hf : Continuous f := by
  rw [continuous_U_iff_matrix]; fun_prop [kroneckerMap]) : IsUnitaryRep (Fintype.card C) (detTwist f
  γ) realInner := ⟨by simp; fun_prop (disch := simp), by simp [field, ← mul_zpow, RCLike.mul_conj],
  conj_modelInner, fun _ ↦ by simp_intro _ [modelInner_self]; positivity ∘ mt
  eq_zero_of_modelInner_self, _, fun _ ↦ by simp [norm_smul, weilRep]; grw [norm_integrated_flip_le,
  mul_comm, realAction, norm_realMultiplier_le, hn, mul_pow, mul_assoc]⟩

lemma isDerivedAction_detTwist {ρ} F (c : ℤˣ) (hρ : ρ.ρ =
  weilDeriv ε' ∘ₗ F + (γ : ℂ) • (traceLinearMap ..).smulRight 1) (h : ∀ Y, f (expU Y) =
  c • F (NormedSpace.exp (c • Y.1))) : IsDerivedAction (detTwist f γ) (polyVector ε') ρ :=
  fun _ _ ↦ by apply (((hasDerivAt_zpow ..).comp 0 (hasDerivAt_det _ (hasDerivAt_exp_smul_const
  ..))).smul (hasDerivAt_realWeil _ (by simpa [h, smul_comm c] using!
  (hasDerivAt_exp_smul_const ..).map_clm (.mk (c • F))) _)).congr_deriv <;> aesop

/-- Suppose z and f(z) are positive definite, diag(d) commutes with f(z), and P ≠ 0 is killed by
∂_i∂_j whenever d_i = d_j and ε′_i ≠ ε′_j. Then ⟨v_P, π(z)v_P⟩ is a positive real, π being
the twisted action `detTwist` f γ. -/
lemma realInner_detTwist_pos {κ} (d : C → κ) {P z} : P ≠ 0 ∧ z.1.1.PosDef ∧ (f z).1.1.PosDef ∧ (∀ i
  j, d i ≠ d j → (f z).1 i j = 0) ∧ (∀ i j, d i = d j ∧ ε' i ≠ ε' j → pderiv i (pderiv j P) = 0) →
  0 < realInner (polyVector _ P) (detTwist f γ z P) := fun ⟨_, hz, hu, hd, hP⟩ ↦ by
  simp [zpow_pos hz.det_pos]
  have ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.1 (by simp [complexLinearPart,
    add_nonneg, apply_ite, conjugate_nonneg_of_nonneg, le_iff, hu.posSemidef, posProj] :
    0 ≤ complexLinearPart (f z)).posSemidef.inv.nonneg
  erw [← fockMatrixCoeff, fockMatrixCoeff_eq_realInner _ hd P hP P hP, hb, linSubst_mul,
    realInner_polyVector, map_linSubst, ← fockPairing_linSubst]
  exact mul_pos (inv_pos.2 (hu.submatrix (by simp)).det_pos) (fockPairing_star_self_pos ((congrArg
    (linSubst (complexLinearPart (f z)) ∘ linSubst b)).mt (by simpa [← linSubst_mul, ← hb])))

variable {ι} [Fintype ι] {η : ι → _} (T : FockDualPair ε ε' ι) (π :
  USign ε →* fockSpace η →L[ℂ] fockSpace η)

/-- π is a continuous unitary representation of U(ε) on Fock space, of norm O(‖g‖^{|R||C|}),
with derivative `oscRows` on polynomials, and ⟨v_P, π(z)v_P⟩ > 0 for z positive definite, P
≠ 0 satisfying `IsHarmonic`. -/
structure OscillatorRep where
  unitary_rep : IsUnitaryRep (Fintype.card ι) π realInner
  derives : IsDerivedAction π (polyVector η) T.oscRows
  inner_pos P z : P ≠ 0 → T.IsHarmonic P → z.1.1.PosDef → 0 < realInner P (π z P)

/-- Commuting representations π of U(ε) and π′ of U(ε′) on one Fock space, each a `OscillatorRep`:
π for the rows of T, π′ for the columns (`FockDualPair.swap`). -/
structure OscillatorPair π' extends OscillatorRep T π where
  column_rep : OscillatorRep T.swap π'
  commute g h : Commute (π g) (π' h)

/-- On the Fock space of R×C matrices with signs ε_rε′_c, the representations h ↦ (det h)^γ
ω(x ↦ hx) of U(ε) and g ↦ (det g)^γ′ ω(x ↦ xg⁻¹) of U(ε′) form a `OscillatorPair` with σ = 1 and
constants γ, γ′ + |R| (`FockDualPair.std`). -/
lemma oscillatorPair_detTwist {γ'} : OscillatorPair (.std ε ε' γ γ') (detTwist ((pairHom ..).comp
  (.inr ..)) γ) (detTwist ((pairHom ..).comp (.inl ..)) γ') := by use ⟨isUnitaryRep_detTwist
  (norm_pairHom_le ..), isDerivedAction_detTwist (kroneckerBilinear.flip 1) 1 (ext_linearMap _ ?_)
  ?_, fun _ _ _ _ _ ↦ realInner_detTwist_pos (·.2) ?_⟩, ⟨isUnitaryRep_detTwist ((norm_pairHom_le
  ..).trans_eq (by ring)), isDerivedAction_detTwist (-kroneckerBilinear 1 ∘ₗ (transposeLinearEquiv
  ..).1) (-1) (ext_linearMap _ ?_) ?_, fun _ _ _ _ _ ↦ realInner_detTwist_pos (·.1) ?_⟩ <;> simp_all
  [swap_oscRows_E, weilDeriv, LinearMap.ext_ring_iff, commute_iff_eq, mul_comm, ← map_mul, exp_neg,
  PosDef.kronecker, PosDef.one, sum_prod_type, single_apply, ite_and] <;> aesop (add simp [oscRows,
  add_comm, DFunLike.ext_iff, smul_eq_C_mul])

lemma principalMinor_kronecker_one g p [@DecidablePred (R × C) p] : principalMinor (g ⊗ₖ 1) p = ∏ c,
  principalMinor g (p ⟨·, c⟩) := by
  erw [kronecker_one, ← principalMinor_submatrix (.prodComm ..), principalMinor_blockDiagonal]; rfl
