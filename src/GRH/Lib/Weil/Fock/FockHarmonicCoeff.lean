import GRH.Lib.GLn.SchurModule.Nabla
import GRH.Lib.DiscreteSeries.CuspKernel.CircleMean
import GRH.Lib.DiscreteSeries.Theta.OscillatorDefs
import GRH.Lib.Weil.Fock.MixedFockModel
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known
result; see Lib.Weil.Fock.OscillatorPair).

This file: Functional bounded by its small-shift differences decays as any power of the shift. Fock
inner product equals Fischer product; polynomials dense; intertwining relations for coefficients.
Matrix coefficients of the oscillator representation between harmonic polynomials. -/

open Complex ComplexConjugate Finset Matrix MvPolynomial Sgn Heisenberg.IsVacuum

variable {ι} [Fintype ι] {ε : ι → _} (u : USign ε) (P Q : MvPolynomial ι ℂ) {κ : Sort*}

/-- For each N some C gives ‖ℓ v‖ₑ ≤ C‖ℓ‖tᴺ·weightedNorm N v for all v in 𝓕, t ≥ 0 and bounded
functionals ℓ such that, if t < 1, |ℓw| ≤ sup over ‖y‖ ≤ t of |ℓw − ℓ(ϱ(y)w)| for every w. -/
lemma exists_enorm_le_mul_weightedNorm_of_sub N : ∃ C : NNReal, ∀ t (ℓ : @fockSpace ι _ ε →L[ℂ] ℂ)
  {v}, 0 ≤ t → (t < 1 → ∀ v B, (∀ y, ‖y‖ ≤ t → ‖ℓ v - ℓ (realHeisOp y v)‖ ≤ B) → ‖ℓ v‖ ≤
  B) → ‖ℓ v‖ₑ ≤ .ofReal (C * ‖ℓ‖ * t ^ N) * weightedNorm N v := by
  let u | (y, w) => (vacVector : fockSpace ε) + -(realHeis ε).β w 1 ^ 2 • realHeisOp y vacVector
  have ⟨n, _, H⟩ := Metric.nhds_basis_closedBall_inv_nat_pos.mem_iff.1 ((by fun_prop : ContinuousAt
    (fun p ↦ ENNReal.ofNNReal (‖u p‖₊ * ((1 + (1 + ‖p.1‖₊) ^ (2 * N)) * (weightedNorm (2 * N)
    (vacVector : fockSpace ε)).toNNReal))) 0).eventually_lt_const (u := 2⁻¹ ^ 2) (by simp [u, sq]))
  refine ⟨‖(vacVector : fockSpace ε)‖₊ * n ^ N, fun t ℓ _ _ hL ↦ norm_le_weightedNorm N
    (le_of_halving (by grw [ℓ.le_opNorm, Heisenberg.Rep.norm_map _ ·]; bound) (by bound) fun M hM h
    z ↦ (lt_or_ge t (n * (1 + ‖z‖))⁻¹).imp (fun l ↦ (div_le_iff₀ (by positivity)).2 (hL
    (l.trans_le (by bound)) _ _ fun y hy ↦ ?_)) (by grw [ℓ.le_opNorm, ← ·]; simp [field, mul_pow]))⟩
  convert ENNReal.toReal_mono (by finiteness) (le_mul_of_le_mul_left (norm_le_weightedNorm N h)
    (le_mul_of_le_mul_left (weightedNorm_realHeisOp_le N (u (y, y * Star.star z)) z)
    (lt_of_pow_lt_pow_left' 2
    ((@H (y, y * Star.star z) (by simp; grw [norm_mul_le, hy, l]; simp [field])).trans_le' _)).le))
  simp [u, realHeis, ← exp_add, dotProduct, signMatrix, smul_smul, sq]; ac_nf; ring
  repeat simp [ENNReal.toReal_add, field, hM, isRapidDatum_vacVector _, ← enorm_eq_nnnorm, add_mul]
  grw [← weightedNorm_realHeisOp_le,
    ← weightedNorm_zero]; erw [← MeasureTheory.lintegral_add_left]; apply sq_lintegral_le
  any_goals fun_prop
  intro; simp [u, -neg_smul, sq]; nth_grw 1 [enorm_add_le]; simp [← ofReal_norm]; ring; rfl

@[simp] lemma realWeil_vacVector_zero : realWeil u vacVector 0 = (principalMinor u (ε · =
  -1))⁻¹ := by erw [eq_inv_of_mul_eq_one_right (conj_delta_mul_weilRep_vacElem ..), conj_conj]

/-- The matrix coefficient ⟨v_P, ω₀(u)v_Q⟩ on Fock space, conjugate-linear in P, for u in U(ε)
and complex polynomials P, Q with Fock vectors v_P, v_Q (`polyVector`). -/
@[simp] noncomputable abbrev fockMatrixCoeff := realInner P (realWeil u Q)

lemma fockMatrixCoeff_raiseOp_lowerOp j : fockMatrixCoeff u Q (raiseOp ε j P) = ∑ i,
  u.1 i j * ε i * fockMatrixCoeff u (lowerOp ε i Q) P ∧ ε j * fockMatrixCoeff u Q
  (lowerOp ε j P) = ∑ i, conj (u.1 i j) * fockMatrixCoeff u (raiseOp ε i Q) P := by
  have h c :=
    ((hasDerivAt_realHeisOp (Pi.single j c) P).map_clm (realInner Q ∘L realWeil u)).unique (by
    convert ((hasDerivAt_realHeisOp (-c • col u j) Q).map_clm (modelInner _)).star
    simp [weilRep_heisOp, conj_modelInner]; convert modelInner_heisOp ..; simp)
  simp_all [heisDeriv, conj_modelInner, apply_ite, mul_assoc, ← mul_sum]
  grind [I_sq, h 1, conj_I]

lemma realInner_X_mul i : realInner (polyVector ε (X i * P)) Q =
  realInner (polyVector ε P) (pderiv i Q) :=
  (fockMatrixCoeff_raiseOp_lowerOp (ε := ε) 1 Q P i).elim (by aesop (add simp [raiseOp, lowerOp]))

/-- For polynomials P, Q, the inner product ⟨v_P, v_Q⟩ equals (P̄(∂)Q)(0), where P̄ has the
complex conjugate coefficients of P. -/
lemma realInner_polyVector {ι} [Fintype ι] {ε : ι → ℤˣ} (P : MvPolynomial ι ℂ) :
    ∀ Q, realInner P (polyVector ε Q) = fockPairing ℂ (map conj P) Q := by apply P.induction_on <;>
                    simp_all [fockPairing_C, realVac, congr(polyVector _ $C_eq_smul_one),
  ← fockPairing_mul_X, mul_comm _ (X _), realInner_X_mul]

/-- The vectors v_P = P(ζ)·exp(−|x|²/2), P a complex polynomial, are dense in the Fock space 𝓕. -/
lemma denseRange_polyVector : DenseRange (polyVector ε) := let V := (polyVector ε).range.closure
  have := V.2; (V.ker_mkQ.le congr($((hom_ext fun _ ↦
    V.ker_mkQ.ge ((exists_tendsto_weightedNorm fun _ ↦ ENNReal.mul_ne_top (by simp)
    (isRapidDatum_vacVector _) ∘ eq_top_mono (weightedNorm_realHeisOp_le ..)).elim fun _ h ↦
  mem_closure_of_tendsto (by simpa [weightedNorm_zero, enorm_sub_rev,
    tendsto_iff_enorm_sub_tendsto_zero] using h 0) (by simp)) : V.mkQL = 0)) ·))


/-- For u in U(diag ε) with positive block a and negative block d, the block diagonal matrix
with blocks a and the entrywise conjugate of d. -/
noncomputable def complexLinearPart :=
  posProj ε * u * posProj ε + posProj (-ε) * u.1.1ᴴᵀ * posProj (-ε)

attribute [local simp] mul_sum sum_mul C_eq_smul_one coeff_homogeneousComponent coeff_pderiv
  complexLinearPart realInner_X_mul linSubst neg_eq_iff_eq_neg raiseOp lowerOp posProj realVac

noncomputable instance : Invertible (complexLinearPart u) :=
  invertibleOfIsUnitDet _ <| have := (realAction ε).7 u u
  by rw [twoBlockTriangular_det₀ _ (ε · = -1), (_ : _ * _ = realMultiplier u * principalMinor u
    (¬ε · = -1)), U.principalMinor_compl] <;> aesop (add simp [toSquareBlockProp, principalMinor,
    realMultiplier, RingHom.map_det, realAction, (u.1.det_ne_zero)], 1% congr)

lemma harmonic_induction {r : Rel ι ι} (S : Submodule ℂ (MvPolynomial ι ℂ)) (h1 : 1 ∈ S)
    (h : ∀ j, ∀ P ∈ S, (∀ i, r i j → pderiv i P = 0) → X j * P ∈ S) P (hP : ∀ i j, r i j → pderiv
    i (pderiv j P) = 0) : P ∈ S := P.sum_homogeneousComponent ▸ sum_mem (by
  rintro n -; induction' n with n i generalizing P; aesop
  rw_mod_cast [← S.smul_mem_iff (NeZero.natCast_ne n.succ ℂ),
    ← (homogeneousComponent_mem ..).sum_X_mul_pderiv]
  convert sum_mem fun j _ ↦ h j _ (i (P.pderiv j) (by grind [_root_.pderiv_comm])) _ <;>
    simp_all [MvPolynomial.ext_iff])

attribute [local instance] Prop.linearOrder in
/-- Let u in U(ε) be block diagonal for labels d, A = (`complexLinearPart` u)⁻¹. If ∂_iQ = 0 for
all i with d_i = d_j, ε_i ≠ ε_j, then ⟨v_{X_jQ}, ω₀(u)v_P⟩ = ∑_i conj(A_ij) ⟨v_Q,
ω₀(u)v_{∂_iP}⟩. -/
lemma fockMatrixCoeff_X_mul {d : ι → κ} (hd : ∀ i j, d i ≠ d j → u.1 i j = 0) P {Q j}
    (h : ∀ i, d i = d j ∧ ε i ≠ ε j → pderiv i Q = 0) : fockMatrixCoeff u (X j * Q) P = ∑ i,
  (complexLinearPart u)ᴴ⁻¹ j i * fockMatrixCoeff u Q (pderiv i P) := by apply
                          (congrFun (inv_mulVec_eq_vec rfl) j).symm.trans (sum_congr rfl fun i _ ↦
  mul_eq_mul_left_iff.2 ((em' _).imp (fun _ ↦ (fockMatrixCoeff_raiseOp_lowerOp u P Q i).elim
  (by cases Int.units_eq_one_or (ε j) <;> simp_all
  [← sum_neg_distrib, mulVec, dotProduct] <;> congr! 1 <;> by_cases d ‹_› = d j <;> aesop))
  (blockTriangular_inv_of_blockTriangular (b := fun i ↦ d i = d j ∧ ε i = ε j) (by aesop_cat) ·)))

variable {ι : Type} [Fintype ι] {ε : ι → _} (u : USign ε)

/-- Let u in U(ε) be block diagonal for labels d, and ∂_i∂_j kill P, Q whenever d_i = d_j, ε_i ≠
ε_j. Then ⟨v_Q, ω₀(u)v_P⟩ = (det u₋)⁻¹⟨v_Q′, v_P⟩, u₋ the negative block, Q′ = Q under X_j ↦
∑_i A_ij X_i, A = (`complexLinearPart` u)⁻¹.

Known result: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q). -/
lemma fockMatrixCoeff_eq_realInner {κ} {d : ι → κ} (hd : ∀ i j, d i ≠ d j → u.1 i j = 0)
    : let K := {P | ∀ i j, d i = d j ∧ ε i ≠ ε j → pderiv i (pderiv j P) = 0}
  ∀ Q ∈ K, ∀ P ∈ K, fockMatrixCoeff u Q P = (principalMinor u (ε · = -1))⁻¹ * realInner
    (polyVector ε (linSubst (complexLinearPart u)⁻¹ Q)) P := by
  refine harmonic_induction ⟨⟨⟨{Q | _}, ?_⟩, ?_⟩, ?_⟩ (harmonic_induction ⟨⟨⟨{P | _}, ?_⟩, ?_⟩, ?_⟩
    ?_ fun _ _ _ h ↦ star_inj.1 (by simpa [conj_modelInner, -polyVector_one, rep_apply_apply] using
    (modelInner_weilRep (realAction ε) u ..).trans (fockMatrixCoeff_X_mul u⁻¹ (by
    simp [↓U.coe_inv IsHermInvolution.mul_self, signMatrix]; tauto) 1 h))) ?_ <;> simp_all
    [fockMatrixCoeff_X_mul u hd, ↓← conjTranspose_nonsing_inv] <;> clear * - <;>
    grind [_root_.pderiv_comm]
