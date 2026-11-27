/- GID: D5/S3/Zeros/GRH/Lib/Weil/Fock/FockVacuum
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Fock/FockVacuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Fock.FockVacuum. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Fock/FockVacuum.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Haar.UnitaryNorm
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known
result; see Lib.Weil.Fock.OscillatorPair).

This file: Sign projections, real multiplier as conjugate determinant of negative block, its norm
bound. The Gaussian is a reproducing vacuum; integrability and polynomial growth bounds. -/

open Matrix Fintype Norms.L2Operator Sgn MeasureTheory Complex ComplexOrder Finset MvPolynomial

section

variable {ι} [Fintype ι] {ε : ι → _} (u : USign ε)

attribute [local simp] posProj signMatrix

@[simp] lemma posProj_mul_self : posProj ε * posProj ε = posProj ε ∧ (posProj ε)ᴴ = posProj ε ∧
  (signMatrix ε)ᴴ = signMatrix ε := by simp

omit [Fintype ι] in
lemma signMatrix_eq_posProj_sub : signMatrix ε = posProj ε - (1 - posProj ε) := by aesop

lemma principalMinor_sign_eq_det u : principalMinor u (ε · = -1) = (posProj ε + (1 - posProj ε) *
  u).det := by rw [principalMinor_eq_det, sub_mul, congrArg det]; aesop

attribute [simp] signMatrix_mul_self

/-- For u in the unitary group U(ε), the complex conjugate of the determinant of the
negative–negative block d of u. -/
noncomputable def realMultiplier := starRingEnd _ (principalMinor u (ε · = -1))

lemma norm_realMultiplier_le : ‖realMultiplier u‖ ≤ ‖u.1.1‖ ^ Fintype.card
  ι := by cases isEmpty_or_nonempty ι <;> simp [realMultiplier, norm_principalMinor_le_pow.trans,
  pow_le_pow_right₀, U.one_le_norm, card_subtype_le]

end

variable {ι} [Fintype ι] {ε : ι → _} (x y) (P : MvPolynomial ι ℂ)

attribute [local simp] holCoord_eq realHeis realVac sum_div signMatrix_eq_posProj_sub

attribute [local simp ←] exp_add sum_neg_distrib integral_const_mul sum_add_distrib sum_sub_distrib

lemma beta_mul_realVac : (realHeis ε).β y x * realVac (x - y) = realVac x * realVac y * exp
  (star (holCoord ε y) ⬝ᵥ holCoord ε x) := by simp [posProj, dotProduct]; grind [conj_conj]

/-- For every real C, the function u ↦ exp(C‖u‖) exp(−|u|²/2) on ℂ^ι, with ‖u‖ the maximum norm
and |u| the Euclidean norm, is integrable for the normalised Lebesgue measure `realMeasure`. -/
lemma integrable_exp_mul_realVac C : Integrable (fun u ↦ (C * ‖u‖).exp * ‖realVac u‖) (realMeasure
  ι) := .mono (.smul (C * C).exp (.of_integral_ne_zero ((integral_gauss (A := scalar ι 4⁻¹)
  (by norm_num [IsAccretive]) 0).trans_ne (by simp)))) (by fun_prop [realVac]) (.of_forall (by
    simp_intro u [← Real.exp_add]; bound [norm_sq_le_re_star_dot u, sq_nonneg (‖u‖ - 2 * C)]))

instance isVacuum_realVac :
  (realHeis ε).IsVacuum (realMeasure ι) realVac := by refine' ⟨by fun_prop [realVac], _, _, _, fun y
  x ↦ by convert congr(realVac y * realVac x * $((integral_add_right_eq_self _ (y - posProj ε *ᵥ
  (x + y))).trans (integral_gauss PosDef.one.isAccretive (-signMatrix ε *ᵥ (x + y))))) using 1 <;>
  simp [star_mulVec_dotProduct]; grind, (integrable_exp_mul_realVac 0).mono' (by fun_prop [realVac])
  _⟩ <;> simp [star_dot_self_eq_sum, ← exp_conj, map_ofNat]

@[simp] lemma norm_holCoord : ‖holCoord ε y‖ = ‖y‖ ∧ ∀ i, ‖holCoord ε y i‖ = ‖y i‖ := by simp [norm,
  apply_ite]

lemma exists_norm_eval_le_exp : ∃ k C, ∀ l, ‖eval l P‖ ≤ |C| * .exp ((k : ℕ) * ‖l‖) :=
  ⟨_, _, fun l ↦ by
  grw [eval_eq', norm_sum_le, ← le_abs_self, ‖l‖.exp_nat_mul, sum_mul]; simp
  grw [norm_le_pi_norm l, ‖l‖.le_exp_log, Real.log_le_self, P.monomial_le_degreeOf,
    prod_pow_eq_pow_sum] <;> bound⟩
