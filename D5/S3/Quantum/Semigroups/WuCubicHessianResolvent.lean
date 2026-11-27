import D5.S3.Quantum.Semigroups.WuCubicHotInnerDiagonalHessian

/-! The resolvent upper bound for the cubic-log trace coefficient in Wu v1,
Remark 3.15 (3.54). The trace gap is the positive quadratic form of the
resolvent on its commutator with the direction. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicHessianResolvent

open WuCubicHotInnerEntropy (cubicPolynomial shiftedRoot)
open WuCubicHotInnerDiagonalHessian (scalarSecond integral_scalarSecond)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact complex trace gap for a Hermitian resolvent and direction. -/
theorem trace_resolvent_sub (P W : Matrix n n ℂ)
    (hP : IsSelfAdjoint P) (hW : IsSelfAdjoint W) :
    (W^2 * P^3).trace - (P*W*P*W*P).trace =
      (star (P*W-W*P) * P * (P*W-W*P)).trace := by
  have h₁ : (W*P^3*W).trace = (W^2*P^3).trace := by
    rw [Matrix.trace_mul_comm (W*P^3) W, ← mul_assoc, ← pow_two]
  have h₂ : (W*(P^2*W*P)).trace = (P^2*W*P*W).trace := Matrix.trace_mul_comm _ _
  have h₃ : ((P*W)*(P^2*W)).trace = (P^2*W*P*W).trace := by
    rw [Matrix.trace_mul_comm, mul_assoc (P^2*W)]
  have h₄ : (P*W*P*W*P).trace = (P^2*W*P*W).trace := by
    rw [Matrix.trace_mul_comm (P*W*P*W) P, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_two]
  rw [star_sub, star_mul, star_mul, hP.star_eq, hW.star_eq,
    show (W*P-P*W)*P*(P*W-W*P) =
      W*P^3*W - W*(P^2*W*P) - (P*W)*(P^2*W) + P*W*P*W*P by noncomm_ring]
  simp only [Matrix.trace_add, Matrix.trace_sub, h₁, h₂, h₃, h₄]
  ring

/-- Sharp resolvent trace bound. Equality holds precisely when the two
matrices commute if the resolvent is positive definite. -/
theorem trace_resolvent_le (P W : Matrix n n ℂ)
    (hP : P.PosDef) (hW : IsSelfAdjoint W) :
    (P*W*P*W*P).trace.re ≤ (W^2*P^3).trace.re ∧
      ((P*W*P*W*P).trace.re = (W^2*P^3).trace.re ↔ Commute P W) := by
  let C := P*W-W*P
  obtain ⟨S, hS, hPS⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hP.isStrictlyPositive
  have hgram : star C * P * C = (S*C)ᴴ * (S*C) := by
    rw [hPS, ← Matrix.star_eq_conjTranspose, star_mul]
    noncomm_ring
  have hpos := Matrix.posSemidef_conjTranspose_mul_self (S*C)
  have hgap := congrArg Complex.re (trace_resolvent_sub P W hP.isHermitian.isSelfAdjoint hW)
  change _ - _ = (star C * P * C).trace.re at hgap
  rw [hgram] at hgap
  have htrace := Complex.nonneg_iff.mp hpos.trace_nonneg
  refine ⟨sub_nonneg.mp (hgap.symm ▸ htrace.1), ?_⟩
  constructor
  · intro he
    have hre : ((S*C)ᴴ * (S*C)).trace.re = 0 := by rw [← hgap, he, sub_self]
    have hz : ((S*C)ᴴ * (S*C)).trace = 0 :=
      Complex.ext hre (by simpa using htrace.2.symm)
    have hSC := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hz
    obtain ⟨u, rfl⟩ := hS
    have hC : C = 0 := by
      simpa [← mul_assoc] using congrArg (fun X => (↑u⁻¹ : Matrix n n ℂ) * X) hSC
    exact sub_eq_zero.mp hC
  · intro hc
    have hC : C = 0 := sub_eq_zero.mpr hc.eq
    apply (sub_eq_zero.mp ?_).symm
    rw [hgap, hC]
    simp

omit [DecidableEq n] in
private theorem trace_real_smul (r : ℝ) (X : Matrix n n ℂ) :
    (r • X).trace.re = r * X.trace.re := by
  rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

omit [Fintype n] in
private theorem shift_posDef (M : Matrix n n ℂ) (hM : M.PosDef) {l : ℝ} (hl : 0 < l) :
    (M + l • (1 : Matrix n n ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add hM.posSemidef (Matrix.PosDef.one.smul hl)

private theorem shiftedRoot_sq (M : Matrix n n ℂ) (hM : M.PosDef) {l : ℝ} (hl : 0 < l) :
    (shiftedRoot M l)^2 = (M+l • (1 : Matrix n n ℂ))⁻¹ := by
  let T := shiftedRoot M l
  have h := WuCubicHotInnerResolvent.shift_inverse_sqrt_congruence M hM.posSemidef l hl
  change T * (M+l • 1) * T = 1 at h
  apply Eq.symm
  apply Matrix.inv_eq_right_inv
  rw [pow_two, ← mul_assoc]
  exact mul_eq_one_comm.mp (by simpa only [mul_assoc] using h)

/-- Coefficient of `t²` in the ordinary trace of the existing cubic polynomial. -/
def quadraticCoeff (M W : Matrix n n ℂ) (l : ℝ) : ℝ :=
  let P := (M+l • (1 : Matrix n n ℂ))⁻¹
  3*(1+l)⁻¹ * (W^2*M).trace.re - (W^2).trace.re + l^3*(P*W*P*W*P).trace.re

/-- The centered polynomial difference extracts exactly twice the quadratic coefficient. -/
theorem cubicPolynomial_centered (M W : Matrix n n ℂ) (hM : M.PosDef)
    {l : ℝ} (hl : 0 < l) (t : ℝ) :
    (cubicPolynomial M (t • W) l).trace.re +
      (cubicPolynomial M ((-t) • W) l).trace.re -
      2*(cubicPolynomial M 0 l).trace.re = 2*t^2*quadraticCoeff M W l := by
  let T := shiftedRoot M l
  let P := (M+l • (1 : Matrix n n ℂ))⁻¹
  let L := (1+l)⁻¹ • (M^2*W + M*W*M + W*M^2) - (M*W + W*M) +
    l • W - l^3 • (T^2*W*T^2)
  let Q := (1+l)⁻¹ • (M*W^2 + W*M*W + W^2*M) - W^2 +
    l^3 • (T^2*W*T^2*W*T^2)
  let C := (1+l)⁻¹ • W^3 - l^3 • (T^2*W*T^2*W*T^2*W*T^2)
  have hpoly (s : ℝ) : cubicPolynomial M (s • W) l =
      cubicPolynomial M 0 l + s • L + s^2 • Q + s^3 • C := by
    simp only [cubicPolynomial, L, Q, C, T, pow_succ, pow_zero, one_mul, mul_one,
      add_zero, sub_zero, zero_mul, mul_zero, add_mul, mul_add, sub_mul, mul_sub,
      mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul, mul_assoc]
    module
  have hMW : (M*W^2).trace = (W^2*M).trace := Matrix.trace_mul_comm _ _
  have hWMW : (W*M*W).trace = (W^2*M).trace := by
    rw [Matrix.trace_mul_comm (W*M) W, ← mul_assoc, ← pow_two]
  have hQ : Q.trace.re = quadraticCoeff M W l := by
    dsimp only [Q, quadraticCoeff]
    rw [show T^2 = P from shiftedRoot_sq M hM hl]
    simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
      trace_real_smul, hMW, hWMW]
    ring
  rw [hpoly t, hpoly (-t)]
  simp only [Matrix.trace_add, Complex.add_re, trace_real_smul, ← hQ]
  ring

/-- Scalar pointwise majorant, in its integrable form. -/
def scalarMajorant (l x : ℝ) : ℝ := (1/2) * scalarSecond l x

theorem scalarMajorant_eq {l x : ℝ} (hx : 0 < x) (hl : 0 < l) :
    scalarMajorant l x = 3*x*(1+l)⁻¹ - 1 + l^3*((x+l)^3)⁻¹ := by
  have hxl := (add_pos hx hl).ne'
  unfold scalarMajorant scalarSecond
  field_simp [hxl]
  ring

theorem integral_scalarMajorant {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun l => scalarMajorant l x) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), scalarMajorant l x) = (5/2)*x + 3*x*Real.log x := by
  obtain ⟨hi, hv⟩ := integral_scalarSecond hx
  refine ⟨hi.const_mul _, ?_⟩
  rw [show (fun l => scalarMajorant l x) = fun l => (1/2 : ℝ)*scalarSecond l x from rfl,
    integral_const_mul, hv]
  ring

private theorem cfc_scalarMajorant (M : Matrix n n ℂ) (hM : M.PosDef)
    {l : ℝ} (hl : 0 < l) :
    cfc (scalarMajorant l) M =
      (3*(1+l)⁻¹ : ℝ) • M - 1 + l^3 • ((M+l • (1 : Matrix n n ℂ))⁻¹)^3 := by
  have hc (f : ℝ → ℝ) := M.finite_real_spectrum.continuousOn f
  have hh := hM.isHermitian.isSelfAdjoint
  have he : cfc (scalarMajorant l) M =
      cfc (fun x : ℝ => (3*(1+l)⁻¹*x - 1) + l^3*((x+l)⁻¹)^3) M := by
    apply cfc_congr
    intro x hx
    rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    dsimp only
    rw [scalarMajorant_eq (hM.eigenvalues_pos i) hl, inv_pow]
    ring
  rw [he, cfc_add M _ _ (hc _) (hc _), cfc_sub _ _ M (hc _) (hc _),
    cfc_const_mul_id _ M hh, cfc_const_one ℝ M hh, cfc_const_mul _ _ M (hc _),
    cfc_pow _ 3 M (hc _) hh,
    D5.S3.Quantum.Divergence.ResolventFunctionalRigidity.cfc_shift_inverse M hM.posSemidef l hl]

/-- The commutator gap gives a pointwise upper bound on the actual coefficient. -/
theorem quadraticCoeff_le (M W : Matrix n n ℂ) (hM : M.PosDef) (hW : IsSelfAdjoint W)
    {l : ℝ} (hl : 0 < l) :
    quadraticCoeff M W l ≤ (W^2 * cfc (scalarMajorant l) M).trace.re := by
  rw [cfc_scalarMajorant M hM hl, mul_add, mul_sub, mul_smul_comm, mul_smul_comm,
    mul_one, Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
    trace_real_smul, trace_real_smul, quadraticCoeff]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
    (trace_resolvent_le _ W (shift_posDef M hM hl).inv hW).1 (pow_nonneg hl.le 3))

private theorem trace_unitaryConj (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U X).trace = X.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

private theorem integrable_quadraticCoeff (M W : Matrix n n ℂ)
    (hM : M.PosDef) (hW : IsSelfAdjoint W) :
    IntegrableOn (quadraticCoeff M W) (Ioi 0) := by
  let e := hM.isHermitian.eigenvalues
  let B := diagonal (fun i => (e i : ℂ))
  let F := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.isHermitian.eigenvectorUnitary
  let V := F.symm W
  have hB : F B = M := hM.isHermitian.spectral_theorem.symm
  have hV : F V = W := F.apply_symm_apply W
  have hv : V.IsHermitian := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
    change star (F.symm W) = F.symm W
    rw [← map_star, hW.star_eq]
  have hshift (l : ℝ) : F (shiftedRoot B l) = shiftedRoot M l := by
    let f : ℝ → ℝ := fun x => Real.sqrt ((x+l)⁻¹)
    have hd : cfc f B = diagonal (fun i => (f (e i) : ℂ)) := by
      simpa only [B, Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
        using Matrix.cfc_diagonal_real (𝕜 := ℂ) e f
    change F (cfc f B) = cfc f M
    rw [hd, hM.isHermitian.cfc_eq]
    rfl
  have hpoly (s l : ℝ) : F (cubicPolynomial B (s • V) l) = cubicPolynomial M (s • W) l := by
    simp only [cubicPolynomial, map_add, map_sub, map_pow, map_mul, map_one,
      LinearMapClass.map_smul_of_tower F, hB, hV, hshift]
  have htrace (s l : ℝ) : (cubicPolynomial B (s • V) l).trace =
      (cubicPolynomial M (s • W) l).trace := by
    rw [← hpoly, trace_unitaryConj]
  have hi := (WuCubicHotInnerDiagonalHessian.integral_cubicPolynomial_centeredDifference
    e hM.eigenvalues_pos V hv 1).1
  dsimp only at hi
  simp only [zero_smul] at hi
  have he (l : ℝ) (hl : l ∈ Ioi 0) :
      (cubicPolynomial B ((1 : ℝ) • V) l).trace.re +
        (cubicPolynomial B (-(1 : ℝ) • V) l).trace.re -
        2*(cubicPolynomial B 0 l).trace.re = 2*quadraticCoeff M W l := by
    have hzero := htrace 0 l
    simp only [zero_smul] at hzero
    rw [htrace, htrace, hzero]
    simpa only [one_pow, mul_one] using cubicPolynomial_centered M W hM hl 1
  have htwo : IntegrableOn (fun l => 2 * quadraticCoeff M W l) (Ioi 0) :=
    hi.congr_fun he measurableSet_Ioi
  have hhalf : IntegrableOn (fun l => (1/2 : ℝ) * (2 * quadraticCoeff M W l)) (Ioi 0) :=
    htwo.const_mul _
  exact hhalf.congr_fun (fun l _ => by ring) measurableSet_Ioi

private theorem weighted_cfc_trace (M X : Matrix n n ℂ) (hM : M.IsHermitian)
    (f : ℝ → ℝ) :
    (X * cfc f M).trace.re =
      ∑ i, (((Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary).symm X) i i).re *
        f (hM.eigenvalues i) := by
  let F := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.eigenvectorUnitary
  have he : cfc f M = F (diagonal (fun i => (f (hM.eigenvalues i) : ℂ))) :=
    hM.cfc_eq f
  conv_lhs => rw [he, ← F.apply_symm_apply X, ← map_mul, trace_unitaryConj]
  change ((F.symm X) * _).trace.re = ∑ i, ((F.symm X) i i).re * f (hM.eigenvalues i)
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Matrix.mul_diagonal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private theorem integral_majorant (M X : Matrix n n ℂ) (hM : M.PosDef) :
    IntegrableOn (fun l => (X * cfc (scalarMajorant l) M).trace.re) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), (X * cfc (scalarMajorant l) M).trace.re) =
        (X * cfc (fun x : ℝ => (5/2)*x+3*x*Real.log x) M).trace.re := by
  let e := hM.isHermitian.eigenvalues
  let V := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hM.isHermitian.eigenvectorUnitary).symm X
  simp_rw [weighted_cfc_trace M X hM.isHermitian]
  have hi (i : n) : IntegrableOn (fun l => (V i i).re * scalarMajorant l (e i)) (Ioi 0) :=
    (integral_scalarMajorant (hM.eigenvalues_pos i)).1.const_mul _
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, (integral_scalarMajorant (hM.eigenvalues_pos i)).2]

/-- The integrated quadratic coefficient for the cubic-log trace with its
factor of three is bounded by the trace against `15M/2 + 9M log M`. -/
theorem integral_quadraticCoeff_le (M W : Matrix n n ℂ) (hM : M.PosDef)
    (hW : IsSelfAdjoint W) :
    IntegrableOn (quadraticCoeff M W) (Ioi 0) ∧
      3 * (∫ l in Ioi (0 : ℝ), quadraticCoeff M W l) ≤
        (W^2 * ((15/2 : ℝ) • M + (9 : ℝ) • (M * cfc Real.log M))).trace.re := by
  have hi := integrable_quadraticCoeff M W hM hW
  obtain ⟨hj, hv⟩ := integral_majorant M (W^2) hM
  refine ⟨hi, ?_⟩
  have hle := setIntegral_mono_on hi hj measurableSet_Ioi (fun l hl => quadraticCoeff_le M W hM hW hl)
  have hc (f : ℝ → ℝ) := M.finite_real_spectrum.continuousOn f
  have hh := hM.isHermitian.isSelfAdjoint
  have he : cfc (fun x : ℝ => (5/2)*x+3*x*Real.log x) M =
      (5/2 : ℝ) • M + (3 : ℝ) • (M * cfc Real.log M) := by
    rw [cfc_add M _ _ (hc _) (hc _), cfc_const_mul_id _ M hh]
    rw [show (fun x : ℝ => 3*x*Real.log x) = fun x => 3*(id x*Real.log x) by
      funext x
      dsimp only [id]
      ring]
    rw [cfc_const_mul _ _ M (hc _), cfc_mul id Real.log M (hc _) (hc _), cfc_id ℝ M hh]
  calc
    _ ≤ 3 * (∫ l in Ioi (0 : ℝ), (W^2 * cfc (scalarMajorant l) M).trace.re) :=
      mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = _ := by
      rw [hv, he]
      simp only [mul_add, mul_smul_comm, Matrix.trace_add, Complex.add_re, trace_real_smul]
      ring

open WuCubicHotInnerEntropy (entropyFactor entropyKernel entropyRemainder entropyRemainder_le
  integral_cubicLogIntegrand integrated_entropyKernel_le)
open WuCubicHotInnerResolvent (cubicLogIntegrand)
open private displaced_posDef entropyKernel_eq_sub from
  D5.S3.Quantum.Semigroups.WuCubicHotInnerEntropy

private theorem integrable_cubicPolynomial (M A : Matrix n n ℂ) (hM : M.PosDef)
    (hA : IsSelfAdjoint A) {bMinus bPlus : ℝ} (hb : 0 < bMinus) (hbb : bMinus ≤ bPlus)
    (hlo : bMinus • (1 : Matrix n n ℂ) ≤ M) (hhi : M ≤ bPlus • (1 : Matrix n n ℂ))
    (hAlo : (-(1/2 : ℝ)) • (1 : Matrix n n ℂ) ≤ A) :
    IntegrableOn (fun l => (cubicPolynomial M (CFC.sqrt M*A*CFC.sqrt M) l).trace.re) (Ioi 0) := by
  have hr : (1/2 : ℝ) < 1 := by norm_num
  have hy := displaced_posDef M A hM hr hAlo
  obtain ⟨hi, _⟩ := integral_cubicLogIntegrand _ hy
  obtain ⟨hk, _⟩ := integrated_entropyKernel_le M A hM hA hb hbb hlo hhi
    (by norm_num) hr hAlo
  refine (hi.sub (hk.const_mul (1/3 : ℝ))).congr_fun ?_ measurableSet_Ioi
  intro l hl
  have he := entropyKernel_eq_sub M A hM hr hAlo hl
  dsimp only at he
  simp only [Pi.sub_apply]
  rw [← he]
  ring

private theorem polynomial_zero_trace (M : Matrix n n ℂ) (hM : M.PosDef)
    {l : ℝ} (hl : 0 < l) :
    (cubicPolynomial M 0 l).trace.re = (cubicLogIntegrand l M).trace.re := by
  have h := WuCubicHotInnerResolvent.cubic_log_integrand_trace_fourth M 0 (shiftedRoot M l) l hl
    (by simpa only [add_zero] using hM.posSemidef)
    (WuCubicHotInnerResolvent.shift_inverse_sqrt_congruence M hM.posSemidef l hl)
  change (cubicLogIntegrand l (M+0)).trace - (cubicPolynomial M 0 l).trace =
    l^3 • ((M+l • 1)⁻¹ * ((shiftedRoot M l*0*shiftedRoot M l)^4 *
      (1+shiftedRoot M l*0*shiftedRoot M l)⁻¹)).trace at h
  simp only [add_zero, mul_zero, zero_mul, zero_pow (by decide : 4 ≠ 0),
    Matrix.trace_zero, smul_zero] at h
  exact congrArg Complex.re (sub_eq_zero.mp h).symm

/-- The actual centered cubic-log trace has the same quadratic upper bound,
with the signed fourth-order remainder controlled for both displacements.
Here the physical direction is `W = √M * A * √M`. -/
theorem cubicLog_centered_le [Nonempty n] (M A : Matrix n n ℂ) (hM : M.PosDef)
    (hA : IsSelfAdjoint A) {bMinus bPlus : ℝ} (hb : 0 < bMinus) (hbb : bMinus ≤ bPlus)
    (hlo : bMinus • (1 : Matrix n n ℂ) ≤ M) (hhi : M ≤ bPlus • (1 : Matrix n n ℂ))
    (t : ℝ) (hplus : (-(1/2 : ℝ)) • (1 : Matrix n n ℂ) ≤ t • A)
    (hminus : (-(1/2 : ℝ)) • (1 : Matrix n n ℂ) ≤ (-t) • A) :
    let W := CFC.sqrt M * A * CFC.sqrt M
    let g := fun s : ℝ => ((M+s • W)^3 * cfc Real.log (M+s • W)).trace.re
    3*(g t + g (-t) - 2*g 0) ≤
      2*t^2 * (W^2 * ((15/2 : ℝ) • M + (9 : ℝ) • (M*cfc Real.log M))).trace.re +
        2*t^4 * (entropyFactor bMinus bPlus (1/2) * (A^4).trace.re) := by
  intro W g
  let p := fun (s l : ℝ) => (cubicPolynomial M (s • W) l).trace.re
  let c := entropyFactor bMinus bPlus (1/2) * (A^4).trace.re
  let b := (W^2 * ((15/2 : ℝ) • M + (9 : ℝ) • (M*cfc Real.log M))).trace.re
  have hW : IsSelfAdjoint W := by
    have hS := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)
    change star (CFC.sqrt M * A * CFC.sqrt M) = CFC.sqrt M * A * CFC.sqrt M
    simp only [star_mul, hS.star_eq, hA.star_eq, mul_assoc]
  have hw (s : ℝ) : CFC.sqrt M * (s • A) * CFC.sqrt M = s • W := by
    rw [mul_smul_comm, smul_mul_assoc]
  have hlocal (s : ℝ) (hs : (-(1/2 : ℝ)) • (1 : Matrix n n ℂ) ≤ s • A) :
      IntegrableOn (p s) (Ioi 0) ∧
        3*(g s - ∫ l in Ioi (0 : ℝ), p s l) ≤ s^4*c := by
    have ha := IsSelfAdjoint.smul (show IsSelfAdjoint s from rfl) hA
    have hi := integrable_cubicPolynomial M (s • A) hM ha hb hbb hlo hhi hs
    rw [hw] at hi
    refine ⟨hi, ?_⟩
    have he := entropyRemainder_le M (s • A) hM ha hb hbb hlo hhi (by norm_num)
      (by norm_num) hs
    unfold entropyRemainder at he
    dsimp only at he
    rw [hw, smul_pow, trace_real_smul] at he
    have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hcard] at he
    change 3*(g s - ∫ l in Ioi (0 : ℝ), p s l) ≤ s^4*c
    simpa only [c, g, p, mul_left_comm] using he
  obtain ⟨hpi, hpe⟩ := hlocal t hplus
  obtain ⟨hmi, hme⟩ := hlocal (-t) hminus
  obtain ⟨hzi, hze⟩ := integral_cubicLogIntegrand M hM
  have he0 (l : ℝ) (hl : l ∈ Ioi 0) : p 0 l = (cubicLogIntegrand l M).trace.re := by
    simpa only [p, zero_smul] using polynomial_zero_trace M hM hl
  have hz : IntegrableOn (p 0) (Ioi 0) :=
    hzi.congr_fun (fun l hl => (he0 l hl).symm) measurableSet_Ioi
  have hv0 : (∫ l in Ioi (0 : ℝ), p 0 l) = g 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi he0, hze]
    simp only [g, zero_smul, add_zero]
  obtain ⟨_, hq⟩ := integral_quadraticCoeff_le M W hM hW
  have he (l : ℝ) (hl : l ∈ Ioi 0) :
      p t l + p (-t) l - 2*p 0 l = (2*t^2)*quadraticCoeff M W l := by
    simpa only [p, zero_smul] using cubicPolynomial_centered M W hM hl t
  have hpvalue :
      (∫ l in Ioi (0 : ℝ), p t l) + (∫ l in Ioi (0 : ℝ), p (-t) l) - 2*g 0 =
        (2*t^2) * (∫ l in Ioi (0 : ℝ), quadraticCoeff M W l) := by
    calc
      _ = ∫ l in Ioi (0 : ℝ), p t l + p (-t) l - 2*p 0 l := by
        have hs := integral_sub (hpi.add hmi) (hz.const_mul (2 : ℝ))
        simp only [Pi.add_apply] at hs
        rw [hs, integral_add hpi hmi, integral_const_mul, hv0]
      _ = _ := by rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul]
  have hpbound : 3 * ((∫ l in Ioi (0 : ℝ), p t l) + (∫ l in Ioi (0 : ℝ), p (-t) l) -
        2*g 0) ≤ (2*t^2)*b := by
    rw [hpvalue, mul_left_comm]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  rw [neg_pow, show Even (4 : ℕ) by decide |>.neg_one_pow, one_mul] at hme
  change 3*(g t + g (-t) - 2*g 0) ≤ 2*t^2*b + 2*t^4*c
  linarith only [hpe, hme, hpbound]

#print axioms trace_resolvent_le
#print axioms cubicPolynomial_centered
#print axioms integral_scalarMajorant
#print axioms integral_quadraticCoeff_le
#print axioms cubicLog_centered_le

end D5.S3.Quantum.Semigroups.WuCubicHessianResolvent
