import D5.S3.Quantum.Semigroups.WuCubicHotInnerResolvent
import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Resource.LogDet.PathSpectralClassical
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import OmegaBuild.Commands

/-! The signed fourth-order entropy remainder in the inner region of Wu v1,
Remark 3.15 (3.54). The estimate uses Loewner bounds and ordinary matrix
trace, then divides by the dimension to obtain normalized trace. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicHotInnerEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The scalar factor from the integrated fourth-order resolvent. -/
def entropyFactor (bMinus bPlus rho : ℝ) : ℝ :=
  bPlus^4 / bMinus * (3/4 + 3*rho/20 + rho^2/10)

private theorem kernel_le_polynomial {rho z : ℝ} (hr1 : rho < 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    3 * (1-z)^3 / (1-rho*z) ≤
      3 * (1-z)^3 + 3*rho*z*(1-z)^3 + 3*rho^2*z^2*(1-z)^2 := by
  have hz0 := hz.1.le
  have hz1 := hz.2
  have hden : 0 < 1-rho*z := by nlinarith [mul_le_mul_of_nonneg_right hr1.le hz0]
  have hden' : 1-z ≤ 1-rho*z := by nlinarith [mul_le_mul_of_nonneg_right hr1.le hz0]
  apply (div_le_iff₀ hden).2
  have h := mul_le_mul_of_nonneg_right hden' (show 0 ≤ 3*rho^2*z^2*(1-z)^2 by positivity)
  linarith only [show (3*(1-z)^3 + 3*rho*z*(1-z)^3 + 3*rho^2*z^2*(1-z)^2) *
    (1-rho*z) - 3*(1-z)^3 = (1-rho*z)*(3*rho^2*z^2*(1-z)^2) -
      (1-z)*(3*rho^2*z^2*(1-z)^2) by ring, h]

private theorem integral_majorant (rho : ℝ) :
    (∫ z in Ioo (0 : ℝ) 1,
        3 * (1-z)^3 + 3*rho*z*(1-z)^3 + 3*rho^2*z^2*(1-z)^2) =
      3/4 + 3*rho/20 + rho^2/10 := by
  rw [← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  let c₁ := -9 + 3*rho
  let c₂ := 9 - 9*rho + 3*rho^2
  let c₃ := -3 + 9*rho - 6*rho^2
  let c₄ := -3*rho + 3*rho^2
  have h (z : ℝ) : 3 * (1-z)^3 + 3*rho*z*(1-z)^3 + 3*rho^2*z^2*(1-z)^2 =
      3 + c₁*z^1 + c₂*z^2 + c₃*z^3 + c₄*z^4 := by dsimp [c₁,c₂,c₃,c₄]; ring
  simp_rw [h]
  have hi (c : ℝ) (k : ℕ) : IntervalIntegrable (fun z : ℝ => c*z^k) volume 0 1 :=
    (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => (3 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add (((hc.add (hi _ _)).add (hi _ _)).add (hi _ _)) (hi _ _),
    intervalIntegral.integral_add ((hc.add (hi _ _)).add (hi _ _)) (hi _ _),
    intervalIntegral.integral_add (hc.add (hi _ _)) (hi _ _),
    intervalIntegral.integral_add hc (hi _ _)]
  simp only [intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const]
  norm_num [c₁,c₂,c₃,c₄, smul_eq_mul]
  ring

/-- The transformed scalar kernel contributes at most the three stated coefficients. -/
theorem integral_kernel_le {rho : ℝ} (hr : 0 ≤ rho) (hr1 : rho < 1) :
    (∫ z in Ioo (0 : ℝ) 1, 3 * (1-z)^3 / (1-rho*z)) ≤
      3/4 + 3*rho/20 + rho^2/10 := by
  rw [← integral_majorant rho]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioo (fun z hz => kernel_le_polynomial hr1 hz)
  · apply ContinuousOn.integrableOn_Icc (a := 0) (b := 1) ?_ |>.mono_set Ioo_subset_Icc_self
    apply (by fun_prop : Continuous (fun z : ℝ => 3 * (1-z)^3)).continuousOn.div
      (by fun_prop)
    intro z hz
    exact (show 0 < 1-rho*z by
      nlinarith [mul_le_mul_of_nonneg_left hz.2 hr]).ne'
  · exact (by fun_prop : Continuous (fun z : ℝ =>
      3*(1-z)^3 + 3*rho*z*(1-z)^3 + 3*rho^2*z^2*(1-z)^2)).continuousOn.integrableOn_Icc.mono_set
        Ioo_subset_Icc_self

omit [DecidableEq n] in
private theorem reTrace_mul_nonneg {P Q : Matrix n n ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ (P * Q).trace.re := by
  classical
  exact RHLinalg.trace_mul_nonneg_of_posSemidef hP.posSemidef hQ.posSemidef

private theorem trace_sq_mono {X Y : Matrix n n ℂ} (hX : 0 ≤ X) (hXY : X ≤ Y) :
    (X^2).trace.re ≤ (Y^2).trace.re := by
  have hY := hX.trans hXY
  have hD : 0 ≤ Y-X := (sub_nonneg.mpr hXY)
  have h := add_nonneg (reTrace_mul_nonneg hD hY) (reTrace_mul_nonneg hX hD)
  simpa only [sub_mul, mul_sub, Matrix.trace_sub, Complex.sub_re, pow_two,
    sub_add_sub_cancel, sub_nonneg] using h

private theorem real_smul_trace_sq (r : ℝ) (X : Matrix n n ℂ) :
    ((r • X)^2).trace.re = r^2 * (X^2).trace.re := by
  rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_two, Matrix.trace_smul]
  rw [Complex.smul_re, pow_two X, smul_eq_mul]

/-- Fourth trace power under a Hermitian sandwich. Two applications of
trace-square monotonicity suffice, so the factors may fail to commute. -/
theorem trace_fourth_sandwich_le (T A : Matrix n n ℂ) (hT : IsSelfAdjoint T)
    (hA : IsSelfAdjoint A) {q : ℝ}
    (hbound : T ^ 2 ≤ q • (1 : Matrix n n ℂ)) :
    ((T*A*T)^4).trace.re ≤ q^4 * (A^4).trace.re := by
  have hT2 : 0 ≤ T^2 := by simpa [pow_two, hT.star_eq] using star_mul_self_nonneg T
  have hfirst : A*(T^2)*A ≤ q • A^2 := by
    simpa only [mul_smul_comm, smul_mul_assoc, mul_one, pow_two] using
      hA.conjugate_le_conjugate hbound
  have hsecond : T*(A*T^2*A)*T ≤ q • (T*A^2*T) := by
    simpa only [mul_smul_comm, smul_mul_assoc] using hT.conjugate_le_conjugate hfirst
  have ha := trace_sq_mono (hA.conjugate_nonneg hT2) hfirst
  have ht := trace_sq_mono (hT.conjugate_nonneg (hA.conjugate_nonneg hT2)) hsecond
  rw [real_smul_trace_sq] at ha ht
  have hcycle : ((T*A^2*T)^2).trace = ((A*T^2*A)^2).trace := by
    calc
      _ = (T * (A^2*T^2*A^2*T)).trace := congrArg trace (by noncomm_ring)
      _ = ((A^2*T^2*A^2*T)*T).trace := Matrix.trace_mul_comm _ _
      _ = (A*(A*T^2*A^2*T^2)).trace := congrArg trace (by noncomm_ring)
      _ = ((A*T^2*A^2*T^2)*A).trace := Matrix.trace_mul_comm _ _
      _ = _ := congrArg trace (by noncomm_ring)
  have hleft : (T*A*T)^4 = (T*(A*T^2*A)*T)^2 := by noncomm_ring
  rw [hleft]
  calc
    _ ≤ q^2 * ((T*A^2*T)^2).trace.re := ht
    _ ≤ q^2 * (q^2 * ((A^2)^2).trace.re) := by
      rw [hcycle]
      exact mul_le_mul_of_nonneg_left ha (sq_nonneg _)
    _ = _ := by rw [← pow_mul]; ring

omit [DecidableEq n] in
private theorem trace_mul_mono_right {P X Y : Matrix n n ℂ} (hP : 0 ≤ P) (h : X ≤ Y) :
    (P*X).trace.re ≤ (P*Y).trace.re := by
  simpa only [mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using
    reTrace_mul_nonneg hP (sub_nonneg.mpr h)

omit [DecidableEq n] in
private theorem trace_mul_mono_left {P Q X : Matrix n n ℂ} (hX : 0 ≤ X) (h : P ≤ Q) :
    (P*X).trace.re ≤ (Q*X).trace.re := by
  simpa only [sub_mul, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using
    reTrace_mul_nonneg (sub_nonneg.mpr h) hX

omit [DecidableEq n] in
private theorem trace_real_smul (r : ℝ) (X : Matrix n n ℂ) :
    (r • X).trace.re = r * X.trace.re := by
  rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

private theorem trace_fourth_nonneg (A : Matrix n n ℂ) (hA : IsSelfAdjoint A) :
    0 ≤ (A^4).trace.re := by
  have hn : 0 ≤ A^2 := by simpa [pow_two, hA.star_eq] using star_mul_self_nonneg A
  rw [show A^4 = A^2*A^2 by noncomm_ring]
  exact reTrace_mul_nonneg hn hn

private theorem trace_resolvent_le (P Z : Matrix n n ℂ) {p t : ℝ}
    (hZ : IsSelfAdjoint Z) (hP : 0 ≤ P) (hPupper : P ≤ p • (1 : Matrix n n ℂ))
    (hp : 0 ≤ p) (ht : t < 1) (hZlower : (-t) • (1 : Matrix n n ℂ) ≤ Z) :
    0 ≤ (P*(Z^4*(1+Z)⁻¹)).trace.re ∧
      (P*(Z^4*(1+Z)⁻¹)).trace.re ≤ p * (1-t)⁻¹ * (Z^4).trace.re := by
  have hspec : ∀ x ∈ spectrum ℝ Z, -t ≤ x := by
    apply (algebraMap_le_iff_le_spectrum (r := -t) hZ).mp
    rwa [Algebra.algebraMap_eq_smul_one]
  have hpos (x : ℝ) (hx : x ∈ spectrum ℝ Z) : 0 < 1+x := by linarith [hspec x hx]
  let f : ℝ → ℝ := fun x => x^4*(1+x)⁻¹
  let g : ℝ → ℝ := fun x => (1-t)⁻¹*x^4
  have hc (k : ℝ → ℝ) := Z.finite_real_spectrum.continuousOn k
  have hshift : cfc (fun x : ℝ => 1+x) Z = 1+Z := by
    rw [cfc_const_add 1 (fun x : ℝ => x) Z (hc _) hZ, cfc_id' ℝ Z hZ, map_one]
  have hf : cfc f Z = Z^4*(1+Z)⁻¹ := by
    change cfc (fun x : ℝ => x^4*(1+x)⁻¹) Z = _
    rw [cfc_mul (fun x : ℝ => x^4) (fun x : ℝ => (1+x)⁻¹) Z (hc _) (hc _),
      cfc_pow_id (R := ℝ) Z 4 hZ,
      cfc_inv (fun x : ℝ => 1+x) Z (fun x hx => (hpos x hx).ne') (hc _) hZ,
      hshift, ← Matrix.nonsing_inv_eq_ringInverse]
  have hnon : 0 ≤ cfc f Z := cfc_nonneg (fun x hx => mul_nonneg (by positivity)
    (inv_nonneg.mpr (hpos x hx).le))
  have hfg : cfc f Z ≤ cfc g Z := by
    apply (cfc_le_iff f g Z (hc _) (hc _) hZ).2
    intro x hx
    dsimp [f,g]
    rw [mul_comm (x^4)]
    exact mul_le_mul_of_nonneg_right
      (inv_anti₀ (sub_pos.mpr ht) (by linarith [hspec x hx])) (by positivity)
  have hg : cfc g Z = (1-t)⁻¹ • Z^4 := by
    exact (cfc_const_mul _ (fun x : ℝ => x^4) Z (hc _)).trans
      (congrArg ((1-t)⁻¹ • ·) (cfc_pow_id (R := ℝ) Z 4 hZ))
  rw [← hf]
  refine ⟨reTrace_mul_nonneg hP hnon, ?_⟩
  calc
    _ ≤ ((p • (1 : Matrix n n ℂ))*cfc f Z).trace.re := trace_mul_mono_left hnon hPupper
    _ ≤ ((p • (1 : Matrix n n ℂ))*cfc g Z).trace.re :=
      trace_mul_mono_right (smul_nonneg hp zero_le_one) hfg
    _ = _ := by rw [hg, smul_mul_assoc, one_mul, trace_real_smul, trace_real_smul, mul_assoc]

/-- Inverse square root of the shifted reference. -/
def shiftedRoot (B : Matrix n n ℂ) (l : ℝ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => Real.sqrt ((x+l)⁻¹)) B

/-- The positive sandwich factor with spectral multiplier sqrt (x/(x+l)). -/
def ratioRoot (B : Matrix n n ℂ) (l : ℝ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => Real.sqrt (x/(x+l))) B

/-- Ordinary real trace of the fourth resolvent term, with its factor of three. -/
def entropyKernel (B A : Matrix n n ℂ) (l : ℝ) : ℝ :=
  let T := ratioRoot B l
  let Z := T*A*T
  3*l^3 * (((B+l • 1)⁻¹)*(Z^4*(1+Z)⁻¹)).trace.re

private theorem ratioRoot_sq (B : Matrix n n ℂ) (hB : B.PosDef) (l : ℝ) (hl : 0 < l) :
    (ratioRoot B l)^2 = cfc (fun x : ℝ => x/(x+l)) B := by
  have hc (f : ℝ → ℝ) := B.finite_real_spectrum.continuousOn f
  rw [ratioRoot, pow_two, ← cfc_mul _ _ B (hc _) (hc _)]
  apply cfc_congr
  intro x hx
  rw [hB.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact Real.mul_self_sqrt (by have := hB.eigenvalues_pos i; positivity)

private theorem normalized_lower {T A : Matrix n n ℂ} (hT : IsSelfAdjoint T) {rho q : ℝ}
    (hr : 0 ≤ rho) (hTupper : T ^ 2 ≤ q • (1 : Matrix n n ℂ))
    (hAlo : (-rho) • (1 : Matrix n n ℂ) ≤ A) :
    (-(rho*q)) • (1 : Matrix n n ℂ) ≤ T*A*T := by
  calc
    _ ≤ (-rho) • T^2 := by
      simpa only [smul_smul, neg_mul] using smul_le_smul_of_nonpos_left hTupper (neg_nonpos.mpr hr)
    _ ≤ _ := by
      simpa only [mul_smul_comm, smul_mul_assoc, mul_one, pow_two] using
        hT.conjugate_le_conjugate hAlo

/-- The signed resolvent remainder is positive and admits the pointwise
fourth-trace majorant for any positive shift. -/
theorem entropyKernel_bounds (B A : Matrix n n ℂ) (hB : B.PosDef) (hA : IsSelfAdjoint A)
    {bMinus bPlus rho l : ℝ} (hb : 0 < bMinus) (hbb : bMinus ≤ bPlus)
    (hBlo : bMinus • (1 : Matrix n n ℂ) ≤ B)
    (hBhi : B ≤ bPlus • (1 : Matrix n n ℂ))
    (hr : 0 ≤ rho) (hr1 : rho < 1) (hAlo : (-rho) • (1 : Matrix n n ℂ) ≤ A)
    (hl : 0 < l) :
    let q := bPlus/(bPlus+l)
    0 ≤ entropyKernel B A l ∧
      entropyKernel B A l ≤
        3*l^3 * ((bMinus+l)⁻¹ * (1-rho*q)⁻¹ * (q^4 * (A^4).trace.re)) := by
  let q := bPlus/(bPlus+l)
  let T := ratioRoot B l
  let Z := T*A*T
  let P := (B+l • (1 : Matrix n n ℂ))⁻¹
  have hbp := hb.trans_le hbb
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hrt : rho*q < 1 := (mul_le_of_le_one_right hr hq1).trans_lt hr1
  have hBh := hB.isHermitian.isSelfAdjoint
  have hspecLo : ∀ x ∈ spectrum ℝ B, bMinus ≤ x := by
    apply (algebraMap_le_iff_le_spectrum (r := bMinus) hBh).mp
    rwa [Algebra.algebraMap_eq_smul_one]
  have hspecHi : ∀ x ∈ spectrum ℝ B, x ≤ bPlus := by
    apply (le_algebraMap_iff_spectrum_le (r := bPlus) hBh).mp
    rwa [Algebra.algebraMap_eq_smul_one]
  have hc (f : ℝ → ℝ) := B.finite_real_spectrum.continuousOn f
  have hT : IsSelfAdjoint T := cfc_predicate _ B
  have hZ : IsSelfAdjoint Z := by
    change star (T*A*T) = T*A*T
    simp only [star_mul, hT.star_eq, hA.star_eq, mul_assoc]
  have hTupper : T ^ 2 ≤ q • (1 : Matrix n n ℂ) := by
    change (ratioRoot B l)^2 ≤ _
    rw [ratioRoot_sq B hB l hl, ← Algebra.algebraMap_eq_smul_one]
    apply (cfc_le_algebraMap_iff _ _ B (hc _) hBh).2
    intro x hx
    have hxpos := hb.trans_le (hspecLo x hx)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right (hspecHi x hx) hl.le]
  have hZlower := normalized_lower hT hr hTupper hAlo
  have hBshift : (B+l • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.posSemidef_add hB.posSemidef (Matrix.PosDef.one.smul hl)
  have hP : 0 ≤ P := hBshift.inv.posSemidef.nonneg
  have hPupper : P ≤ (bMinus+l)⁻¹ • (1 : Matrix n n ℂ) := by
    change (B+l • (1 : Matrix n n ℂ))⁻¹ ≤ _
    rw [← D5.S3.Quantum.Divergence.ResolventFunctionalRigidity.cfc_shift_inverse
      B hB.posSemidef l hl, ← Algebra.algebraMap_eq_smul_one]
    exact (cfc_le_algebraMap_iff _ _ B (hc _) hBh).2
      (fun x hx => inv_anti₀ (by positivity) (add_le_add_left (hspecLo x hx) l))
  have h := trace_resolvent_le P Z hZ hP hPupper (by positivity) hrt hZlower
  have ht := trace_fourth_sandwich_le T A hT hA hTupper
  change 0 ≤ 3*l^3 * (P*(Z^4*(1+Z)⁻¹)).trace.re ∧
    3*l^3 * (P*(Z^4*(1+Z)⁻¹)).trace.re ≤ _
  refine ⟨mul_nonneg (by positivity) h.1, mul_le_mul_of_nonneg_left
    (h.2.trans (mul_le_mul_of_nonneg_left ht ?_)) (by positivity)⟩
  exact mul_nonneg (by positivity) (inv_nonneg.mpr (sub_nonneg.mpr hrt.le))

private theorem continuousOn_inverse {F : ℝ → Matrix n n ℂ} {s : Set ℝ}
    (hF : ContinuousOn F s) (hunit : ∀ x ∈ s, IsUnit (F x)) :
    ContinuousOn (fun x => (F x)⁻¹) s := by
  intro x hx
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det (F x)).mp (hunit x hx)
  have hdet : ContinuousAt Ring.inverse (F x).det := hu ▸ NormedRing.inverse_continuousAt u
  exact (continuousAt_matrix_inv (F x) hdet).comp_continuousWithinAt (hF x hx)

private theorem continuousOn_ratioRoot (B : Matrix n n ℂ) (hB : B.PosDef) :
    ContinuousOn (ratioRoot B) (Ioi (0 : ℝ)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let U : Matrix n n ℂ := hB.isHermitian.eigenvectorUnitary
  change Continuous (fun l : Ioi (0 : ℝ) => ratioRoot B l)
  have hf (i : n) : Continuous (fun l : Ioi (0 : ℝ) =>
      (Real.sqrt (hB.isHermitian.eigenvalues i / (hB.isHermitian.eigenvalues i + l)) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    apply Real.continuous_sqrt.comp
    refine continuous_const.div (continuous_const.add continuous_subtype_val) fun l => ?_
    exact (add_pos (hB.eigenvalues_pos i) l.property).ne'
  let D := fun l : Ioi (0 : ℝ) => Matrix.diagonal (fun i : n =>
    (Real.sqrt (hB.isHermitian.eigenvalues i / (hB.isHermitian.eigenvalues i + l)) : ℂ))
  have hd : Continuous D := by
    apply continuous_matrix
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [D] using hf i
    · simpa [D, Matrix.diagonal_apply_ne _ hij] using
        (continuous_const : Continuous (fun _ : Ioi (0 : ℝ) => (0 : ℂ)))
  have he (l : Ioi (0 : ℝ)) : ratioRoot B l = U * (D l * Uᴴ) := by
    rw [ratioRoot, hB.isHermitian.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    simp only [U, D, RCLike.ofReal_eq_complex_ofReal, star_eq_conjTranspose, mul_assoc]
    rfl
  simp_rw [he]
  exact continuous_const.mul (hd.mul continuous_const)

private theorem continuousOn_entropyKernel (B A : Matrix n n ℂ) (hB : B.PosDef)
    {rho : ℝ} (hr : 0 ≤ rho) (hr1 : rho < 1)
    (hAlo : (-rho) • (1 : Matrix n n ℂ) ≤ A) :
    ContinuousOn (entropyKernel B A) (Ioi (0 : ℝ)) := by
  let Z := fun l : ℝ => ratioRoot B l * A * ratioRoot B l
  have hT := continuousOn_ratioRoot B hB
  have hZ : ContinuousOn Z (Ioi (0 : ℝ)) := (hT.mul continuousOn_const).mul hT
  have hP : ContinuousOn (fun l : ℝ => (B+l • (1 : Matrix n n ℂ))⁻¹) (Ioi 0) := by
    apply continuousOn_inverse (by fun_prop)
    intro l hl
    exact (Matrix.PosDef.posSemidef_add hB.posSemidef (Matrix.PosDef.one.smul hl)).isUnit
  have hJ : ContinuousOn (fun l => (1+Z l)⁻¹) (Ioi 0) := by
    apply continuousOn_inverse (continuousOn_const.add hZ)
    intro l hl
    have hc (f : ℝ → ℝ) := B.finite_real_spectrum.continuousOn f
    have ht : (ratioRoot B l)^2 ≤ (1 : Matrix n n ℂ) := by
      rw [ratioRoot_sq B hB l hl]
      apply (cfc_le_one_iff _ B (hc _) hB.isHermitian.isSelfAdjoint).2
      intro x hx
      rw [hB.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      have hi := hB.eigenvalues_pos i
      apply (div_le_one (by exact add_pos hi hl)).2
      linarith [show 0 < l from hl]
    have hTadj : IsSelfAdjoint (ratioRoot B l) := cfc_predicate _ B
    have hZlow : (-rho) • (1 : Matrix n n ℂ) ≤ Z l := by
      simpa only [one_smul, mul_one, Z] using
        normalized_lower hTadj hr (q := 1) (by simpa only [one_smul] using ht) hAlo
    have hpos : (Z l - (-rho) • (1 : Matrix n n ℂ)).PosSemidef :=
      (sub_nonneg.mpr hZlow).posSemidef
    have he : Z l - (-rho) • (1 : Matrix n n ℂ) + (1-rho) • 1 = 1+Z l := by
      rw [sub_smul, one_smul, neg_smul]
      abel
    change IsUnit (1+Z l)
    rw [← he]
    exact (Matrix.PosDef.posSemidef_add hpos (Matrix.PosDef.one.smul (sub_pos.mpr hr1))).isUnit
  have hM := hP.mul ((hZ.pow 4).mul hJ)
  have hre : ContinuousOn (fun l => (Matrix.trace
      ((B+l • (1 : Matrix n n ℂ))⁻¹ * ((Z l)^4 * (1+Z l)⁻¹))).re) (Ioi 0) := by
    apply Complex.continuous_re.comp_continuousOn
    rw [continuousOn_iff_continuous_domRestrict] at hM ⊢
    exact continuous_finsetSum _ fun i _ => hM.matrix_elem i i
  exact (by fun_prop : ContinuousOn (fun l : ℝ => 3*l^3) (Ioi 0)).mul hre

private def positiveShift (b z : ℝ) : ℝ := b/z-b

private theorem positiveShift_image {b : ℝ} (hb : 0 < b) :
    positiveShift b '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext l
  constructor
  · rintro ⟨z, hz, rfl⟩
    change 0 < b/z-b
    apply sub_pos.mpr
    exact (lt_div_iff₀ hz.1).2 (by nlinarith [mul_lt_mul_of_pos_left hz.2 hb])
  · intro hl
    have hp : 0 < b+l := add_pos hb hl
    refine ⟨b/(b+l), ⟨by positivity, (div_lt_one hp).2 (by linarith [show 0 < l from hl])⟩, ?_⟩
    dsimp [positiveShift]
    field_simp [hb.ne', hp.ne']
    ring

private theorem positiveShift_inj {b : ℝ} (hb : 0 < b) :
    InjOn (positiveShift b) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have he : b/x = b/y := by dsimp [positiveShift] at hxy; linarith
  have h := (div_eq_div_iff hx.1.ne' hy.1.ne').mp he
  exact (mul_left_cancel₀ hb.ne' h).symm

private theorem positiveShift_deriv (b : ℝ) (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivWithinAt (positiveShift b) (-(b/z^2)) (Ioo 0 1) z := by
  have h := (((hasDerivAt_id z).inv hz.1.ne').const_mul b).sub_const b
  convert h.hasDerivWithinAt using 1
  · ext x
    simp [positiveShift, div_eq_mul_inv]
  · simp [div_eq_mul_inv]

private theorem integral_positiveShift {b : ℝ} (hb : 0 < b) (f : ℝ → ℝ) :
    (∫ l in Ioi (0 : ℝ), f l) = ∫ z in Ioo (0 : ℝ) 1, b/z^2 * f (positiveShift b z) := by
  rw [← positiveShift_image hb, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (positiveShift_deriv b) (positiveShift_inj hb)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro z _
  dsimp only
  rw [abs_neg, abs_of_nonneg (by positivity), smul_eq_mul]

private theorem integrableOn_positiveShift {b : ℝ} (hb : 0 < b) (f : ℝ → ℝ) :
    IntegrableOn f (Ioi 0) ↔
      IntegrableOn (fun z => b/z^2 * f (positiveShift b z)) (Ioo 0 1) := by
  rw [← positiveShift_image hb, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo (positiveShift_deriv b) (positiveShift_inj hb)]
  simp only [abs_neg, abs_div, abs_of_pos hb, abs_sq, smul_eq_mul]

/-- The actual integral of the fourth-order matrix resolvent, using ordinary trace. -/
theorem integrated_entropyKernel_le (B A : Matrix n n ℂ) (hB : B.PosDef) (hA : IsSelfAdjoint A)
    {bMinus bPlus rho : ℝ} (hb : 0 < bMinus) (hbb : bMinus ≤ bPlus)
    (hBlo : bMinus • (1 : Matrix n n ℂ) ≤ B)
    (hBhi : B ≤ bPlus • (1 : Matrix n n ℂ))
    (hr : 0 ≤ rho) (hr1 : rho < 1) (hAlo : (-rho) • (1 : Matrix n n ℂ) ≤ A) :
    IntegrableOn (entropyKernel B A) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), entropyKernel B A l) ≤
        entropyFactor bMinus bPlus rho * (A^4).trace.re := by
  let K := fun z : ℝ => 3 * (1-z)^3 / (1-rho*z)
  let c := bPlus^4/bMinus * (A^4).trace.re
  let f := fun z : ℝ => bPlus/z^2 * entropyKernel B A (positiveShift bPlus z)
  have hbp := hb.trans_le hbb
  have hc : 0 ≤ c := mul_nonneg (by positivity) (trace_fourth_nonneg A hA)
  have hpoint (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) : 0 ≤ f z ∧ f z ≤ c*K z := by
    let l := positiveShift bPlus z
    have hl : 0 < l := by
      have hm : l ∈ positiveShift bPlus '' Ioo (0 : ℝ) 1 := ⟨z, hz, rfl⟩
      rwa [positiveShift_image hbp] at hm
    have hx : bPlus/(bPlus+l) = z := by
      dsimp [l, positiveShift]
      field_simp [hbp.ne', hz.1.ne']
      ring
    have hden : 0 < 1-rho*z := by
      have := mul_le_of_le_one_right hr hz.2.le
      linarith
    have hratio : (bMinus+l)⁻¹ ≤ (bPlus/bMinus)*(bPlus+l)⁻¹ := by
      rw [← div_eq_mul_inv, inv_eq_one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hb).2
      nlinarith [mul_le_mul_of_nonneg_right hbb hl.le]
    obtain ⟨hn, hle⟩ := entropyKernel_bounds B A hB hA hb hbb hBlo hBhi hr hr1 hAlo hl
    rw [hx] at hle
    have hm := mul_le_mul_of_nonneg_right hratio
      (show 0 ≤ (1-rho*z)⁻¹ * (z^4 * (A^4).trace.re) from
        mul_nonneg (by positivity) (mul_nonneg (by positivity) (trace_fourth_nonneg A hA)))
    have hm' : (bMinus+l)⁻¹ * (1-rho*z)⁻¹ * (z^4 * (A^4).trace.re) ≤
        bPlus/bMinus*(bPlus+l)⁻¹ * (1-rho*z)⁻¹ * (z^4 * (A^4).trace.re) := by
      simpa only [mul_assoc] using hm
    refine ⟨mul_nonneg (by positivity) hn, ?_⟩
    calc
      f z ≤ bPlus/z^2 * (3*l^3 *
          (bPlus/bMinus*(bPlus+l)⁻¹ * (1-rho*z)⁻¹ * (z^4 * (A^4).trace.re))) :=
        mul_le_mul_of_nonneg_left (hle.trans (mul_le_mul_of_nonneg_left hm' (by positivity)))
          (by positivity)
      _ = c*K z := by
        dsimp [c, K, l, positiveShift]
        field_simp [hbp.ne', hb.ne', hz.1.ne', hden.ne']
        ring
  have hK : IntegrableOn K (Ioo 0 1) := by
    apply ContinuousOn.integrableOn_Icc (a := 0) (b := 1) ?_ |>.mono_set Ioo_subset_Icc_self
    apply (by fun_prop : Continuous (fun z : ℝ => 3 * (1-z)^3)).continuousOn.div
      (by fun_prop)
    intro z hz
    exact (show 0 < 1-rho*z by
      nlinarith [mul_le_mul_of_nonneg_left hz.2 hr]).ne'
  have hcK : IntegrableOn (fun z => c*K z) (Ioo 0 1) := hK.const_mul c
  have hshift : ContinuousOn (positiveShift bPlus) (Ioo 0 1) :=
    (continuousOn_const.div continuousOn_id (fun _ hz => hz.1.ne')).sub continuousOn_const
  have hmap : MapsTo (positiveShift bPlus) (Ioo 0 1) (Ioi 0) := by
    intro z hz
    rw [← positiveShift_image hbp]
    exact mem_image_of_mem _ hz
  have hfcont : ContinuousOn f (Ioo 0 1) :=
    (continuousOn_const.div (continuousOn_id.pow 2) (fun _ hz => pow_ne_zero _ hz.1.ne')).mul
      ((continuousOn_entropyKernel B A hB hr hr1 hAlo).comp hshift hmap)
  have hf : IntegrableOn f (Ioo 0 1) := by
    apply hcK.mono' (hfcont.aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioo (0 : ℝ) 1) measurableSet_Ioo] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hpoint z hz).1]
    exact (hpoint z hz).2
  refine ⟨(integrableOn_positiveShift hbp _).2 hf, ?_⟩
  rw [integral_positiveShift hbp]
  calc
    _ ≤ ∫ z in Ioo (0 : ℝ) 1, c*K z :=
      setIntegral_mono_on hf hcK measurableSet_Ioo (fun z hz => (hpoint z hz).2)
    _ = c * (∫ z in Ioo (0 : ℝ) 1, K z) := integral_const_mul _ _
    _ ≤ c * (3/4 + 3*rho/20 + rho^2/10) :=
      mul_le_mul_of_nonneg_left (integral_kernel_le hr hr1) hc
    _ = _ := by dsimp [c, entropyFactor]; ring

private theorem scalar_log_resolvent {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun l : ℝ => (1+l)⁻¹-(x+l)⁻¹) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), (1+l)⁻¹-(x+l)⁻¹) = Real.log x := by
  let f := fun z : ℝ => (x-1)/(1+(x-1)*z)
  have hden (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : 0 < 1+(x-1)*z := by
    by_cases h : z = 1
    · rw [h]; linarith
    · have ha : 0 < 1-z := sub_pos.mpr (lt_of_le_of_ne hz.2 h)
      have hb := mul_nonneg hx.le hz.1
      nlinarith
  have he (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
      1/z^2 * ((1+positiveShift 1 z)⁻¹-(x+positiveShift 1 z)⁻¹) = f z := by
    have h := (hden z (Ioo_subset_Icc_self hz)).ne'
    have h' : 1-z+z*x ≠ 0 := by
      convert h using 1
      ring
    dsimp [f, positiveShift]
    field_simp [hz.1.ne', h]
    ring_nf
    field_simp [h']
    ring
  have hc : ContinuousOn f (Icc 0 1) :=
    continuousOn_const.div (by fun_prop) fun z hz => (hden z hz).ne'
  refine ⟨(integrableOn_positiveShift one_pos _).2
    (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self |>.congr_fun
      (fun z hz => (he z hz).symm) measurableSet_Ioo), ?_⟩
  rw [integral_positiveShift one_pos, setIntegral_congr_fun measurableSet_Ioo he,
    ← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  have hd (z : ℝ) (hz : z ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t => Real.log (1+(x-1)*t)) (f z) z := by
    rw [uIcc_of_le zero_le_one] at hz
    have h := (Real.hasDerivAt_log (hden z hz).ne').comp z
      (((hasDerivAt_id z).const_mul (x-1)).const_add 1)
    simpa [f, div_eq_mul_inv, mul_comm, Function.comp_def] using h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc zero_le_one)]
  simp

/-- The positive-shift representation of the real trace of the matrix cubic logarithm. -/
theorem integral_cubicLogIntegrand (Y : Matrix n n ℂ) (hY : Y.PosDef) :
    IntegrableOn (fun l => (WuCubicHotInnerResolvent.cubicLogIntegrand l Y).trace.re) (Ioi 0) ∧
    (∫ l in Ioi (0 : ℝ), (WuCubicHotInnerResolvent.cubicLogIntegrand l Y).trace.re) =
      (Y^3*cfc Real.log Y).trace.re := by
  let e := hY.isHermitian.eigenvalues
  let f := fun i (l : ℝ) => (e i)^3 * ((1+l)⁻¹-(e i+l)⁻¹)
  have he (l : ℝ) : (WuCubicHotInnerResolvent.cubicLogIntegrand l Y).trace.re = ∑ i, f i l := by
    exact D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum Y hY.isHermitian _
  have hi (i : n) : IntegrableOn (f i) (Ioi 0) :=
    (scalar_log_resolvent (hY.eigenvalues_pos i)).1.const_mul _
  have hc (g : ℝ → ℝ) := Y.finite_real_spectrum.continuousOn g
  simp_rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i),
    ← cfc_pow_id (R := ℝ) Y 3 hY.isHermitian.isSelfAdjoint,
    ← cfc_mul _ _ Y (hc _) (hc _),
    D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum Y hY.isHermitian]
  apply Finset.sum_congr rfl
  intro i _
  rw [show f i = (fun l => (e i)^3 * ((1+l)⁻¹-(e i+l)⁻¹)) from rfl,
    integral_const_mul, (scalar_log_resolvent (hY.eigenvalues_pos i)).2]

/-- Degree-three polynomial part of the shifted cubic logarithm integrand. -/
def cubicPolynomial (B U : Matrix n n ℂ) (l : ℝ) : Matrix n n ℂ :=
  let Y := B+U
  let W := shiftedRoot B l
  let Z := W*U*W
  (1+l)⁻¹ • Y^3 - Y^2 + l • Y - l^2 • 1 +
    l^3 • (W*(1-Z+Z^2-Z^3)*W)

private theorem ratioRoot_eq_mul (B : Matrix n n ℂ) (hB : B.PosDef) (l : ℝ) :
    ratioRoot B l = shiftedRoot B l * CFC.sqrt B ∧
      ratioRoot B l = CFC.sqrt B * shiftedRoot B l := by
  have hc (g : ℝ → ℝ) := B.finite_real_spectrum.continuousOn g
  have hs : CFC.sqrt B = cfc Real.sqrt B := by
    rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt B hB.posSemidef.nonneg]
    apply cfc_congr
    intro x _
    simp only [Real.sqrt]
  have he : ratioRoot B l = shiftedRoot B l * CFC.sqrt B := by
    rw [hs, shiftedRoot, ← cfc_mul _ _ B (hc _) (hc _), ratioRoot]
    apply cfc_congr
    intro x hx
    rw [hB.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    dsimp only
    rw [div_eq_mul_inv, mul_comm (hB.isHermitian.eigenvalues i),
      Real.sqrt_mul' _ (hB.eigenvalues_pos i).le]
  refine ⟨he, ?_⟩
  rw [he, hs, shiftedRoot, ← cfc_mul _ _ B (hc _) (hc _),
    ← cfc_mul _ _ B (hc _) (hc _)]
  exact cfc_congr (fun _ _ => mul_comm _ _)

private theorem displaced_posDef (B A : Matrix n n ℂ) (hB : B.PosDef) {rho : ℝ}
    (hr1 : rho < 1) (hAlo : (-rho) • (1 : Matrix n n ℂ) ≤ A) :
    (B+CFC.sqrt B*A*CFC.sqrt B).PosDef := by
  let S := CFC.sqrt B
  have hA : (A-(-rho) • (1 : Matrix n n ℂ)).PosSemidef :=
    (sub_nonneg.mpr hAlo).posSemidef
  have he : A-(-rho) • (1 : Matrix n n ℂ) + (1-rho) • 1 = 1+A := by
    rw [sub_smul, one_smul, neg_smul]
    abel
  have hJ : (1+A).PosDef :=
    he ▸ Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul (sub_pos.mpr hr1))
  have hS := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)
  have hunit : IsUnit S := (CFC.isUnit_sqrt_iff B hB.posSemidef.nonneg).2 hB.isUnit
  have hsquare : S*S = B := by
    rw [← pow_two]
    exact CFC.sq_sqrt B hB.posSemidef.nonneg
  have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := 1+A) hunit).2 hJ
  rwa [hS.star_eq, mul_add, add_mul, mul_one, hsquare] at h

private theorem entropyKernel_eq_sub (B A : Matrix n n ℂ) (hB : B.PosDef) {rho l : ℝ}
    (hr1 : rho < 1) (hAlo : (-rho) • (1 : Matrix n n ℂ) ≤ A) (hl : 0 < l) :
    let U := CFC.sqrt B*A*CFC.sqrt B
    3 * ((WuCubicHotInnerResolvent.cubicLogIntegrand l (B+U)).trace.re -
      (cubicPolynomial B U l).trace.re) = entropyKernel B A l := by
  let U := CFC.sqrt B*A*CFC.sqrt B
  let W := shiftedRoot B l
  have hnorm : W * (B+l • 1) * W = 1 :=
    WuCubicHotInnerResolvent.shift_inverse_sqrt_congruence B hB.posSemidef l hl
  have h := WuCubicHotInnerResolvent.cubic_log_integrand_trace_fourth B U W l hl
    (displaced_posDef B A hB hr1 hAlo).posSemidef hnorm
  change _ - (cubicPolynomial B U l).trace =
    l^3 • (((B+l • 1)⁻¹)*((W*U*W)^4 * (1+W*U*W)⁻¹)).trace at h
  have he : W*U*W = ratioRoot B l*A*ratioRoot B l := by
    obtain ⟨h₁, h₂⟩ := ratioRoot_eq_mul B hB l
    calc
      W * U * W =
          (shiftedRoot B l * CFC.sqrt B) * A * (CFC.sqrt B * shiftedRoot B l) := by
            dsimp [U, W]; noncomm_ring
      _ = _ := congrArg₂ (fun X Y : Matrix n n ℂ => X*A*Y) h₁.symm h₂.symm
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul, he] at hre
  change 3 * _ = _
  rw [hre]
  simp only [entropyKernel, mul_assoc]

/-- Normalized trace of the cubic-log entropy after subtracting the integrated
degree-three part at the positive definite reference. The other terms of the
inner entropy polynomial have degree at most three already. -/
def entropyRemainder (B A : Matrix n n ℂ) : ℝ :=
  let U := CFC.sqrt B*A*CFC.sqrt B
  let Y := B+U
  3 * ((Y^3*cfc Real.log Y).trace.re -
    (∫ l in Ioi (0 : ℝ), (cubicPolynomial B U l).trace.re)) / Fintype.card n

/-- The integrated entropy remainder bound with the normalized fourth trace.
The argument needs only the lower Loewner bound on the perturbation. -/
theorem entropyRemainder_le (B A : Matrix n n ℂ) (hB : B.PosDef) (hA : IsSelfAdjoint A)
    {bMinus bPlus rho : ℝ} (hb : 0 < bMinus) (hbb : bMinus ≤ bPlus)
    (hBlo : bMinus • (1 : Matrix n n ℂ) ≤ B)
    (hBhi : B ≤ bPlus • (1 : Matrix n n ℂ))
    (hr : 0 ≤ rho) (hr1 : rho < 1) (hAlo : (-rho) • (1 : Matrix n n ℂ) ≤ A) :
    entropyRemainder B A ≤ entropyFactor bMinus bPlus rho *
      ((A^4).trace.re / Fintype.card n) := by
  let U := CFC.sqrt B*A*CFC.sqrt B
  let Y := B+U
  let f := fun l => (WuCubicHotInnerResolvent.cubicLogIntegrand l Y).trace.re
  let g := fun l => (cubicPolynomial B U l).trace.re
  obtain ⟨hf, hfval⟩ := integral_cubicLogIntegrand Y (displaced_posDef B A hB hr1 hAlo)
  obtain ⟨hK, hKle⟩ := integrated_entropyKernel_le B A hB hA hb hbb hBlo hBhi hr hr1 hAlo
  have he (l : ℝ) (hl : l ∈ Ioi (0 : ℝ)) : 3*(f l-g l) = entropyKernel B A l :=
    entropyKernel_eq_sub B A hB hr1 hAlo hl
  have hg : IntegrableOn g (Ioi 0) := by
    refine (hf.sub (hK.const_mul (1/3 : ℝ))).congr_fun ?_ measurableSet_Ioi
    intro l hl
    change f l - (1/3)*entropyKernel B A l = g l
    rw [← he l hl]
    ring
  have hvalue : 3*((Y^3*cfc Real.log Y).trace.re - ∫ l in Ioi (0 : ℝ), g l) =
      ∫ l in Ioi (0 : ℝ), entropyKernel B A l := by
    rw [← setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul, integral_sub hf hg, hfval]
  change (3*((Y^3*cfc Real.log Y).trace.re - ∫ l in Ioi (0 : ℝ), g l)) / _ ≤ _
  rw [hvalue, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hKle (Nat.cast_nonneg _)

#print axioms entropyRemainder_le
#print axioms integral_cubicLogIntegrand
#print axioms integrated_entropyKernel_le
#print axioms entropyKernel_bounds
#print axioms integral_kernel_le
#print axioms trace_fourth_sandwich_le

end D5.S3.Quantum.Semigroups.WuCubicHotInnerEntropy
