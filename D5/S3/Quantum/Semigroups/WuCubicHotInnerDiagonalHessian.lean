import D5.S3.Quantum.Semigroups.WuCubicHotInnerEntropy
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity

/-! The pointwise quadratic coefficient of the shifted cubic polynomial in a diagonal basis. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicHotInnerDiagonalHessian

open WuCubicHotInnerEntropy (cubicPolynomial shiftedRoot)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric scalar kernel for the second variation at shift `l`. -/
def shiftHessian (l x y : ℝ) : ℝ :=
  3 * (x + y) / (1 + l) - 2 +
    l ^ 3 * (((x + l)⁻¹) ^ 2 * (y + l)⁻¹ + ((y + l)⁻¹) ^ 2 * (x + l)⁻¹)

omit [DecidableEq n] in
private theorem trace_real_smul (r : ℝ) (M : Matrix n n ℂ) :
    (r • M).trace.re = r * M.trace.re := by
  rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

private theorem trace_diagonal_three {U : Matrix n n ℂ} (hU : U.IsHermitian)
    (a b c : n → ℝ) :
    (diagonal (fun i => (a i : ℂ)) * U * diagonal (fun i => (b i : ℂ)) * U *
      diagonal (fun i => (c i : ℂ))).trace.re =
      ∑ i, ∑ j, a i * b j * c i * Complex.normSq (U i j) := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul, Complex.re_sum]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← hU.apply j i, Complex.star_def]
  rw [show (a i : ℂ) * U i j * (b j : ℂ) * starRingEnd ℂ (U i j) * (c i : ℂ) =
    ((a i : ℂ) * (b j : ℂ) * (c i : ℂ)) * (U i j * starRingEnd ℂ (U i j)) by ring]
  simp only [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The real trace has an exact cubic expansion along a Hermitian direction, with quadratic
coefficient given by the symmetric kernel on pairs of diagonal entries. -/
theorem cubicPolynomial_trace_expansion (x : n → ℝ) (hx : ∀ i, 0 < x i)
    (U : Matrix n n ℂ) (hU : U.IsHermitian) (l : ℝ) (hl : 0 < l) :
    let B := diagonal (fun i => (x i : ℂ))
    ∃ a c : ℝ, ∀ t : ℝ,
      (cubicPolynomial B (t • U) l).trace.re = (cubicPolynomial B 0 l).trace.re +
        t * a + t ^ 2 * ((1 / 2 : ℝ) *
          ∑ i, ∑ j, shiftHessian l (x i) (x j) * Complex.normSq (U i j)) + t ^ 3 * c := by
  let B := diagonal (fun i => (x i : ℂ))
  let W := shiftedRoot B l
  let R := W ^ 2
  let L := (1 + l)⁻¹ • (B ^ 2 * U + B * U * B + U * B ^ 2) - (B * U + U * B) +
    l • U - l ^ 3 • (R * U * R)
  let Q := (1 + l)⁻¹ • (B * U ^ 2 + U * B * U + U ^ 2 * B) - U ^ 2 +
    l ^ 3 • (R * U * R * U * R)
  let C := (1 + l)⁻¹ • U ^ 3 - l ^ 3 • (R * U * R * U * R * U * R)
  have hpoly (t : ℝ) : cubicPolynomial B (t • U) l =
      cubicPolynomial B 0 l + t • L + t ^ 2 • Q + t ^ 3 • C := by
    simp only [cubicPolynomial, L, Q, C, R, W, pow_succ, pow_zero, one_mul, mul_one,
      add_zero, sub_zero, zero_mul, mul_zero, add_mul, mul_add, sub_mul, mul_sub,
      mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul, mul_assoc]
    module
  let r : n → ℝ := fun i => (x i + l)⁻¹
  have hW : W = diagonal (fun i => (Real.sqrt (r i) : ℂ)) := by
    simpa only [W, shiftedRoot, B, r, Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
      using Matrix.cfc_diagonal_real (𝕜 := ℂ) x (fun z : ℝ => Real.sqrt ((z + l)⁻¹))
  have hR : R = diagonal (fun i => (r i : ℂ)) := by
    rw [show R = W ^ 2 from rfl, hW, pow_two, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul, ← pow_two,
      Real.sq_sqrt (inv_nonneg.mpr (add_pos (hx i) hl).le : 0 ≤ r i)]
  let N : n → n → ℝ := fun i j => Complex.normSq (U i j)
  have hBU : (B * U ^ 2).trace.re = ∑ i, ∑ j, x i * N i j := by
    simpa only [B, N, pow_two, Complex.ofReal_one, Matrix.diagonal_one, mul_one, mul_assoc]
      using trace_diagonal_three hU x (fun _ => 1) (fun _ => 1)
  have hUBU : (U * B * U).trace = (B * U ^ 2).trace := by
    rw [mul_assoc U B U, Matrix.trace_mul_comm U (B * U), mul_assoc B U U, ← pow_two]
  have hUUB : (U ^ 2 * B).trace = (B * U ^ 2).trace := Matrix.trace_mul_comm _ _
  have hUU : (U ^ 2).trace.re = ∑ i, ∑ j, N i j := by
    simpa only [N, pow_two, Complex.ofReal_one, Matrix.diagonal_one, one_mul, mul_one]
      using trace_diagonal_three hU (fun _ => 1) (fun _ => 1) (fun _ => 1)
  have hRR := trace_diagonal_three hU r r r
  let w : n → n → ℝ := fun i j => 3 * x i / (1 + l) - 1 + l ^ 3 * (r i ^ 2 * r j)
  have hQ : Q.trace.re = ∑ i, ∑ j, w i j * N i j := by
    dsimp only [Q]
    rw [hR]
    simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re,
      trace_real_smul, hUBU, hUUB, hBU, hUU, hRR]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [w, N, div_eq_mul_inv]
    ring
  have hN (i j : n) : N i j = N j i := by
    change Complex.normSq (U i j) = Complex.normSq (U j i)
    rw [← hU.apply i j, Complex.star_def, Complex.normSq_conj]
  have hswap : (∑ i, ∑ j, w j i * N i j) = ∑ i, ∑ j, w i j * N i j := by
    calc
      _ = ∑ i, ∑ j, w j i * N j i := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hN i j]
      _ = _ := Finset.sum_comm
  have hsum : (∑ i, ∑ j, shiftHessian l (x i) (x j) * N i j) =
      (∑ i, ∑ j, w i j * N i j) + ∑ i, ∑ j, w j i * N i j := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [shiftHessian, w, r, div_eq_mul_inv]
    ring
  have hsym : (∑ i, ∑ j, w i j * N i j) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, shiftHessian l (x i) (x j) * N i j := by
    rw [hsum, hswap]
    ring
  refine ⟨L.trace.re, C.trace.re, fun t => ?_⟩
  rw [hpoly t]
  simp only [Matrix.trace_add, Complex.add_re, trace_real_smul]
  rw [hQ, hsym]

#print axioms cubicPolynomial_trace_expansion

open private scalar_log_resolvent from D5.S3.Quantum.Semigroups.WuCubicHotInnerEntropy

/-- The first scalar derivative of the shifted cubic logarithm integrand. -/
def scalarFirst (l x : ℝ) : ℝ :=
  3 * x^2 * ((1+l)⁻¹ - (x+l)⁻¹) + x^3 * ((x+l)^2)⁻¹

/-- The second scalar derivative of the shifted cubic logarithm integrand. -/
def scalarSecond (l x : ℝ) : ℝ :=
  6 * x * ((1+l)⁻¹ - (x+l)⁻¹) + 6 * x^2 * ((x+l)^2)⁻¹ -
    2 * x^3 * ((x+l)^3)⁻¹

/-- Derivative in the positive scalar argument, with the shift fixed. -/
theorem hasDerivAt_scalarCubic {l x : ℝ} (hx : 0 < x) (hl : 0 < l) :
    HasDerivAt (fun z : ℝ => z^3 * ((1+l)⁻¹ - (z+l)⁻¹)) (scalarFirst l x) x := by
  have hinv := ((hasDerivAt_id x).add_const l).inv (add_pos hx hl).ne'
  convert ((hasDerivAt_id x).pow 3).mul (hinv.const_sub ((1+l)⁻¹)) using 1
  · rfl
  · simp [scalarFirst, id_eq, div_eq_mul_inv]

/-- The derivative of the first derivative at a positive scalar argument. -/
theorem hasDerivAt_scalarFirst {l x : ℝ} (hx : 0 < x) (hl : 0 < l) :
    HasDerivAt (scalarFirst l) (scalarSecond l x) x := by
  have hinv := ((hasDerivAt_id x).add_const l).inv (add_pos hx hl).ne'
  have h :=
    ((((hasDerivAt_id x).pow 2).const_mul 3).mul (hinv.const_sub ((1+l)⁻¹))).add
      (((hasDerivAt_id x).pow 3).mul (hinv.pow 2))
  convert h using 1
  · funext z
    simp [scalarFirst, inv_pow]
  · simp [scalarSecond, id_eq, div_eq_mul_inv, ← inv_pow]
    ring

/-- The shift kernel is the divided difference of the first derivative. -/
theorem shiftHessian_eq_dividedDifference {l x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hl : 0 < l) (hxy : x ≠ y) :
    shiftHessian l x y = (scalarFirst l x - scalarFirst l y) / (x-y) := by
  apply (eq_div_iff (sub_ne_zero.mpr hxy)).2
  unfold shiftHessian scalarFirst
  field_simp [(show 0 < 1+l by positivity).ne', (add_pos hx hl).ne',
    (add_pos hy hl).ne']
  ring

/-- At a coincident level the shift kernel is the second derivative. -/
theorem shiftHessian_self {l x : ℝ} (hx : 0 < x) (hl : 0 < l) :
    shiftHessian l x x = scalarSecond l x := by
  unfold shiftHessian scalarSecond
  field_simp [(show 0 < 1+l by positivity).ne', (add_pos hx hl).ne']
  ring

private theorem integral_shift_rpow {x a : ℝ} (hx : 0 < x) (ha : a < -1) :
    (∫ l in Ioi (0 : ℝ), (x+l)^a) = -x^(a+1)/(a+1) := by
  have hpre : (fun l : ℝ => l+x) ⁻¹' Ioi x = Ioi 0 := by
    ext l
    simp
  rw [← integral_Ioi_rpow_of_lt ha hx]
  have h :=
    (measurePreserving_add_right (volume : Measure ℝ) x).setIntegral_preimage_emb
      (Homeomorph.addRight x).isClosedEmbedding.measurableEmbedding (fun l => l^a) (Ioi x)
  rw [hpre] at h
  simpa only [add_comm] using h

private theorem integral_shift_inv_sq {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun l : ℝ => ((x+l)^2)⁻¹) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), ((x+l)^2)⁻¹) = x⁻¹ := by
  constructor
  · simpa only [Real.rpow_neg_ofNat, _root_.zpow_neg, zpow_ofNat, add_comm] using
      integrableOn_add_rpow_Ioi_of_lt (a := -2) (by norm_num) (neg_lt_zero.mpr hx)
  · have h := integral_shift_rpow hx (a := -2) (by norm_num)
    rw [show (-2 : ℝ) + 1 = -1 by norm_num] at h
    simpa [_root_.zpow_neg, Real.rpow_neg_one] using h

private theorem integral_shift_inv_cube {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun l : ℝ => ((x+l)^3)⁻¹) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), ((x+l)^3)⁻¹) = (2*x^2)⁻¹ := by
  constructor
  · simpa only [Real.rpow_neg_ofNat, _root_.zpow_neg, zpow_ofNat, add_comm] using
      integrableOn_add_rpow_Ioi_of_lt (a := -3) (by norm_num) (neg_lt_zero.mpr hx)
  · convert integral_shift_rpow hx (a := -3) (by norm_num) using 1
    · simp [_root_.zpow_neg]
    · rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg_ofNat, _root_.zpow_neg, zpow_ofNat]
      field_simp [hx.ne']

/-- Integrating the first scalar derivative recovers the derivative of x³ log x. -/
theorem integral_scalarFirst {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun l => scalarFirst l x) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), scalarFirst l x) = 3*x^2*Real.log x+x^2 := by
  obtain ⟨hlog, hlogval⟩ := scalar_log_resolvent hx
  obtain ⟨hsq, hsqval⟩ := integral_shift_inv_sq hx
  refine ⟨(hlog.const_mul _).add (hsq.const_mul _), ?_⟩
  simp only [scalarFirst]
  rw [integral_add (hlog.const_mul _) (hsq.const_mul _), integral_const_mul,
    integral_const_mul, hlogval, hsqval]
  field_simp [hx.ne']

/-- Integrating the second scalar derivative gives the repeated-level value. -/
theorem integral_scalarSecond {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun l => scalarSecond l x) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), scalarSecond l x) = 6*x*Real.log x+5*x := by
  obtain ⟨hlog, hlogval⟩ := scalar_log_resolvent hx
  obtain ⟨hsq, hsqval⟩ := integral_shift_inv_sq hx
  obtain ⟨hcube, hcubeval⟩ := integral_shift_inv_cube hx
  have hsum := (hlog.const_mul (6*x)).add (hsq.const_mul (6*x^2))
  refine ⟨hsum.sub (hcube.const_mul _), ?_⟩
  have hsub := integral_sub hsum (hcube.const_mul (2*x^3))
  simp only [Pi.add_apply] at hsub
  simp only [scalarSecond]
  rw [hsub, integral_add (hlog.const_mul _) (hsq.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, hlogval, hsqval, hcubeval]
  field_simp [hx.ne']
  ring

/-- Integrated Hessian kernel of x³ log x, including the coincident-level value. -/
def logHessian (x y : ℝ) : ℝ :=
  if x = y then 6*x*Real.log x+5*x
  else ((3*x^2*Real.log x+x^2) - (3*y^2*Real.log y+y^2))/(x-y)

/-- The shift kernel is integrable and its exact integral is the cubic-log Hessian kernel. -/
theorem integral_shiftHessian {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun l => shiftHessian l x y) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), shiftHessian l x y) = logHessian x y := by
  by_cases hxy : x = y
  · subst y
    obtain ⟨hi, hv⟩ := integral_scalarSecond hx
    refine ⟨hi.congr_fun (fun l hl => (shiftHessian_self hx hl).symm) measurableSet_Ioi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi (fun l hl => shiftHessian_self hx hl), hv]
    simp [logHessian]
  · obtain ⟨hix, hvx⟩ := integral_scalarFirst hx
    obtain ⟨hiy, hvy⟩ := integral_scalarFirst hy
    have he (l : ℝ) (hl : l ∈ Ioi (0 : ℝ)) :
        shiftHessian l x y = (x-y)⁻¹ * (scalarFirst l x - scalarFirst l y) := by
      rw [shiftHessian_eq_dividedDifference hx hy hl hxy, div_eq_inv_mul]
    have hi : IntegrableOn (fun l => (x-y)⁻¹ * (scalarFirst l x - scalarFirst l y)) (Ioi 0) :=
      (hix.sub hiy).const_mul _
    refine ⟨hi.congr_fun (fun l hl => (he l hl).symm)
      measurableSet_Ioi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
      integral_sub hix hiy, hvx, hvy, logHessian, ite_eq_right hxy, div_eq_inv_mul]

omit [DecidableEq n] in
/-- The exact integral of the ordered-pair coefficient from the trace polynomial. -/
theorem integral_trace_quadratic (x : n → ℝ) (hx : ∀ i, 0 < x i) (U : Matrix n n ℂ) :
    IntegrableOn (fun l => (1/2 : ℝ) *
      ∑ i, ∑ j, shiftHessian l (x i) (x j) * Complex.normSq (U i j)) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), (1/2 : ℝ) *
        ∑ i, ∑ j, shiftHessian l (x i) (x j) * Complex.normSq (U i j)) =
        (1/2 : ℝ) * ∑ i, ∑ j, logHessian (x i) (x j) * Complex.normSq (U i j) := by
  have hi (i j : n) := (integral_shiftHessian (hx i) (hx j)).1.mul_const
    (Complex.normSq (U i j))
  have hs (i : n) := integrable_finsetSum Finset.univ (fun j _ => hi i j)
  refine ⟨(integrable_finsetSum Finset.univ (fun i _ => hs i)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hs i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const, (integral_shiftHessian (hx i) (hx j)).2]

#print axioms hasDerivAt_scalarCubic
#print axioms hasDerivAt_scalarFirst
#print axioms integral_shiftHessian
#print axioms integral_trace_quadratic

/-- The integrated centered second difference of the staged trace polynomial.
The quadratic coefficient is multiplied by two in the centered difference. -/
theorem integral_cubicPolynomial_centeredDifference
    (x : n → ℝ) (hx : ∀ i, 0 < x i) (U : Matrix n n ℂ) (hU : U.IsHermitian) (t : ℝ) :
    let B := Matrix.diagonal (fun i => (x i : ℂ))
    let f := fun s l => (WuCubicHotInnerEntropy.cubicPolynomial B (s • U) l).trace.re
    IntegrableOn (fun l => f t l + f (-t) l - 2*f 0 l) (Ioi 0) ∧
      (∫ l in Ioi (0 : ℝ), f t l + f (-t) l - 2*f 0 l) =
        t^2 * ∑ i, ∑ j, logHessian (x i) (x j) * Complex.normSq (U i j) := by
  let q := fun l => (1/2 : ℝ) *
    ∑ i, ∑ j, shiftHessian l (x i) (x j) * Complex.normSq (U i j)
  intro B f
  obtain ⟨hi, hv⟩ := integral_trace_quadratic x hx U
  have he (l : ℝ) (hl : l ∈ Ioi (0 : ℝ)) :
      f t l + f (-t) l - 2*f 0 l = (2*t^2)*q l := by
    obtain ⟨a, c, h⟩ := cubicPolynomial_trace_expansion x hx U hU l hl
    change ∀ s : ℝ, f s l = _ at h
    rw [h t, h (-t)]
    dsimp [f, q]
    simp only [zero_smul]
    ring
  have hscaled : IntegrableOn (fun l => (2*t^2)*q l) (Ioi 0) := hi.const_mul _
  refine ⟨hscaled.congr_fun (fun l hl => (he l hl).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul]
  change (2*t^2) * (∫ l in Ioi (0 : ℝ), q l) = _
  rw [show (∫ l in Ioi (0 : ℝ), q l) = _ from hv]
  ring

/-- The physical cubic logarithm, after subtracting the mass and Gibbs
logarithm charges, gives this kernel per unordered pair. -/
def entropyPairKernel (x y : ℝ) : ℝ :=
  if x = y then 9*x else 3*(x^2+x*y+y^2)*Real.log (x/y)/(x-y)

/-- The mass charge is 3(x+y) at centered unit mass. The diagonal Gibbs
logarithm assigns 3 log x and 3 log y to the two orientations. -/
theorem entropyPairKernel_eq_sub_charges {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    entropyPairKernel x y =
      3*logHessian x y - 3*(x+y) -
        3*((2*x+y)*Real.log x + (2*y+x)*Real.log y) := by
  by_cases hxy : x = y
  · subst y
    rw [entropyPairKernel, logHessian, ite_eq_left rfl, ite_eq_left rfl]
    ring
  · rw [entropyPairKernel, logHessian, ite_eq_right hxy, ite_eq_right hxy,
      Real.log_div hx.ne' hy.ne']
    field_simp [sub_ne_zero.mpr hxy]
    ring

#print axioms integral_cubicPolynomial_centeredDifference
#print axioms entropyPairKernel_eq_sub_charges

/-- The centered trace of the actual cubic logarithm splits into the exact
quadratic term and the integral of the centered resolvent remainder. -/
theorem cubicLog_trace_centeredRemainder
    (x : n → ℝ) (hx : ∀ i, 0 < x i) (U : Matrix n n ℂ) (hU : U.IsHermitian) (t : ℝ) :
    let B := diagonal (fun i => (x i : ℂ))
    let Y := fun s : ℝ => B + s • U
    (Y t).PosDef → (Y (-t)).PosDef →
    let f := fun s l => (WuCubicHotInnerResolvent.cubicLogIntegrand l (Y s)).trace.re
    let p := fun s l => (cubicPolynomial B (s • U) l).trace.re
    let r := fun l => (f t l + f (-t) l - 2*f 0 l) - (p t l + p (-t) l - 2*p 0 l)
    let g := fun s => ((Y s)^3 * cfc Real.log (Y s)).trace.re
    IntegrableOn r (Ioi (0 : ℝ)) ∧
      g t + g (-t) - 2*g 0 =
        t^2 * (∑ i, ∑ j, logHessian (x i) (x j) * Complex.normSq (U i j)) +
          ∫ l in Ioi (0 : ℝ), r l := by
  intro B Y hp hm f p r g
  have hzero : (Y 0).PosDef := by
    dsimp only [Y]
    rw [zero_smul, add_zero]
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    exact_mod_cast hx i
  obtain ⟨hit, hvt⟩ := WuCubicHotInnerEntropy.integral_cubicLogIntegrand (Y t) hp
  obtain ⟨him, hvm⟩ := WuCubicHotInnerEntropy.integral_cubicLogIntegrand (Y (-t)) hm
  obtain ⟨hi₀, hv₀⟩ := WuCubicHotInnerEntropy.integral_cubicLogIntegrand (Y 0) hzero
  change IntegrableOn (f t) (Ioi 0) at hit
  change IntegrableOn (f (-t)) (Ioi 0) at him
  change IntegrableOn (f 0) (Ioi 0) at hi₀
  change (∫ l in Ioi (0 : ℝ), f t l) = g t at hvt
  change (∫ l in Ioi (0 : ℝ), f (-t) l) = g (-t) at hvm
  change (∫ l in Ioi (0 : ℝ), f 0 l) = g 0 at hv₀
  have hi : IntegrableOn (fun l => f t l + f (-t) l - 2*f 0 l) (Ioi 0) :=
    (hit.add him).sub (hi₀.const_mul _)
  have hs := integral_sub (hit.add him) (hi₀.const_mul (2 : ℝ))
  simp only [Pi.add_apply] at hs
  have hv : (∫ l in Ioi (0 : ℝ), f t l + f (-t) l - 2*f 0 l) =
      g t + g (-t) - 2*g 0 := by
    rw [hs, integral_add hit him, integral_const_mul, hvt, hvm, hv₀]
  obtain ⟨hiP, hvP⟩ := integral_cubicPolynomial_centeredDifference x hx U hU t
  change IntegrableOn (fun l => p t l + p (-t) l - 2*p 0 l) (Ioi 0) at hiP
  change (∫ l in Ioi (0 : ℝ), p t l + p (-t) l - 2*p 0 l) =
    t^2 * (∑ i, ∑ j, logHessian (x i) (x j) * Complex.normSq (U i j)) at hvP
  refine ⟨hi.sub hiP, ?_⟩
  dsimp only [r]
  rw [integral_sub hi hiP, hv, hvP]
  ring

#print axioms cubicLog_trace_centeredRemainder

private theorem trace_cubicQuadratic_diagonalWeight (x g : n → ℝ)
    (U : Matrix n n ℂ) (hU : U.IsHermitian) :
    let B := diagonal (fun i => (x i : ℂ))
    let G := diagonal (fun i => (g i : ℂ))
    ((B * U^2 + U * B * U + U^2 * B) * G).trace.re =
      ∑ i, ∑ j, ((2*x i+x j)*g i) * Complex.normSq (U i j) := by
  intro B G
  have h₁ : (B * U^2 * G).trace.re =
      ∑ i, ∑ j, (x i*g i) * Complex.normSq (U i j) := by
    simpa only [B, G, pow_two, Complex.ofReal_one, Matrix.diagonal_one, mul_one, mul_assoc]
      using trace_diagonal_three hU x (fun _ => 1) g
  have h₂ : (U * B * U * G).trace.re =
      ∑ i, ∑ j, (x j*g i) * Complex.normSq (U i j) := by
    simpa only [B, G, Complex.ofReal_one, Matrix.diagonal_one, one_mul]
      using trace_diagonal_three hU (fun _ => 1) x g
  have h₃ : (U^2 * B * G).trace.re =
      ∑ i, ∑ j, (x i*g i) * Complex.normSq (U i j) := by
    rw [mul_assoc]
    have hBG : B * G = diagonal (fun i => ((x i*g i : ℝ) : ℂ)) := by
      simp only [B, G, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]
    rw [hBG]
    simpa only [pow_two, Complex.ofReal_one, Matrix.diagonal_one, one_mul, mul_one]
      using trace_diagonal_three hU (fun _ => 1) (fun _ => 1) (fun i => x i*g i)
  simp only [add_mul, Matrix.trace_add, Complex.add_re, h₁, h₂, h₃,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- The integrated physical cubic-log coefficient after the matrix mass
and Gibbs quadratic charges. At centered unit mass the quadratic mass
charge is the trace of the quadratic coefficient of the cube. -/
theorem physical_trace_quadratic_sub_charges
    (x : n → ℝ) (hx : ∀ i, 0 < x i) (U : Matrix n n ℂ) (hU : U.IsHermitian) :
    let B := diagonal (fun i => (x i : ℂ))
    let T := B * U^2 + U * B * U + U^2 * B
    3 * (∫ l in Ioi (0 : ℝ), (1/2 : ℝ) *
      ∑ i, ∑ j, shiftHessian l (x i) (x j) * Complex.normSq (U i j)) -
      T.trace.re - (T * cfc Real.log (B^3)).trace.re =
      (1/2 : ℝ) * ∑ i, ∑ j, entropyPairKernel (x i) (x j) * Complex.normSq (U i j) := by
  intro B T
  rw [(integral_trace_quadratic x hx U).2]
  let g : n → ℝ := fun i => 1 + 3 * Real.log (x i)
  let N : n → n → ℝ := fun i j => Complex.normSq (U i j)
  let k : n → n → ℝ := fun i j => (2*x i+x j)*g i
  have hB3 : B^3 = diagonal (fun i => ((x i ^ 3 : ℝ) : ℂ)) := by
    simp only [B, Matrix.diagonal_pow, Complex.ofReal_pow]
    rfl
  have hGibbs : cfc Real.log (B^3) =
      diagonal (fun i => ((3 * Real.log (x i) : ℝ) : ℂ)) := by
    rw [hB3]
    refine (Matrix.cfc_diagonal_real (𝕜 := ℂ) (fun i => x i ^ 3) Real.log).trans ?_
    apply congrArg diagonal
    funext i
    change (Real.log (x i ^ 3) : ℂ) = ((3 * Real.log (x i) : ℝ) : ℂ)
    exact congrArg Complex.ofReal (by simpa only [Nat.cast_ofNat] using Real.log_pow (x i) 3)
  have hweight : (1 : Matrix n n ℂ) + cfc Real.log (B^3) =
      diagonal (fun i => (g i : ℂ)) := by
    rw [hGibbs, ← Matrix.diagonal_one]
    simpa only [g, Complex.ofReal_add, Complex.ofReal_one] using
      Matrix.diagonal_add (fun _ : n => (1 : ℂ))
        (fun i => ((3 * Real.log (x i) : ℝ) : ℂ))
  have hcharge : T.trace.re + (T * cfc Real.log (B^3)).trace.re = ∑ i, ∑ j, k i j * N i j := by
    calc
      _ = (T * 1 + T * cfc Real.log (B^3)).trace.re := by
        simp only [T, mul_one, Matrix.trace_add, Complex.add_re]
      _ = _ := by
        rw [← mul_add, hweight]
        exact trace_cubicQuadratic_diagonalWeight x g U hU
  have hN (i j : n) : N i j = N j i := by
    change Complex.normSq (U i j) = Complex.normSq (U j i)
    rw [← hU.apply i j, Complex.star_def, Complex.normSq_conj]
  have hswap : (∑ i, ∑ j, k j i * N i j) = ∑ i, ∑ j, k i j * N i j := by
    calc
      _ = ∑ i, ∑ j, k j i * N j i := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hN i j]
      _ = _ := Finset.sum_comm
  rw [sub_sub, hcharge]
  change 3 * ((1/2 : ℝ) * ∑ i, ∑ j, logHessian (x i) (x j) * N i j) -
      (∑ i, ∑ j, k i j * N i j) =
        (1/2 : ℝ) * ∑ i, ∑ j, entropyPairKernel (x i) (x j) * N i j
  calc
    _ = (1/2 : ℝ) * ((3 * ∑ i, ∑ j, logHessian (x i) (x j) * N i j) -
          ((∑ i, ∑ j, k i j * N i j) + ∑ i, ∑ j, k j i * N i j)) := by rw [hswap]; ring
    _ = _ := by
      congr 1
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [entropyPairKernel_eq_sub_charges (hx i) (hx j)]
      dsimp [k, g]
      ring

#print axioms physical_trace_quadratic_sub_charges

end D5.S3.Quantum.Semigroups.WuCubicHotInnerDiagonalHessian
