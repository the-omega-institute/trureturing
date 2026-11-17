/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalSingularPartners
   generality: G
   mirror-B: none(waiver:original-singular-value-pair-endpoint)
   mirror-E: none(waiver:open-total-original-count)
   anchors: []
   utility: none
   digest: Actual original singular partners give bounded algebraic integer value pairs. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalCoefficients
import D5.S3.Arith.Divisors.NumberFieldDivisorSubpower
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.RingTheory.AdjoinRoot

/-! Genuine factor roots turn actual original endpoints into algebraic integer divisors. -/

open Polynomial NumberField
open scoped NumberField BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

/-- The linear polynomial belonging to an actual integer endpoint coordinate. -/
def coordinateLinear (z : Coordinate) : ℤ[X] := PrimeCube.linear z.1 z.2

/-- The quadratic expression in the genuine fixed-factor divisor identity. -/
def singularValuePolynomial (q : Coordinate) (base : Endpoint) (x : Coordinate) : ℤ[X] :=
  -endpointQ base + endpointL q base * coordinateLinear x

/-- The product in the genuine divisor identity, before evaluation at a factor root. -/
def singularProductPolynomial (q : Coordinate) (base : Endpoint) : ℤ[X] :=
  endpointQ base * (endpointQ base - endpointL q base * coordinateLinear q)

private theorem singular_divisor_identity (q : Coordinate) (base e : Endpoint) :
    singularValuePolynomial q base e.1 * singularValuePolynomial q base e.2 -
      singularProductPolynomial q base = endpointL q base * pencil q base e := by
  simp only [singularValuePolynomial, singularProductPolynomial, pencil,
    endpointL, endpointQ, coordinateLinear, PrimeCube.linear, PrimeCube.quadratic,
    coeffL, coeffM, coeffQ, coeffR, coeffS]
  simp only [map_add, map_sub, map_mul]
  ring

private theorem singular_value_degree (q : Coordinate) (base : Endpoint) (x : Coordinate) :
    (singularValuePolynomial q base x).natDegree ≤ 2 := by
  unfold singularValuePolynomial endpointQ endpointL coordinateLinear
    PrimeCube.linear PrimeCube.quadratic
  compute_degree

private theorem endpointQ_degree (base : Endpoint) : (endpointQ base).natDegree ≤ 2 := by
  unfold endpointQ PrimeCube.quadratic
  compute_degree

private theorem singular_second_degree (q : Coordinate) (base : Endpoint) :
    (endpointQ base - endpointL q base * coordinateLinear q).natDegree ≤ 2 := by
  unfold endpointQ endpointL coordinateLinear PrimeCube.linear PrimeCube.quadratic
  compute_degree

/-- The actual number field cut out by an integer irreducible factor. -/
abbrev SingularFactorField (F : ℤ[X]) := AdjoinRoot (F.map (Int.castRingHom ℚ))

private theorem singular_root_eval (F P : ℤ[X])
    [Fact (Irreducible (F.map (Int.castRingHom ℚ)))] :
    P.eval₂ (Int.castRingHom (SingularFactorField F)) (AdjoinRoot.root (F.map (Int.castRingHom ℚ))) =
      AdjoinRoot.mk (F.map (Int.castRingHom ℚ)) (P.map (Int.castRingHom ℚ)) := by
  have hcomp : (AdjoinRoot.of (F.map (Int.castRingHom ℚ))).comp (Int.castRingHom ℚ) =
      Int.castRingHom (SingularFactorField F) := by ext z; simp
  rw [← hcomp, ← Polynomial.eval₂_map]
  rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

private theorem singular_root_self (F : ℤ[X])
    [Fact (Irreducible (F.map (Int.castRingHom ℚ)))] :
    F.eval₂ (Int.castRingHom (SingularFactorField F)) (AdjoinRoot.root (F.map (Int.castRingHom ℚ))) = 0 := by
  rw [singular_root_eval, AdjoinRoot.mk_self]

/-- The leading coefficient times the actual factor root is an algebraic integer. -/
def singularTheta (F : ℤ[X]) [Fact (Irreducible (F.map (Int.castRingHom ℚ)))] :
    𝓞 (SingularFactorField F) :=
  ⟨(F.leadingCoeff : SingularFactorField F) * AdjoinRoot.root (F.map (Int.castRingHom ℚ)),
    by
      change (Int.castRingHom (SingularFactorField F)).IsIntegralElem _
      apply RingHom.isIntegralElem_leadingCoeff_mul
      exact singular_root_self F⟩

private def scaledQuadratic (F P : ℤ[X])
    [Fact (Irreducible (F.map (Int.castRingHom ℚ)))] : 𝓞 (SingularFactorField F) :=
  (P.coeff 0 : 𝓞 (SingularFactorField F)) * (F.leadingCoeff : 𝓞 (SingularFactorField F))^2 +
    (P.coeff 1 : 𝓞 (SingularFactorField F)) * F.leadingCoeff * singularTheta F +
      (P.coeff 2 : 𝓞 (SingularFactorField F)) * (singularTheta F)^2

private theorem scaledQuadratic_eval (F P : ℤ[X])
    [Fact (Irreducible (F.map (Int.castRingHom ℚ)))] (hd : P.natDegree ≤ 2) :
    (scaledQuadratic F P : SingularFactorField F) =
      (F.leadingCoeff : SingularFactorField F)^2 *
        P.eval₂ (Int.castRingHom (SingularFactorField F)) (AdjoinRoot.root (F.map (Int.castRingHom ℚ))) := by
  rw [Polynomial.eval₂_eq_sum_range' _ (by omega : P.natDegree < 3)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    zero_add, scaledQuadratic, RingOfIntegers.coe_eq_algebraMap,
    map_add, map_mul, map_pow, map_intCast, singularTheta, RingOfIntegers.map_mk, eq_intCast]
  ring

/-- The genuine scaled original value at one actual integer endpoint. -/
def singularFactorValue (F : ℤ[X]) [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (q : Coordinate) (base : Endpoint) (x : Coordinate) : 𝓞 (SingularFactorField F) :=
  scaledQuadratic F (singularValuePolynomial q base x)

/-- The fixed algebraic integer product supplied by the actual baseline. -/
def singularFactorProduct (F : ℤ[X]) [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (q : Coordinate) (base : Endpoint) : 𝓞 (SingularFactorField F) :=
  scaledQuadratic F (endpointQ base) *
    scaledQuadratic F (endpointQ base - endpointL q base * coordinateLinear q)

/-- The actual algebraic value pairs of endpoints belonging to one factor. -/
def singularFactorValuePairs (F : ℤ[X]) [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (q : Coordinate) (base : Endpoint) (S : Finset Endpoint) :
    Finset (𝓞 (SingularFactorField F) × 𝓞 (SingularFactorField F)) := by
  classical
  exact (S.filter (fun e => F ∣ pencil q base e)).image
    (fun e => (singularFactorValue F q base e.1, singularFactorValue F q base e.2))

private theorem actual_singular_factor_product (F : ℤ[X])
    [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (q : Coordinate) (base e : Endpoint) (hF : F ∣ pencil q base e) :
    singularFactorValue F q base e.1 * singularFactorValue F q base e.2 =
      singularFactorProduct F q base := by
  have hroot : (pencil q base e).eval₂ (Int.castRingHom (SingularFactorField F))
      (AdjoinRoot.root (F.map (Int.castRingHom ℚ))) = 0 := by
    rw [singular_root_eval, AdjoinRoot.mk_eq_zero]
    exact Polynomial.map_dvd (Int.castRingHom ℚ) hF
  apply RingOfIntegers.ext
  simp only [singularFactorValue, singularFactorProduct,
    RingOfIntegers.coe_eq_algebraMap, map_mul,
    scaledQuadratic_eval F _ (singular_value_degree q base e.1),
    scaledQuadratic_eval F _ (singular_value_degree q base e.2),
    scaledQuadratic_eval F _ (endpointQ_degree base),
    scaledQuadratic_eval F _ (singular_second_degree q base)]
  have hid := congrArg
    (Polynomial.eval₂RingHom (Int.castRingHom (SingularFactorField F))
      (AdjoinRoot.root (F.map (Int.castRingHom ℚ))))
    (singular_divisor_identity q base e)
  simp only [coe_eval₂RingHom, singularProductPolynomial, eval₂_sub, eval₂_mul,
    hroot, mul_zero] at hid
  simp only [eval₂_sub, eval₂_mul]
  linear_combination (F.leadingCoeff : SingularFactorField F)^4 * hid

private theorem singular_root_nonzero_of_unit {p : ℕ} [Fact p.Prime]
    (F P : ℤ[X]) [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (hprim : F.IsPrimitive) (b : ℤ) (hFb : ((F.eval b : ℤ) : ZMod p) = 0)
    (hunit : IsUnit ((P.eval b : ℤ) : ZMod p)) :
    P.eval₂ (Int.castRingHom (SingularFactorField F)) (AdjoinRoot.root (F.map (Int.castRingHom ℚ))) ≠ 0 := by
  intro hz
  rw [singular_root_eval, AdjoinRoot.mk_eq_zero] at hz
  have hdvd := (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast F P hprim).mpr hz
  obtain ⟨U, hU⟩ := hdvd
  apply hunit.ne_zero
  rw [hU, eval_mul, Int.cast_mul, hFb, zero_mul]

private theorem singularFactorProduct_ne_zero {p : ℕ} [Fact p.Prime]
    (F : ℤ[X]) [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (hprim : F.IsPrimitive) (b : ℤ) (hFb : ((F.eval b : ℤ) : ZMod p) = 0)
    (q : Coordinate) (base : Endpoint)
    (hQ : IsUnit (((endpointQ base).eval b : ℤ) : ZMod p))
    (hQZ : IsUnit (((endpointQ base - endpointL q base * coordinateLinear q).eval b : ℤ) : ZMod p)) :
    singularFactorProduct F q base ≠ 0 := by
  have hF : F ≠ 0 := hprim.ne_zero
  have ha : (F.leadingCoeff : SingularFactorField F) ≠ 0 := by
    exact_mod_cast leadingCoeff_ne_zero.mpr hF
  have hq := singular_root_nonzero_of_unit F (endpointQ base) hprim b hFb hQ
  have hqz := singular_root_nonzero_of_unit F
    (endpointQ base - endpointL q base * coordinateLinear q) hprim b hFb hQZ
  intro hz
  have hh := congrArg (fun x : 𝓞 (SingularFactorField F) => (x : SingularFactorField F)) hz
  simp only [singularFactorProduct, RingOfIntegers.coe_eq_algebraMap, map_mul, map_zero,
    scaledQuadratic_eval F _ (endpointQ_degree base),
    scaledQuadratic_eval F _ (singular_second_degree q base)] at hh
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) hq)
    (mul_ne_zero (pow_ne_zero 2 ha) hqz) hh

private theorem factor_coeff_bound (p : ℝ) (hp : 8 ≤ p) (P F : ℤ[X])
    (hP : P ≠ 0) (hd : P.natDegree ≤ 3) (hF : F ∣ P)
    (hcoeff : ∀ j, |(P.coeff j : ℝ)| ≤ p^2) :
    ∀ j, |(F.coeff j : ℝ)| ≤ p^3 := by
  obtain ⟨U, hU⟩ := hF
  have hFn : F ≠ 0 := by intro hz; simp [hz] at hU; exact hP hU
  have hUn : U ≠ 0 := by intro hz; simp [hz] at hU; exact hP hU
  let f := F.map (Int.castRingHom ℂ)
  let u := U.map (Int.castRingHom ℂ)
  let P' := P.map (Int.castRingHom ℂ)
  have heq : P' = f * u := by simp only [P', f, u, hU, Polynomial.map_mul]
  have huc : (1 : ℝ) ≤ ‖u.coeff U.natDegree‖ := by
    have hi : (1 : ℝ) ≤ |(U.leadingCoeff : ℝ)| := by
      exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hUn)
    simpa only [u, coeff_map, Int.coe_castRingHom, Complex.norm_intCast,
      coeff_natDegree, Nat.cast_natAbs] using hi
  have hus : (1 : ℝ) ≤ u.supNorm := huc.trans (u.le_supNorm _)
  have hPs : P'.supNorm ≤ p^2 := by
    obtain ⟨j, hj⟩ := P'.exists_eq_supNorm
    rw [hj]
    simpa only [P', coeff_map, Int.coe_castRingHom, Complex.norm_intCast,
      Nat.cast_natAbs] using hcoeff j
  have hdegrees : f.natDegree + u.natDegree ≤ 3 := by
    have hm := Polynomial.natDegree_mul hFn hUn
    rw [← hU] at hm
    simpa only [f, u, natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective, ← hm] using hd
  have hpow : (2 : ℝ)^(f.natDegree+u.natDegree) ≤ 8 := by
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdegrees).trans_eq (by norm_num)
  have hG := Polynomial.supNorm_mul_supNorm_le_two_pow f u
  rw [← heq] at hG
  have hfs : f.supNorm ≤ 8 * p^2 := by
    calc
      _ ≤ f.supNorm * u.supNorm := le_mul_of_one_le_right f.supNorm_nonneg hus
      _ ≤ _ := hG
      _ ≤ _ := mul_le_mul hpow hPs P'.supNorm_nonneg (by norm_num)
  intro j
  have hfc : |(F.coeff j : ℝ)| ≤ 8 * p^2 := by
    simpa only [f, coeff_map, Int.coe_castRingHom, Complex.norm_intCast,
      Nat.cast_natAbs] using (f.le_supNorm j).trans hfs
  exact hfc.trans (by nlinarith [sq_nonneg p])

private theorem singular_embedding_eval (F P : ℤ[X])
    [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (σ : SingularFactorField F →+* ℂ) :
    σ (P.eval₂ (Int.castRingHom (SingularFactorField F)) (AdjoinRoot.root (F.map (Int.castRingHom ℚ)))) =
      P.eval₂ (Int.castRingHom ℂ) (σ (AdjoinRoot.root (F.map (Int.castRingHom ℚ)))) := by
  have hcomp : σ.comp (Int.castRingHom (SingularFactorField F)) = Int.castRingHom ℂ := by
    ext z
    simp
  simpa only [Polynomial.aeval_def, algebraMap_int_eq, hcomp] using
    Polynomial.hom_eval₂ P (Int.castRingHom (SingularFactorField F)) σ
      (AdjoinRoot.root (F.map (Int.castRingHom ℚ)))

private theorem singular_root_bound (p : ℝ) (hp : 8 ≤ p) (F : ℤ[X])
    [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (hF : F ≠ 0) (hcoeff : ∀ j, |(F.coeff j : ℝ)| ≤ p^3)
    (σ : SingularFactorField F →+* ℂ) :
    ‖σ (AdjoinRoot.root (F.map (Int.castRingHom ℚ)))‖ ≤ p^4 := by
  let f := F.map (Int.castRingHom ℂ)
  have hfn : f ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hF
  have hr : f.IsRoot (σ (AdjoinRoot.root (F.map (Int.castRingHom ℚ)))) := by
    rw [Polynomial.IsRoot, eval_map, ← singular_embedding_eval]
    simp only [singular_root_self, map_zero]
  have hsup : ((Finset.range f.natDegree).sup (fun j => ‖f.coeff j‖₊) : NNReal) ≤
      ⟨p^3, by positivity⟩ := by
    apply Finset.sup_le
    intro j _
    have hh : ‖f.coeff j‖ ≤ p^3 := by
      simpa only [f, coeff_map, Int.coe_castRingHom, Complex.norm_intCast,
        Nat.cast_natAbs] using hcoeff j
    exact_mod_cast hh
  have hlc : (1 : ℝ) ≤ ‖f.leadingCoeff‖ := by
    have hi : (1 : ℝ) ≤ |(F.leadingCoeff : ℝ)| := by
      exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hF)
    simpa only [f, leadingCoeff_map_of_injective (f := Int.castRingHom ℂ) Int.cast_injective,
      Int.coe_castRingHom, Complex.norm_intCast, Nat.cast_natAbs] using hi
  have hc : (f.cauchyBound : ℝ) ≤ p^3 + 1 := by
    change (((Finset.range f.natDegree).sup (fun j => ‖f.coeff j‖₊) : NNReal) : ℝ) /
      ‖f.leadingCoeff‖ + 1 ≤ p^3 + 1
    apply add_le_add _ le_rfl
    apply (div_le_iff₀ (by linarith : 0 < ‖f.leadingCoeff‖)).mpr
    have hsr : (((Finset.range f.natDegree).sup (fun j => ‖f.coeff j‖₊) : NNReal) : ℝ) ≤ p^3 := by
      exact_mod_cast hsup
    exact hsr.trans (le_mul_of_one_le_right (by positivity) hlc)
  have hh : ‖σ (AdjoinRoot.root (F.map (Int.castRingHom ℚ)))‖ < (f.cauchyBound : ℝ) := by
    exact_mod_cast hr.norm_lt_cauchyBound hfn
  have hp3 : 1 ≤ p^3 := one_le_pow₀ (by linarith : 1 ≤ p)
  have hp4 : 8*p^3 ≤ p*p^3 := mul_le_mul_of_nonneg_right hp (by positivity)
  exact hh.le.trans (hc.trans (by nlinarith))

private theorem singularFactorField_degree (F : ℤ[X])
    [hF : Fact (Irreducible (F.map (Int.castRingHom ℚ)))] (hd : F.natDegree ≤ 3) :
    Module.finrank ℚ (SingularFactorField F) ≤ 3 := by
  have hdim := (AdjoinRoot.powerBasis hF.out.ne_zero).finrank
  rw [AdjoinRoot.powerBasis_dim] at hdim
  simp only [natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective] at hdim
  exact hdim.le.trans hd

private theorem singular_value_expansion (q : Coordinate) (base : Endpoint) (x : Coordinate) :
    singularValuePolynomial q base x =
      C (-coeffQ base + coeffL q base*x.1) +
        C (-coeffR base + coeffL q base*x.2 + coeffM q base*x.1)*X +
          C (-coeffS base + coeffM q base*x.2)*X^2 := by
  simp only [singularValuePolynomial, endpointQ, endpointL, coordinateLinear,
    PrimeCube.linear, PrimeCube.quadratic, map_add, map_sub, map_mul, map_neg]
  ring

private theorem singular_value_coeff_bound (p : ℝ) (hp : 1 ≤ p)
    (q : Coordinate) (base : Endpoint) (x : Coordinate)
    (hl : |(coeffL q base : ℝ)| ≤ p^2) (hm : |(coeffM q base : ℝ)| ≤ p^2)
    (hu : |(coeffQ base : ℝ)| ≤ p^2) (hv : |(coeffR base : ℝ)| ≤ p^2)
    (hw : |(coeffS base : ℝ)| ≤ p^2)
    (hx : |(x.1 : ℝ)| ≤ p) (hy : |(x.2 : ℝ)| ≤ p) :
    ∀ j ≤ 2, |((singularValuePolynomial q base x).coeff j : ℝ)| ≤ 3 * p^3 := by
  have hprod (a b : ℝ) (ha : |a| ≤ p^2) (hb : |b| ≤ p) : |a*b| ≤ p^3 := by
    rw [abs_mul]
    calc
      _ ≤ p^2*p := mul_le_mul ha hb (abs_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hp23 : p^2 ≤ p^3 := by nlinarith [sq_nonneg p]
  have hc0 : (singularValuePolynomial q base x).coeff 0 =
      -coeffQ base + coeffL q base * x.1 := by
    rw [singular_value_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    norm_num
  have hc1 : (singularValuePolynomial q base x).coeff 1 =
      -coeffR base + coeffL q base * x.2 + coeffM q base * x.1 := by
    rw [singular_value_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    norm_num
  have hc2 : (singularValuePolynomial q base x).coeff 2 =
      -coeffS base + coeffM q base * x.2 := by
    rw [singular_value_expansion]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    norm_num
  intro j hj
  interval_cases j
  · rw [hc0]
    push_cast
    have hb := (abs_add_le (-(coeffQ base : ℝ)) ((coeffL q base : ℝ)*(x.1 : ℝ)))
    rw [abs_neg] at hb
    nlinarith [hprod _ _ hl hx]
  · rw [hc1]
    push_cast
    have hb := (abs_add_le (-(coeffR base : ℝ)+(coeffL q base : ℝ)*(x.2 : ℝ))
      ((coeffM q base : ℝ)*(x.1 : ℝ))).trans
      (add_le_add (abs_add_le (-(coeffR base : ℝ))
        ((coeffL q base : ℝ)*(x.2 : ℝ))) le_rfl)
    rw [abs_neg] at hb
    nlinarith [hprod _ _ hl hy, hprod _ _ hm hx]
  · rw [hc2]
    push_cast
    have hb := abs_add_le (-(coeffS base : ℝ)) ((coeffM q base : ℝ)*(x.2 : ℝ))
    rw [abs_neg] at hb
    nlinarith [hprod _ _ hm hy]

private theorem quadratic_eval_bound (p : ℝ) (hp : 1 ≤ p) (P : ℤ[X])
    (hd : P.natDegree ≤ 2) (hc : ∀ j ≤ 2, |(P.coeff j : ℝ)| ≤ 3 * p^3)
    (z : ℂ) (hz : ‖z‖ ≤ p^4) :
    ‖P.eval₂ (Int.castRingHom ℂ) z‖ ≤ 9 * p^11 := by
  have hnorm : ∀ j ≤ 2, ‖(P.coeff j : ℂ)‖ ≤ 3 * p^3 := by
    intro j hj
    simpa only [Complex.norm_intCast, Nat.cast_natAbs] using hc j hj
  rw [eval₂_eq_sum_range' _ (by omega : P.natDegree < 3)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, mul_one, Int.coe_castRingHom]
  calc
    _ ≤ (‖(P.coeff 0 : ℂ)‖ + ‖(P.coeff 1 : ℂ)‖ * ‖z‖) +
        ‖(P.coeff 2 : ℂ)‖ * ‖z‖^2 := by
      have hh : ‖(P.coeff 0 : ℂ)+(P.coeff 1 : ℂ)*z+(P.coeff 2 : ℂ)*z^2‖ ≤
          (‖(P.coeff 0 : ℂ)‖+‖(P.coeff 1 : ℂ)*z‖)+‖(P.coeff 2 : ℂ)*z^2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      simpa only [norm_mul, norm_pow] using hh
    _ ≤ (3*p^3+3*p^3*p^4)+3*p^3*(p^4)^2 := by
      gcongr
      · exact hnorm 0 (by omega)
      · exact hnorm 1 (by omega)
      · exact hnorm 2 (by omega)
    _ ≤ 9*p^11 := by
      have h3 : p^3 ≤ p^11 := pow_le_pow_right₀ hp (by decide)
      have h7 : p^7 ≤ p^11 := pow_le_pow_right₀ hp (by decide)
      nlinarith

private theorem singular_value_embedding_bound (p : ℝ) (hp : 16 ≤ p) (F : ℤ[X])
    [Fact (Irreducible (F.map (Int.castRingHom ℚ)))]
    (hF : F ≠ 0) (hcoeff : ∀ j, |(F.coeff j : ℝ)| ≤ p^3)
    (q : Coordinate) (base : Endpoint) (x : Coordinate)
    (hl : |(coeffL q base : ℝ)| ≤ p^2) (hm : |(coeffM q base : ℝ)| ≤ p^2)
    (hu : |(coeffQ base : ℝ)| ≤ p^2) (hv : |(coeffR base : ℝ)| ≤ p^2)
    (hw : |(coeffS base : ℝ)| ≤ p^2)
    (hx : |(x.1 : ℝ)| ≤ p) (hy : |(x.2 : ℝ)| ≤ p)
    (σ : SingularFactorField F →+* ℂ) :
    ‖σ (singularFactorValue F q base x : SingularFactorField F)‖ ≤ p^18 := by
  have hp1 : 1 ≤ p := by linarith
  have ha := hcoeff F.natDegree
  rw [coeff_natDegree] at ha
  have hroot := singular_root_bound p (by linarith) F hF hcoeff σ
  have hb := quadratic_eval_bound p hp1 (singularValuePolynomial q base x)
    (singular_value_degree q base x)
    (singular_value_coeff_bound p hp1 q base x hl hm hu hv hw hx hy) _ hroot
  have heq := congrArg σ (scaledQuadratic_eval F (singularValuePolynomial q base x)
    (singular_value_degree q base x))
  change σ (singularFactorValue F q base x : SingularFactorField F) = _ at heq
  simp only [map_mul, map_pow, map_intCast, singular_embedding_eval] at heq
  rw [heq, norm_mul, norm_pow, Complex.norm_intCast]
  have hscale : |(F.leadingCoeff : ℝ)|^2 ≤ (p^3)^2 :=
    pow_le_pow_left₀ (abs_nonneg (F.leadingCoeff : ℝ)) ha 2
  calc
    _ ≤ (p^3)^2*(9*p^11) := mul_le_mul hscale hb (norm_nonneg _) (by positivity)
    _ = 9*p^17 := by ring
    _ ≤ p*p^17 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = p^18 := by ring

private theorem algebraic_product_norm_bound {K : Type*} [Field K] [NumberField K]
    (hd : Module.finrank ℚ K ≤ 3) (p : ℝ) (hp : 1 ≤ p) (D : 𝓞 K)
    (hb : ∀ σ : K →+* ℂ, ‖σ (D : K)‖ ≤ p^36) :
    ((Algebra.norm ℤ D).natAbs : ℝ) ≤ p^108 := by
  classical
  have hprod : (∏ σ : K →+* ℂ, ‖σ (D : K)‖) =
      ((Algebra.norm ℤ D).natAbs : ℝ) := by
    have h := congr(‖$(Algebra.norm_eq_prod_embeddings ℚ ℂ (D : K))‖).symm
    rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ)
      (fun f => ‖f (D : K)‖) (fun φ => ‖φ (D : K)‖)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
    rw [← Algebra.coe_norm_int D] at h
    simpa only [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast,
      Nat.cast_natAbs, Int.cast_abs] using h
  rw [← hprod]
  calc
    _ ≤ ∏ _σ : K →+* ℂ, p^36 := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun σ _ => hb σ)
    _ = (p^36)^(Module.finrank ℚ K) := by simp only [Finset.prod_const,
      Finset.card_univ, NumberField.Embeddings.card]
    _ ≤ (p^36)^3 := pow_le_pow_right₀ (one_le_pow₀ hp) hd
    _ = p^108 := by ring

private theorem original_singular_unit_observations {c : ℕ} [NeZero c]
    (a₁ a₂ : ZMod c) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (base : Endpoint)
    (hr : IsUnit (R.1 : ZMod c)) (ht : IsUnit (-(physical R V q).2 : ZMod c))
    (he : WordSolution c a₁ a₂ R V q base)
    (hx : IsUnit ((physical R V base.1).1 : ZMod c))
    (hy : IsUnit ((physical R V base.2).1 : ZMod c))
    (hk : IsUnit (1 - a₁*a₂*(ht.unit : ZMod c)*((physical R V q).1 : ZMod c))) :
    let β := (V.1 : ZMod c) * (↑hr.unit⁻¹ : ZMod c)
    IsUnit ((endpointL q base).eval₂ (Int.castRingHom _) β) ∧
      IsUnit ((endpointQ base).eval₂ (Int.castRingHom _) β) ∧
      IsUnit ((endpointQ base - endpointL q base * coordinateLinear q).eval₂
        (Int.castRingHom _) β) := by
  dsimp only
  let gt := ha₁.unit * ha₂.unit * ht.unit
  let gtr := gt * hr.unit
  let β : ZMod c := (V.1 : ZMod c) * (↑hr.unit⁻¹ : ZMod c)
  let α : ZMod c := -(↑gtr⁻¹ : ZMod c)
  let value (z : Coordinate) : ZMod c := (z.1 : ZMod c) + β*z.2
  have hphys (z : Coordinate) : ((physical R V z).1 : ZMod c) =
      (hr.unit : ZMod c)*value z := by
    have hinv : (↑hr.unit⁻¹ : ZMod c)*(hr.unit : ZMod c)=1 := by simp
    simp only [physical, Int.cast_add, Int.cast_mul, value, β]
    linear_combination -(V.1 : ZMod c)*(z.2 : ZMod c)*hinv -
      (z.1 : ZMod c)*hr.unit_spec
  rw [hphys base.1] at hx
  rw [hphys base.2] at hy
  have hxv := (IsUnit.mul_iff.mp hx).2
  have hyv := (IsUnit.mul_iff.mp hy).2
  have heval (n : ℤ) : (n : ℤ[X]).eval₂ (Int.castRingHom (ZMod c)) β =
      (n : ZMod c) := map_intCast
        (Polynomial.eval₂RingHom (Int.castRingHom (ZMod c)) β) n
  have hQ : (endpointQ base).eval₂ (Int.castRingHom (ZMod c)) β = value base.1*value base.2 := by
    simp [endpointQ, PrimeCube.quadratic, coeffQ, coeffR, coeffS, heval, value]
    ring
  have hQu : IsUnit ((endpointQ base).eval₂ (Int.castRingHom (ZMod c)) β) := by
    rw [hQ]
    exact hxv.mul hyv
  have hid : α*(endpointL q base).eval₂ (Int.castRingHom (ZMod c)) β +
      (endpointQ base).eval₂ (Int.castRingHom (ZMod c)) β = 0 := by
    simpa [α, gtr, gt, β] using
      original_endpoint_identity a₁ a₂ ha₁ ha₂ R V q base hr ht he
  have hαL : α*(endpointL q base).eval₂ (Int.castRingHom (ZMod c)) β =
      -(endpointQ base).eval₂ (Int.castRingHom (ZMod c)) β := by linear_combination hid
  have hLu : IsUnit ((endpointL q base).eval₂ (Int.castRingHom (ZMod c)) β) := by
    have hh : IsUnit (α*(endpointL q base).eval₂ (Int.castRingHom (ZMod c)) β) := by
      rw [hαL]
      exact hQu.neg
    exact (IsUnit.mul_iff.mp hh).2
  have hαgtr : α*(gtr : ZMod c) = -1 := by
    dsimp only [α]
    rw [neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hminus : α*(gt : ZMod c)*((physical R V q).1 : ZMod c) = -value q := by
    rw [hphys]
    have hh : α*(gt : ZMod c)*((hr.unit : ZMod c)*value q) =
        (α*(gtr : ZMod c))*value q := by
      simp only [gtr, Units.val_mul]
      ring
    rw [hh, hαgtr]
    ring
  have hshift : α+value q = α*(1-(gt : ZMod c)*((physical R V q).1 : ZMod c)) := by
    linear_combination hminus
  have hshiftu : IsUnit (α+value q) := by
    rw [hshift]
    exact (gtr⁻¹).isUnit.neg.mul (by
      simpa [gt, Units.val_mul, ha₁.unit_spec, ha₂.unit_spec, mul_assoc] using hk)
  refine ⟨hLu, hQu, ?_⟩
  have heq : (endpointQ base - endpointL q base * coordinateLinear q).eval₂
      (Int.castRingHom (ZMod c)) β =
      -(endpointL q base).eval₂ (Int.castRingHom (ZMod c)) β*(α+value q) := by
    simp only [eval₂_sub, eval₂_mul, coordinateLinear, PrimeCube.linear,
      eval₂_add, eval₂_C, eval₂_mul, eval₂_X, Int.coe_castRingHom]
    dsimp only [value]
    linear_combination hid
  rw [heq]
  exact hLu.neg.mul hshiftu

private theorem fixed_factor_value_pairs_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime], 16 ≤ (p : ℝ) →
      ∀ (F : ℤ[X]) [Fact (Irreducible (F.map (Int.castRingHom ℚ)))],
      F.IsPrimitive → F.natDegree ≤ 3 →
      (∀ j, |(F.coeff j : ℝ)| ≤ (p : ℝ)^3) → ∀ (b : ℤ),
      ((F.eval b : ℤ) : ZMod p) = 0 → ∀ (q : Coordinate) (base : Endpoint)
      (S : Finset Endpoint) (e₀ : Endpoint), e₀ ∈ S → F ∣ pencil q base e₀ →
      IsUnit (((endpointQ base).eval b : ℤ) : ZMod p) →
      IsUnit (((endpointQ base-endpointL q base*coordinateLinear q).eval b : ℤ) : ZMod p) →
      |(coeffL q base : ℝ)| ≤ (p : ℝ)^2 → |(coeffM q base : ℝ)| ≤ (p : ℝ)^2 →
      |(coeffQ base : ℝ)| ≤ (p : ℝ)^2 → |(coeffR base : ℝ)| ≤ (p : ℝ)^2 →
      |(coeffS base : ℝ)| ≤ (p : ℝ)^2 →
      (∀ e ∈ S, ∀ z ∈ ({e.1,e.2} : Finset Coordinate),
        |(z.1 : ℝ)| ≤ p ∧ |(z.2 : ℝ)| ≤ p) →
      ((singularFactorValuePairs F q base S).card : ℝ) ≤ C*(p : ℝ)^ε := by
  classical
  obtain ⟨C, hC, hcount⟩ :=
    D5.S3.Arith.Divisors.NumberFieldDivisorSubpower.fixed_product_pairs_subpower ε hε
  refine ⟨C, hC, ?_⟩
  intro p _ hp F _ hprim hd hcoeff b hFb q base S e₀ he₀ hFe₀ hQu hQZu
    hl hm hu hv hw hS
  let D := singularFactorProduct F q base
  have hD : D ≠ 0 := singularFactorProduct_ne_zero F hprim b hFb q base hQu hQZu
  have hpoint (x : Coordinate) (hx : |(x.1 : ℝ)| ≤ p) (hy : |(x.2 : ℝ)| ≤ p)
      (σ : SingularFactorField F →+* ℂ) :
      ‖σ (singularFactorValue F q base x : SingularFactorField F)‖ ≤ (p : ℝ)^18 :=
    singular_value_embedding_bound (p : ℝ) hp F hprim.ne_zero hcoeff q base x
      hl hm hu hv hw hx hy σ
  have hDemb (σ : SingularFactorField F →+* ℂ) : ‖σ (D : SingularFactorField F)‖ ≤ (p : ℝ)^36 := by
    have hprod := actual_singular_factor_product F q base e₀ hFe₀
    have hx := hS e₀ he₀ e₀.1 (by simp)
    have hy := hS e₀ he₀ e₀.2 (by simp)
    change ‖σ (singularFactorProduct F q base : SingularFactorField F)‖ ≤ _
    rw [← hprod]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul]
    calc
      _ ≤ (p : ℝ)^18*(p : ℝ)^18 := mul_le_mul (hpoint _ hx.1 hx.2 σ)
        (hpoint _ hy.1 hy.2 σ) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hnorm := algebraic_product_norm_bound (singularFactorField_degree F hd)
    (p : ℝ) (by linarith) D hDemb
  unfold singularFactorValuePairs
  apply hcount (SingularFactorField F) (singularFactorField_degree F hd) (p : ℝ)
    (by linarith) D hD hnorm
  · intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    exact actual_singular_factor_product F q base e (Finset.mem_filter.mp he).2
  · intro z hz σ
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    have hx := hS e (Finset.mem_filter.mp he).1 e.1 (by simp)
    exact hpoint e.1 hx.1 hx.2 σ

private theorem actual_pencil_weighted_coeff (J₁ J₂ : ℝ) (q : Coordinate)
    (base e : Endpoint) (h₁ : 1 ≤ J₁) (h₂ : 1 ≤ J₂)
    (hq : CoordinateBound J₁ J₂ q)
    (hb₁ : CoordinateBound J₁ J₂ base.1) (hb₂ : CoordinateBound J₁ J₂ base.2)
    (he₁ : CoordinateBound J₁ J₂ e.1) (he₂ : CoordinateBound J₁ J₂ e.2) :
    ∀ j ≤ (pencil q base e).natDegree,
      |((pencil q base e).coeff j : ℝ)| ≤ 18 * J₁^(3-j) * J₂^j := by
  have hh := actual_pencil_coefficient_bounds J₁ J₂ q base e hq hb₁ hb₂ he₁ he₂
  intro j hj
  have hj3 := hj.trans (pencil_natDegree q base e)
  interval_cases j <;> norm_num at *
  · nlinarith [pow_nonneg (by linarith : 0 ≤ J₁) 3]
  · exact hh.2.1
  · exact hh.2.2.1
  · nlinarith [pow_nonneg (by linarith : 0 ≤ J₂) 3]

private theorem reduce_eval_at_lift {c p : ℕ} (f : ZMod c →+* ZMod p)
    (P : ℤ[X]) (β : ZMod c) (b : ℤ) (hb : (b : ZMod p) = f β) :
    f (P.eval₂ (Int.castRingHom (ZMod c)) β) = ((P.eval b : ℤ) : ZMod p) := by
  have hcomp : f.comp (Int.castRingHom (ZMod c)) = Int.castRingHom (ZMod p) := by
    ext z
    simp
  change f (P.eval₂ (Int.castRingHom (ZMod c)) β) = (Int.castRingHom (ZMod p)) (P.eval b)
  rw [← Polynomial.eval₂_at_apply]
  simp only [Int.coe_castRingHom, hb]
  simpa only [hcomp] using Polynomial.hom_eval₂ P (Int.castRingHom (ZMod c)) f β

private theorem original_singular_cover (p : ℕ) (hp : p.Prime)
    (J₁ J₂ M : ℝ) (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (base : Endpoint) (S : Finset Endpoint) (e₀ : Endpoint)
    (he₀ : e₀ ∈ S) (hr : IsUnit (R.1 : ZMod (p^3)))
    (ht : IsUnit (-(physical R V q).2 : ZMod (p^3)))
    (hbase : WordSolution (p^3) a₁ a₂ R V q base)
    (hx : IsUnit ((physical R V base.1).1 : ZMod (p^3)))
    (hy : IsUnit ((physical R V base.2).1 : ZMod (p^3)))
    (hk : IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical R V q).1 : ZMod (p^3))))
    (h₁₂ : J₂ ≤ J₁) (h₂ : 1 ≤ J₂)
    (hq : CoordinateBound J₁ J₂ q)
    (hb₁ : CoordinateBound J₁ J₂ base.1) (hb₂ : CoordinateBound J₁ J₂ base.2)
    (hS : ∀ e ∈ S, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2)
    (hword : ∀ e ∈ S, WordSolution (p^3) a₁ a₂ R V q e)
    (hred : ∀ e ∈ S, (pencil q base e).map (Int.castRingHom (ZMod p)) ≠ 0)
    (hderiv : ∀ e ∈ S, (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
      ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p))
        ((V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3)))) = 0)
    (hcap : (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3)
    (hlargeR : (10368*(3 : ℝ)^9)^5*M^35 < (p : ℝ)^4)
    (hlargeQ : (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ)) :
    let b : ℤ := ((V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))).val
    ∃ F : Finset ℤ[X], F.card ≤ 3 ∧
      (∀ f ∈ F, Irreducible f ∧ f.IsPrimitive ∧ f ∣ pencil q base e₀ ∧
        ((f.eval b : ℤ) : ZMod p) = 0 ∧ f.map (Int.castRingHom (ZMod p)) ≠ 0) ∧
      (∀ e ∈ S, ∃ f ∈ F, f ∣ pencil q base e) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let β := (V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))
  let b : ℤ := β.val
  let reduction := ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  have hb : (b : ZMod p) = reduction β := by
    have hh := congrArg reduction (ZMod.natCast_zmod_val β)
    simpa only [map_natCast, b, Int.cast_natCast] using hh
  have hu := original_singular_unit_observations a₁ a₂ ha₁ ha₂ R V q base hr ht hbase hx hy hk
  have hL : IsUnit ((((endpointL q base).eval b : ℤ) : ZMod p)) := by
    rw [← reduce_eval_at_lift reduction (endpointL q base) β b hb]
    exact hu.1.map reduction
  let row : Option {e // e ∈ S} → Endpoint := fun i => i.elim base Subtype.val
  let l := fun i => coeffL q (row i)
  let m := fun i => coeffM q (row i)
  let u := fun i => coeffQ (row i)
  let v := fun i => coeffR (row i)
  let w := fun i => coeffS (row i)
  have hfamily (e : {e // e ∈ S}) : PrimeCube.familyPolynomial l m u v w e =
      pencil q base e.val := rfl
  have hrow (i : Option {e // e ∈ S}) :
      CoordinateBound J₁ J₂ (row i).1 ∧ CoordinateBound J₁ J₂ (row i).2 := by
    cases i with
    | none => exact ⟨hb₁, hb₂⟩
    | some e => exact hS e.val e.property
  have hcoeffs (i : Option {e // e ∈ S}) :=
    actual_coefficient_bounds J₁ J₂ q (row i) hq (hrow i).1 (hrow i).2
  obtain ⟨F, hcard, hF, hcover⟩ := PrimeCube.actual_singular_factor_cover l m u v w
    (⟨e₀, he₀⟩ : {e // e ∈ S}) p b J₁ J₂ 3 18 M h₁₂ h₂ (by norm_num) (by norm_num)
    (fun i => (hcoeffs i).1) (fun i => (hcoeffs i).2.1)
    (by intro i; exact (hcoeffs i).2.2.1.trans (by nlinarith [sq_nonneg J₁]))
    (by
      intro i
      have hpos : 0 ≤ J₁*J₂ := mul_nonneg (by linarith) (by linarith)
      exact (hcoeffs i).2.2.2.1.trans (by nlinarith))
    (by intro i; exact (hcoeffs i).2.2.2.2.trans (by nlinarith [sq_nonneg J₂]))
    (by simpa only [l, m, row, coeffL, coeffM, endpointL, PrimeCube.linear,
      eval_add, eval_C, eval_mul, eval_X, Option.elim_none, mul_comm] using hL)
    (by intro e; simpa only [hfamily] using hred e.val e.property)
    (by intro e; simpa only [hfamily] using pencil_natDegree q base e.val)
    (by
      intro e
      rw [hfamily]
      exact actual_pencil_weighted_coeff J₁ J₂ q base e.val
        (h₂.trans h₁₂) h₂ hq hb₁ hb₂ (hS e.val e.property).1 (hS e.val e.property).2)
    (by
      intro e
      rw [hfamily]
      exact original_pencil_dvd hp a₁ a₂ ha₁ ha₂ R V q base e.val
        hr ht hbase (hword e.val e.property))
    (by
      intro e
      rw [hfamily]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      change (Int.castRingHom (ZMod p)) ((pencil q base e.val).derivative.eval b) = 0
      rw [← Polynomial.eval₂_at_apply]
      simp only [Int.coe_castRingHom, hb]
      exact hderiv e.val e.property)
    hcap hlargeR hlargeQ
  refine ⟨F, hcard, ?_, ?_⟩
  · intro f hf
    simpa only [hfamily] using hF f hf
  · intro e he
    simpa only [hfamily] using hcover (⟨e, he⟩ : {e // e ∈ S})

/-- Actual nonzero singular original pencils have a constructed cover by at most
three relevant factors. For each factor, the genuine algebraic integer value
pairs of the retained original endpoints satisfy a uniform subpower bound.
The coefficient and unit inputs belong to the original physical baseline;
neither factor heights nor a factor-count supplier is assumed. -/
theorem actual_singular_value_pairs_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (J₁ J₂ M : ℝ)
      (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
      (R V q : Coordinate) (base : Endpoint) (S : Finset Endpoint)
      (hr : IsUnit (R.1 : ZMod (p^3))) (ht : IsUnit (-(physical R V q).2 : ZMod (p^3))),
      16 ≤ (p : ℝ) → J₂ ≤ J₁ → 1 ≤ J₂ → 18*J₁^3 ≤ (p : ℝ)^2 →
      WordSolution (p^3) a₁ a₂ R V q base →
      IsUnit ((physical R V base.1).1 : ZMod (p^3)) →
      IsUnit ((physical R V base.2).1 : ZMod (p^3)) →
      IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical R V q).1 : ZMod (p^3))) →
      CoordinateBound J₁ J₂ q → CoordinateBound J₁ J₂ base.1 → CoordinateBound J₁ J₂ base.2 →
      (∀ e ∈ S, CoordinateBound J₁ J₂ e.1 ∧ CoordinateBound J₁ J₂ e.2) →
      (∀ e ∈ S, WordSolution (p^3) a₁ a₂ R V q e) →
      (∀ e ∈ S, (pencil q base e).map (Int.castRingHom (ZMod p)) ≠ 0) →
      (∀ e ∈ S, (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
        ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p))
          ((V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3)))) = 0) →
      (J₁*J₂)^5 ≤ M^5*(p : ℝ)^3 →
      (10368*(3 : ℝ)^9)^5*M^35 < (p : ℝ)^4 →
      (24*(8*(18 : ℝ))^4)^5*M^40 < (p : ℝ) →
      ∃ F : Finset ℤ[X], F.card ≤ 3 ∧
        (∀ f ∈ F, Irreducible f ∧ f.IsPrimitive ∧
          Irreducible (f.map (Int.castRingHom ℚ)) ∧ f.natDegree ≤ 3) ∧
        (∀ e ∈ S, ∃ f ∈ F, f ∣ pencil q base e) ∧
        (∀ f ∈ F, ∀ hfQ : Irreducible (f.map (Int.castRingHom ℚ)),
          letI : Fact (Irreducible (f.map (Int.castRingHom ℚ))) := ⟨hfQ⟩
          ((singularFactorValuePairs f q base S).card : ℝ) ≤ C*(p : ℝ)^ε) := by
  classical
  obtain ⟨C, hC, hcount⟩ := fixed_factor_value_pairs_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro p hp J₁ J₂ M a₁ a₂ ha₁ ha₂ R V q base S hr ht hp16 h₁₂ h₂ hheight
    hbase hx hy hk hq hb₁ hb₂ hS hword hred hderiv hcap hlargeR hlargeQ
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  by_cases hSempty : S = ∅
  · subst S
    exact ⟨∅, by simp, by simp, by simp, by simp⟩
  obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
  obtain ⟨F, hcard, hF, hcover⟩ := original_singular_cover p hp J₁ J₂ M a₁ a₂ ha₁ ha₂
    R V q base S e₀ he₀ hr ht hbase hx hy hk h₁₂ h₂ hq hb₁ hb₂ hS hword hred hderiv
    hcap hlargeR hlargeQ
  have h₁ : 1 ≤ J₁ := h₂.trans h₁₂
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hJ₁0 : 0 ≤ J₁ := by linarith
  have hJ₂0 : 0 ≤ J₂ := by linarith
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hJp : J₁ ≤ p := by
    have hcube : J₁^3 ≤ (p : ℝ)^3 :=
      (show J₁^3 ≤ (p : ℝ)^2 by nlinarith [pow_nonneg hJ₁0 3]).trans
        (pow_le_pow_right₀ hp1 (by decide : 2 ≤ 3))
    exact (pow_le_pow_iff_left₀ hJ₁0 hp0 (by decide : 3 ≠ 0)).mp hcube
  have hP₀ : pencil q base e₀ ≠ 0 := by
    intro hz
    simpa only [hz, Polynomial.map_zero, ne_eq, not_true_eq_false] using hred e₀ he₀
  have hPcoeff : ∀ j, |((pencil q base e₀).coeff j : ℝ)| ≤ (p : ℝ)^2 := by
    intro j
    by_cases hj : j ≤ (pencil q base e₀).natDegree
    · have hj3 := hj.trans (pencil_natDegree q base e₀)
      have hb := actual_pencil_weighted_coeff J₁ J₂ q base e₀ h₁ h₂ hq hb₁ hb₂
        (hS e₀ he₀).1 (hS e₀ he₀).2 j hj
      apply hb.trans
      calc
        _ ≤ 18*J₁^(3-j)*J₁^j := by gcongr
        _ = 18*J₁^3 := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hj3]
        _ ≤ _ := hheight
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp only [Int.cast_zero, abs_zero]
      positivity
  have hFd (f : ℤ[X]) (hf : f ∈ F) : f.natDegree ≤ 3 :=
    (natDegree_le_of_dvd (hF f hf).2.2.1 hP₀).trans (pencil_natDegree q base e₀)
  have hFQ (f : ℤ[X]) (hf : f ∈ F) : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hF f hf).2.1).mp
      (hF f hf).1
  refine ⟨F, hcard, (fun f hf => ⟨(hF f hf).1, (hF f hf).2.1, hFQ f hf, hFd f hf⟩),
    hcover, ?_⟩
  intro f hf hfQ
  letI : Fact (Irreducible (f.map (Int.castRingHom ℚ))) := ⟨hfQ⟩
  let β := (V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))
  let b : ℤ := β.val
  let reduction := ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  have hb : (b : ZMod p) = reduction β := by
    have hh := congrArg reduction (ZMod.natCast_zmod_val β)
    simpa only [map_natCast, b, Int.cast_natCast] using hh
  have hu := original_singular_unit_observations a₁ a₂ ha₁ ha₂ R V q base hr ht hbase hx hy hk
  have hQu : IsUnit ((((endpointQ base).eval b : ℤ) : ZMod p)) := by
    rw [← reduce_eval_at_lift reduction (endpointQ base) β b hb]
    exact hu.2.1.map reduction
  have hQZu : IsUnit
      ((((endpointQ base-endpointL q base*coordinateLinear q).eval b : ℤ) : ZMod p)) := by
    rw [← reduce_eval_at_lift reduction _ β b hb]
    exact hu.2.2.map reduction
  have hcoeff := factor_coeff_bound (p : ℝ) (by linarith) (pencil q base e₀) f hP₀
    (pencil_natDegree q base e₀) (hF f hf).2.2.1 hPcoeff
  have hc := actual_coefficient_bounds J₁ J₂ q base hq hb₁ hb₂
  have hJ13 : J₁ ≤ J₁^3 := by simpa using pow_le_pow_right₀ h₁ (by decide : 1 ≤ 3)
  have hJ23 : J₁^2 ≤ J₁^3 := pow_le_pow_right₀ h₁ (by decide : 2 ≤ 3)
  have hJJ : J₁*J₂ ≤ J₁^2 := by nlinarith
  have hJ₂sq : J₂^2 ≤ J₁^2 := pow_le_pow_left₀ hJ₂0 h₁₂ 2
  apply hcount p hp16 f (hF f hf).2.1 (hFd f hf) hcoeff b (hF f hf).2.2.2.1 q base S e₀
    he₀ (hF f hf).2.2.1 hQu hQZu
    (hc.1.trans (by nlinarith)) (hc.2.1.trans (by nlinarith))
    (hc.2.2.1.trans (by nlinarith)) (hc.2.2.2.1.trans (by nlinarith))
    (hc.2.2.2.2.trans (by nlinarith))
  intro e he z hz
  have hzbound : CoordinateBound J₁ J₂ z := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (hS e he).1
    · exact (hS e he).2
  exact ⟨hzbound.1.trans hJp, hzbound.2.trans (h₁₂.trans hJp)⟩

end
end D5.S3.Arith.CharacterSums.Original
