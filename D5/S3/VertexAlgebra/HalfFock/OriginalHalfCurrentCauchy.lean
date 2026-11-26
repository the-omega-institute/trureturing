/- GID: D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentCauchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chamber expansion and the regular half-current coordinate correction. -/

import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Substitution

/-! Ordinary bivariate coefficients computed in the chamber with the second
variable expanded first. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy

open OriginalHalfCurrentTransport (unitPower chamberCoefficient chamber_coefficient_eq_contraction
  contractionScalar)
open PowerSeries

private abbrev Outer := LaurentSeries ℂ
private abbrev Chamber := PowerSeries Outer
private def liftOuter : PowerSeries ℂ →+* Outer := HahnSeries.ofPowerSeries ℤ ℂ
private def inner : PowerSeries ℂ →+* Chamber := PowerSeries.map (HahnSeries.C (Γ := ℤ))
private def outer : PowerSeries ℂ →+* Chamber := PowerSeries.C.comp liftOuter
private def u : Outer := HahnSeries.single 1 1
private def U : Chamber := C u
private def I : Chamber := C u⁻¹
private abbrev V : Chamber := X

private theorem u_ne : u ≠ 0 := by simp [u]

private theorem U_mul_I : U * I = 1 := by
  rw [U, I, ← map_mul, mul_inv_cancel₀ u_ne, map_one]

private theorem unitPower_add (eta a b : ℂ) :
    unitPower eta (a+b) = unitPower eta a * unitPower eta b := by
  simp only [unitPower, binomialSeries_add, map_mul]

private theorem unitPower_zero (eta : ℂ) : unitPower eta 0 = 1 := by
  simp [unitPower]

private theorem unitPower_one (eta : ℂ) :
    unitPower eta 1 = 1 - C eta * X := by
  have he : (1 : ℂ) = ((1:ℕ):ℂ) := by norm_num
  rw [unitPower, he, binomialSeries_nat]
  simp [map_add, rescale_X, sub_eq_add_neg, neg_mul]

private def e (eta : ℂ) : Chamber := C (HahnSeries.C eta)
private def b (eta : ℂ) : Chamber := outer (unitPower eta (1/2))
private def c (eta : ℂ) : Chamber := inner (unitPower eta (1/2))
private def bi (eta : ℂ) : Chamber := outer (unitPower eta (-1/2))
private def ci (eta : ℂ) : Chamber := inner (unitPower eta (-1/2))

private theorem root_laws (eta : ℂ) :
    b eta ^ 2 = 1-e eta*U ∧ c eta ^ 2 = 1-e eta*V ∧
      b eta * bi eta = 1 ∧ c eta * ci eta = 1 := by
  have hsq : unitPower eta ((1:ℂ)/2) ^ 2 = 1 - C eta * X := by
    rw [pow_two, ← unitPower_add, show (1:ℂ)/2+1/2=1 by ring, unitPower_one]
  have hi : unitPower eta ((1:ℂ)/2) * unitPower eta (-1/2) = 1 := by
    rw [← unitPower_add, show (1:ℂ)/2+(-1/2)=0 by ring, unitPower_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmul : outer (C eta * X) = e eta * U := by
      rw [map_mul]
      congr 1
      · exact congrArg C (HahnSeries.ofPowerSeries_C eta)
      · exact congrArg C HahnSeries.ofPowerSeries_X
    rw [b, ← map_pow, hsq, map_sub, map_one, hmul]
  · simpa [c, e, inner] using congrArg inner hsq
  · simpa only [b, bi, map_mul, map_one] using congrArg outer hi
  · simpa only [c, ci, map_mul, map_one] using congrArg inner hi

private def half : Outer := (2:Outer)⁻¹

private def geometricCauchy : Chamber :=
  C half * (1+X) * (invOneSubPow Outer 2 : Chamber)

private theorem geometric_relation :
    (1-X)^2 * geometricCauchy = C half * (1+X) := by
  have h := (invOneSubPow Outer 2).inv_mul
  change (invOneSubPow Outer 2).inv * (invOneSubPow Outer 2 : Chamber) = 1 at h
  rw [invOneSubPow_inv_eq_one_sub_pow] at h
  unfold geometricCauchy
  rw [show (1-X)^2 * (C half * (1+X) * (invOneSubPow Outer 2 : Chamber)) =
      (C half * (1+X)) * ((1-X)^2 * (invOneSubPow Outer 2 : Chamber)) by ring, h, mul_one]

private theorem geometric_coefficient (n : ℕ) :
    coeff n geometricCauchy = (n:Outer)+half := by
  rw [geometricCauchy, mul_assoc, coeff_C_mul, add_mul, map_add, one_mul,
    invOneSubPow_val_succ_eq_mk_add_choose]
  cases n with
  | zero => simp [half]
  | succ n =>
    have hx : coeff (n+1) (X * mk (fun k => ((1+k).choose 1 : Outer))) =
        ((1+n).choose 1 : Outer) := by
      rw [mul_comm, ← pow_one (X : Chamber), coeff_mul_X_pow, coeff_mk]
    rw [hx, coeff_mk, Nat.choose_one_right, Nat.choose_one_right]
    push_cast
    unfold half
    have h2 : (2:Outer) ≠ 0 := by
      intro hz
      have hc := congrArg (fun s : Outer => s.coeff 0) hz
      change (HahnSeries.single (0:ℤ) (2:ℂ)).coeff 0 = (0:Outer).coeff 0 at hc
      simp [HahnSeries.coeff_single] at hc
    have ht : (2:Outer)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
    linear_combination ((n:Outer)+1) * ht

private def ratio (eta : ℂ) : Chamber := V * (I * b eta^2 * ci eta^2)
private def plainRatio : Chamber := V * I

private theorem substRelation (z : Chamber) (h : HasSubst z) :
    (1-z)^2 * geometricCauchy.subst z = C half * (1+z) := by
  let f : Chamber →ₐ[Outer] Chamber := substAlgHom h
  have hx : f X = z := by
    rw [show f X = subst z X from congrFun (coe_substAlgHom h) X, subst_X h]
  have hc : f (C half) = C half := by
    rw [C_eq_algebraMap, AlgHom.commutes]
  have he := congrArg f geometric_relation
  simpa only [map_mul, map_pow, map_add, map_sub, map_one, hx, hc,
    show f geometricCauchy = geometricCauchy.subst z from
      congrFun (coe_substAlgHom h) geometricCauchy] using he

private def plain : Chamber := I * geometricCauchy.subst plainRatio
private def dressed (eta : ℂ) : Chamber :=
  I * bi eta * ci eta^3 * geometricCauchy.subst (ratio eta)

private theorem clear_plain :
    (U-V)^2*plain = C half*(U+V) := by
  have h := substRelation plainRatio (HasSubst.X'.mul_left)
  have hal : U-V = U*(1-plainRatio) := by
    rw [plainRatio]
    linear_combination V * U_mul_I
  rw [hal, plain]
  calc
    _ = U * (U*I) * ((1-plainRatio)^2 * geometricCauchy.subst plainRatio) := by ring
    _ = _ := by
      rw [U_mul_I, mul_one, h, plainRatio]
      linear_combination C half * V * U_mul_I

private theorem clear_dressed (eta : ℂ) :
    (U-V)^2*dressed eta = C half*(U*c eta*bi eta + V*b eta*ci eta) := by
  obtain ⟨hb, hc, hbi, hci⟩ := root_laws eta
  have h := substRelation (ratio eta) (HasSubst.X'.mul_left)
  have hal : U-V = U*c eta^2*(1-ratio eta) := by
    unfold ratio
    have hci2 : c eta^2*ci eta^2 = 1 := by rw [← mul_pow, hci, one_pow]
    calc
      _ = U*c eta^2-V*b eta^2 := by rw [hb, hc]; ring
      _ = U*c eta^2 - (U*I)*(c eta^2*ci eta^2)*V*b eta^2 := by
        rw [U_mul_I, hci2]; ring
      _ = _ := by ring
  calc
    _ = (U*I)*(c eta*ci eta)^3*(U*c eta*bi eta) *
        ((1-ratio eta)^2 * geometricCauchy.subst (ratio eta)) := by rw [hal, dressed]; ring
    _ = U*c eta*bi eta*(C half*(1+ratio eta)) := by rw [U_mul_I, hci, one_pow, one_mul, one_mul, h]
    _ = C half*(U*c eta*bi eta + (U*I)*(b eta*bi eta)*(c eta*ci eta)*V*b eta*ci eta) := by
      unfold ratio
      ring
    _ = _ := by rw [U_mul_I, hbi, hci]; ring

private theorem unitPower_constant (eta a : ℂ) : constantCoeff (unitPower eta a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [unitPower]

private theorem outerRoot_coeffZero (eta : ℂ) :
    (liftOuter (unitPower eta (1/2))).coeff 0 = 1 := by
  change ((unitPower eta (1/2) : PowerSeries ℂ) : LaurentSeries ℂ).coeff (↑(0:ℕ)) = 1
  rw [LaurentSeries.coeff_coe_powerSeries, coeff_zero_eq_constantCoeff_apply, unitPower_constant]

private def sumRootInverse (eta : ℂ) : Chamber :=
  invOfUnit (b eta + c eta)
    (Units.mk0 (liftOuter (unitPower eta (1/2)) + 1) (by
      intro h
      have he := congrArg (fun f : Outer => f.coeff 0) h
      change (liftOuter (unitPower eta (1/2)) + 1).coeff 0 = (0:Outer).coeff 0 at he
      rw [HahnSeries.coeff_add, outerRoot_coeffZero, HahnSeries.coeff_zero,
        HahnSeries.coeff_one, if_pos rfl] at he
      norm_num at he))

private theorem sumRootInverse_mul (eta : ℂ) :
    (b eta+c eta)*sumRootInverse eta = 1 := by
  unfold sumRootInverse
  apply mul_invOfUnit
  change constantCoeff (b eta + c eta) = liftOuter (unitPower eta (1/2)) + 1
  rw [map_add]
  congr 1
  rw [c, inner, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
    unitPower_constant, map_one]

/-- The normalized regular expression in the Laurent chamber. Its factors
are the two binomial roots with constant coefficient one, their inverses,
and the inverse of their sum squared. -/
def regularSeries (eta : ℂ) : PowerSeries (LaurentSeries ℂ) :=
  e eta * C half * (1+b eta*c eta) * bi eta * ci eta * sumRootInverse eta^2

private theorem correction_is_regular (eta : ℂ) :
    dressed eta - plain = regularSeries eta := by
  obtain ⟨hb, hc, hbi, hci⟩ := root_laws eta
  have hs := sumRootInverse_mul eta
  have h1 : (c eta-b eta)*(b eta+c eta) = e eta*(U-V) := by
    linear_combination hc-hb
  have h2 : (U*c eta-V*b eta)*(b eta+c eta) = (U-V)*(1+b eta*c eta) := by
    linear_combination U*hc - V*hb
  have hu : U-V ≠ 0 := by
    intro h
    have hc0 := congrArg PowerSeries.constantCoeff h
    have : u = 0 := by simpa [U] using hc0
    exact u_ne this
  apply mul_left_cancel₀ (pow_ne_zero 2 hu)
  rw [mul_sub, clear_plain, clear_dressed]
  calc
    _ = C half * bi eta * ci eta *
        ((c eta-b eta)*(U*c eta-V*b eta)) := by
      linear_combination C half * (((U+V)*(c eta*ci eta)-V*b eta*ci eta) * hbi +
        (U+V-U*c eta*bi eta) * hci)
    _ = C half * bi eta * ci eta *
        ((c eta-b eta)*(b eta+c eta) * ((U*c eta-V*b eta)*(b eta+c eta))) *
          sumRootInverse eta^2 := by
      rw [show C half * bi eta * ci eta *
          ((c eta-b eta)*(b eta+c eta) * ((U*c eta-V*b eta)*(b eta+c eta))) *
            sumRootInverse eta^2 =
          C half * bi eta * ci eta *
            ((c eta-b eta)*(U*c eta-V*b eta)) *
              (((b eta+c eta)*sumRootInverse eta)^2) by ring, hs, one_pow, mul_one]
    _ = _ := by rw [h1,h2,regularSeries]; ring


private theorem coeff_mul_subst (H G A : Chamber) (q : ℕ) :
    coeff q (H * G.subst (V*A)) =
      ∑ n ∈ Finset.range (q+1), coeff n G * coeff q (H*(V*A)^n) := by
  have hz : HasSubst (V*A) := HasSubst.X'.mul_left
  have powerCoeffZero (i n : ℕ) (h : i < n) : coeff i ((V*A)^n) = 0 := by
    rw [mul_pow, mul_comm, coeff_mul_X_pow', if_neg (by omega)]
  have hsubst (j : ℕ) (hj : j ≤ q) :
      coeff j (G.subst (V*A)) =
        ∑ n ∈ Finset.range (q+1), coeff n G * coeff j ((V*A)^n) := by
    rw [coeff_subst' hz]
    simp only [smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro n hn
    apply Finset.mem_range.mpr
    by_contra! h
    apply hn
    dsimp only
    rw [powerCoeffZero j n (by omega), mul_zero]
  rw [coeff_mul]
  calc
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal q, ∑ n ∈ Finset.range (q+1),
        coeff n G * (coeff ij.1 H * coeff ij.2 ((V*A)^n)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hj : ij.1 + ij.2 = q := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [hsubst ij.2 (by omega), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, ← coeff_mul]

private theorem unitPower_nat_mul (eta a : ℂ) (n : ℕ) :
    unitPower eta (a*(n:ℂ)) = unitPower eta a ^ n := by
  induction n with
  | zero => simp [unitPower_zero]
  | succ n ih =>
    rw [Nat.cast_succ, mul_add, mul_one, unitPower_add, ih, pow_succ]

private theorem dressed_term (eta : ℂ) (n : ℕ) :
    (I * bi eta * ci eta^3) * ratio eta^n =
      C (u ^ (-(n:ℤ)-1) * liftOuter (unitPower eta ((n:ℂ)-1/2))) *
        (inner (unitPower eta (-(n:ℂ)-3/2)) * X^n) := by
  have houter : bi eta * (b eta^2)^n = outer (unitPower eta ((n:ℂ)-1/2)) := by
    rw [b, bi, ← map_pow, ← map_pow, ← unitPower_nat_mul, ← unitPower_nat_mul,
      ← map_mul, ← unitPower_add]
    congr 2
    push_cast
    ring
  have hinner : ci eta^3 * (ci eta^2)^n = inner (unitPower eta (-(n:ℂ)-3/2)) := by
    simp only [ci, ← map_pow, ← unitPower_nat_mul, ← map_mul, ← unitPower_add]
    congr 2
    push_cast
    ring
  have hI : I * I^n = C (u^(-(n:ℤ)-1)) := by
    rw [I, ← map_pow, ← map_mul]
    congr 1
    rw [← zpow_neg_one, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ u_ne]
    congr 1
    ring
  rw [ratio, show (I * bi eta * ci eta^3) * (V*(I*b eta^2*ci eta^2))^n =
      (I*I^n) * (bi eta*(b eta^2)^n) * ((ci eta^3*(ci eta^2)^n)*X^n) by
        simp only [mul_pow]
        ring, houter, hinner, hI, outer, RingHom.comp_apply, ← map_mul]

private theorem coeff_dressed_term (eta : ℂ) (n p q : ℕ) (hn : n ≤ q) :
    ((coeff n geometricCauchy) * coeff q ((I*bi eta*ci eta^3)*ratio eta^n)).coeff (p:ℤ) =
      ((n:ℂ)+1/2) * coeff (p+n+1) (unitPower eta ((n:ℂ)-1/2)) *
        coeff (q-n) (unitPower eta (-(n:ℂ)-3/2)) := by
  rw [dressed_term, coeff_C_mul, coeff_mul_X_pow', if_pos hn, inner, coeff_map,
    geometric_coefficient]
  have hC : (n:Outer)+half = HahnSeries.C ((n:ℂ)+1/2) := by
    rw [map_add, map_natCast, div_eq_mul_inv, one_mul, map_inv₀, map_ofNat]
    rfl
  have hp : (p:ℤ) - (-(n:ℤ)-1) = ((p+n+1:ℕ):ℤ) := by omega
  rw [hC, show u^(-(n:ℤ)-1) = HahnSeries.single (-(n:ℤ)-1) (1:ℂ) by
    exact (RatFunc.single_zpow _).symm]
  rw [← mul_assoc (HahnSeries.C _), mul_comm (HahnSeries.C _), mul_assoc,
    ← map_mul, mul_assoc (HahnSeries.single _ _), HahnSeries.coeff_single_mul, one_mul, hp]
  rw [HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero]
  change ((unitPower eta ((n:ℂ)-1/2) : PowerSeries ℂ) : LaurentSeries ℂ).coeff
    (↑(p+n+1:ℕ)) * _ = _
  rw [LaurentSeries.coeff_coe_powerSeries]
  ring

private theorem dressed_coefficient (eta : ℂ) (p q : ℕ) :
    (coeff q (dressed eta)).coeff (p:ℤ) = chamberCoefficient eta p q := by
  rw [dressed, ratio, coeff_mul_subst]
  change (HahnSeries.coeff.addMonoidHom (p:ℤ)) _ = _
  rw [map_sum]
  unfold chamberCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  exact coeff_dressed_term eta n p q (by simpa using hn)

private theorem plain_coefficient (p q : ℕ) : (coeff q plain).coeff (p:ℤ) = 0 := by
  rw [plain, plainRatio, coeff_mul_subst]
  have hterm (n : ℕ) :
      coeff q (I * (V*I)^n) = if q = n then u^(-(n:ℤ)-1) else 0 := by
    rw [mul_pow, show I*(V^n*I^n) = (I*I^n)*X^n by ring, I,
      ← map_pow, ← map_mul, coeff_C_mul_X_pow]
    congr 1
    rw [← zpow_neg_one, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ u_ne]
    congr 1
    ring
  simp_rw [hterm]
  rw [Finset.sum_eq_single_of_mem q (by simp)]
  · rw [if_pos rfl, geometric_coefficient]
    have hC : (q:Outer)+half = HahnSeries.C ((q:ℂ)+1/2) := by
      rw [map_add, map_natCast, div_eq_mul_inv, one_mul, map_inv₀, map_ofNat]
      rfl
    rw [hC, show u^(-(q:ℤ)-1) = HahnSeries.single (-(q:ℤ)-1) (1:ℂ) by
      exact (RatFunc.single_zpow _).symm]
    rw [HahnSeries.coeff_mul_single]
    simp [HahnSeries.C, HahnSeries.coeff_single, show (p:ℤ)-(-(q:ℤ)-1) ≠ 0 by omega]
  · intro n _ hn
    simp [Ne.symm hn]

/-- The ordinary coefficient of the regular Cauchy expression is the
finite binomial contraction for every pair of frequencies. -/
theorem regular_series_coefficient (eta : ℂ) (p q : ℕ) :
    (PowerSeries.coeff q (regularSeries eta)).coeff (p:ℤ) =
      eta^(p+q+1) * contractionScalar p q := by
  rw [← correction_is_regular, map_sub, HahnSeries.coeff_sub, dressed_coefficient,
    plain_coefficient, sub_zero, chamber_coefficient_eq_contraction]

end D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentCauchy
