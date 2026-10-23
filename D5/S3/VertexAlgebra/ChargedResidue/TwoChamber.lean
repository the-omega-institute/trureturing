/- GID: D5/S3/VertexAlgebra/ChargedResidue/TwoChamber
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/TwoChamber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed coefficients of the two collision chambers. -/
import D5.S3.VertexAlgebra.ChargedResidue.QuadraticResidue

/-! All integer coefficient indices are extended by zero in negative degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open LatticeHalfFockChargedCollision PowerSeries
noncomputable section

def scalarSignedCoeff (f : PowerSeries ℂ) (k : ℤ) : ℂ :=
  if k < 0 then 0 else coeff k.toNat f

private theorem signed_add (f g : PowerSeries ℂ) (k : ℤ) :
    scalarSignedCoeff (f+g) k = scalarSignedCoeff f k + scalarSignedCoeff g k := by
  by_cases h : k < 0 <;> simp [scalarSignedCoeff, h]

private theorem signed_sub (f g : PowerSeries ℂ) (k : ℤ) :
    scalarSignedCoeff (f-g) k = scalarSignedCoeff f k - scalarSignedCoeff g k := by
  by_cases h : k < 0 <;> simp [scalarSignedCoeff, h]

private theorem signed_shift (f : PowerSeries ℂ) (k : ℤ) :
    scalarSignedCoeff (X*f) k = scalarSignedCoeff f (k-1) := by
  by_cases negative : k < 0
  · simp [scalarSignedCoeff, negative, show k-1 < 0 by omega]
  by_cases zero : k = 0
  · subst k
    simp [scalarSignedCoeff]
  have positive : 1 ≤ k := by omega
  have index : k.toNat = (k-1).toNat+1 := by omega
  simp only [scalarSignedCoeff, ite_eq_right negative,
    ite_eq_right (by omega : ¬ k-1 < 0), index]
  simpa using coeff_X_pow_mul f 1 (k-1).toNat

private theorem binomial_step (a : ℤ) :
    binomialSeries (R := ℤ) ℂ (a+1) = binomialSeries (R := ℤ) ℂ a * (1+X) := by
  rw [binomialSeries_add]
  congr 1
  simpa using (binomialSeries_nat (R := ℤ) (A := ℂ) 1)

def chamberSeries (a b : ℤ) : PowerSeries ℂ :=
  rescale (-1 : ℂ) (binomialSeries (R := ℤ) ℂ a) * binomialSeries (R := ℤ) ℂ b

def chamberDifference (a b v : ℤ) : ℂ :=
  scalarSignedCoeff (chamberSeries a b) v -
    (-1 : ℂ)^a * scalarSignedCoeff (chamberSeries a b) (a+b-v)

def localPoleCoefficient (a b v : ℤ) : ℂ :=
  scalarSignedCoeff (binomialSeries (R := ℤ) ℂ (v-a-b-1) *
    ((quadraticCoordinateUnit^b : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) (-a-1)

def localPoleTotal (a b v : ℤ) : ℂ :=
  localPoleCoefficient a b v + (-1 : ℂ)^v * localPoleCoefficient b a v

private theorem series_left_step (a b : ℤ) :
    chamberSeries (a+1) b = chamberSeries a b - X*chamberSeries a b := by
  unfold chamberSeries
  rw [binomial_step, map_mul, map_add]
  simp only [map_one, rescale_X, map_neg, map_one, neg_one_mul]
  ring

private theorem series_right_step (a b : ℤ) :
    chamberSeries a (b+1) = chamberSeries a b + X*chamberSeries a b := by
  unfold chamberSeries
  rw [binomial_step]
  ring

private theorem difference_left_step (a b v : ℤ) :
    chamberDifference (a+1) b v = chamberDifference a b v - chamberDifference a b (v-1) := by
  simp only [chamberDifference, series_left_step, signed_sub, signed_shift,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
  have i : a+1+b-v-1 = a+b-v := by omega
  have j : a+b-(v-1) = a+1+b-v := by omega
  rw [i, j]
  ring

private theorem difference_right_step (a b v : ℤ) :
    chamberDifference a (b+1) v = chamberDifference a b v + chamberDifference a b (v-1) := by
  simp only [chamberDifference, series_right_step, signed_add, signed_shift]
  have i : a+(b+1)-v-1 = a+b-v := by omega
  have j : a+b-(v-1) = a+(b+1)-v := by omega
  rw [i, j]
  ring

private theorem pole_left_step (a b v : ℤ) :
    localPoleCoefficient (a+1) b v =
      localPoleCoefficient a b v - localPoleCoefficient a b (v-1) := by
  let f := binomialSeries (R := ℤ) ℂ (v-a-b-2) *
    ((quadraticCoordinateUnit^b : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
  have shift : binomialSeries (R := ℤ) ℂ (v-a-b-1) =
      binomialSeries (R := ℤ) ℂ (v-a-b-2) * (1+X) := by
    simpa only [show v-a-b-2+1 = v-a-b-1 by omega] using binomial_step (v-a-b-2)
  unfold localPoleCoefficient
  rw [shift, ← signed_sub, show v-1-a-b-1 = v-a-b-2 by omega,
    show v-(a+1)-b-1 = v-a-b-2 by omega]
  have factor :
      binomialSeries (R := ℤ) ℂ (v-a-b-2) * (1+X) *
          ((quadraticCoordinateUnit^b : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) -
        binomialSeries (R := ℤ) ℂ (v-a-b-2) *
          ((quadraticCoordinateUnit^b : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = X*f := by
    dsimp [f]
    ring
  rw [factor, signed_shift]
  congr 1
  omega

private theorem pole_right_step (a b v : ℤ) :
    localPoleCoefficient a (b+1) v =
      localPoleCoefficient a b v + localPoleCoefficient a b (v-1) := by
  have unit_value : (quadraticCoordinateUnit : PowerSeries ℂ) = 2+X :=
    IsUnit.unit_spec _
  have shift : binomialSeries (R := ℤ) ℂ (v-a-b-1) =
      binomialSeries (R := ℤ) ℂ (v-a-b-2) * (1+X) := by
    simpa only [show v-a-b-2+1 = v-a-b-1 by omega] using binomial_step (v-a-b-2)
  unfold localPoleCoefficient
  rw [shift, ← signed_add, show v-1-a-b-1 = v-a-b-2 by omega,
    show v-a-(b+1)-1 = v-a-b-2 by omega, zpow_add, zpow_one, Units.val_mul, unit_value]
  congr 1
  ring

private theorem total_left_step (a b v : ℤ) :
    localPoleTotal (a+1) b v = localPoleTotal a b v - localPoleTotal a b (v-1) := by
  have sign : (-1 : ℂ)^(v-1) = -((-1 : ℂ)^v) := by
    rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
    simp only [div_eq_mul_inv, inv_neg, inv_one, mul_neg_one]
  simp only [localPoleTotal, pole_left_step, pole_right_step, sign]
  ring

private theorem total_right_step (a b v : ℤ) :
    localPoleTotal a (b+1) v = localPoleTotal a b v + localPoleTotal a b (v-1) := by
  have sign : (-1 : ℂ)^(v-1) = -((-1 : ℂ)^v) := by
    rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
    simp only [div_eq_mul_inv, inv_neg, inv_one, mul_neg_one]
  simp only [localPoleTotal, pole_left_step, pole_right_step, sign]
  ring

private theorem propagate (m : ℕ)
    (base : ∀ v : ℤ, chamberDifference (-(m : ℤ)) (-(m : ℤ)) v =
      localPoleTotal (-(m : ℤ)) (-(m : ℤ)) v) (i j : ℕ) (v : ℤ) :
    chamberDifference (-(m : ℤ)+i) (-(m : ℤ)+j) v =
      localPoleTotal (-(m : ℤ)+i) (-(m : ℤ)+j) v := by
  induction i generalizing j v with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    induction j generalizing v with
    | zero => simpa using base v
    | succ j ih =>
      push_cast
      rw [← add_assoc, difference_right_step, total_right_step, ih, ih]
  | succ i ih =>
    push_cast
    rw [← add_assoc, difference_left_step, total_left_step, ih, ih]

private theorem series_add_exponents (a b c d : ℤ) :
    chamberSeries (a+c) (b+d) = chamberSeries a b * chamberSeries c d := by
  simp only [chamberSeries, binomialSeries_add, map_mul]
  ring

private theorem symmetric_series (m : ℕ) :
    chamberSeries (-(m : ℤ)) (-(m : ℤ)) =
      ((invOneSubPow ℂ m : PowerSeries ℂ)).subst (X^2 : PowerSeries ℂ) := by
  have hh : HasSubst (X^2 : PowerSeries ℂ) := HasSubst.X_pow (by decide)
  have positive : chamberSeries (m : ℤ) (m : ℤ) = (1-X^2 : PowerSeries ℂ)^m := by
    simp only [chamberSeries, binomialSeries_nat, map_pow, map_add, map_one, rescale_X,
      map_neg, map_one, neg_one_mul]
    rw [← mul_pow]
    congr 1
    ring
  have lhs : chamberSeries (-(m : ℤ)) (-(m : ℤ)) * (1-X^2 : PowerSeries ℂ)^m = 1 := by
    rw [← positive, ← series_add_exponents]
    simp [chamberSeries]
  have rhs : ((invOneSubPow ℂ m : PowerSeries ℂ)).subst (X^2 : PowerSeries ℂ) *
      (1-X^2 : PowerSeries ℂ)^m = 1 := by
    have inverse : (invOneSubPow ℂ m : PowerSeries ℂ) * (1-X : PowerSeries ℂ)^m = 1 := by
      rw [← invOneSubPow_inv_eq_one_sub_pow]
      exact (invOneSubPow ℂ m).val_inv
    have mapped := congrArg (substAlgHom hh) inverse
    rw [map_mul, map_one, coe_substAlgHom, subst_pow hh, subst_sub hh, subst_X hh] at mapped
    have one : (1 : PowerSeries ℂ).subst (X^2 : PowerSeries ℂ) = 1 := by
      rw [← coe_substAlgHom hh, map_one]
    simpa only [one] using mapped
  have nonzero : (1-X^2 : PowerSeries ℂ)^m ≠ 0 := by
    apply pow_ne_zero
    intro h
    have h0 := congrArg constantCoeff h
    norm_num at h0
  exact mul_right_cancel₀ nonzero (lhs.trans rhs.symm)

private theorem symmetric_even (n : ℕ) (j : ℤ) :
    scalarSignedCoeff (chamberSeries (-((n+1 : ℕ) : ℤ)) (-((n+1 : ℕ) : ℤ))) (2*j) =
      if j < 0 then 0 else ((n+j.toNat).choose n : ℂ) := by
  rw [symmetric_series]
  by_cases negative : j < 0
  · simp [scalarSignedCoeff, negative, show 2*j < 0 by omega]
  · have idx : (2*j).toNat = 2*j.toNat := by omega
    simp only [scalarSignedCoeff, ite_eq_right (by omega : ¬ 2*j < 0),
      ite_eq_right negative, idx, coeff_subst_X_pow (by decide : 2 ≠ 0),
      dvd_mul_right, ite_true, Nat.mul_div_right, map_id, RingHom.id_apply]
    rw [invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk]
    have div : 2*j.toNat/2 = j.toNat := by omega
    rw [div]
    rfl

private theorem symmetric_odd (n : ℕ) (j : ℤ) :
    scalarSignedCoeff (chamberSeries (-((n+1 : ℕ) : ℤ)) (-((n+1 : ℕ) : ℤ))) (2*j+1) = 0 := by
  rw [symmetric_series]
  by_cases negative : 2*j+1 < 0
  · simp [scalarSignedCoeff, negative]
  · have notdiv : ¬ 2 ∣ (2*j+1).toNat := by omega
    simp [scalarSignedCoeff, negative, coeff_subst_X_pow (by decide : 2 ≠ 0), notdiv]

private theorem symmetric_poles (n : ℕ) (v : ℤ) :
    localPoleTotal (-((n+1 : ℕ) : ℤ)) (-((n+1 : ℕ) : ℤ)) v =
      ((1+(-1 : ℂ)^v)/2) * Ring.choose ((v : ℂ)/2+(n : ℂ)) n := by
  have jac := collision_scalar_coordinate (v+2*(n : ℤ)) 0 n
  have scalar : collisionScalar (v+2*(n : ℤ)) 0 n =
      Ring.choose ((v : ℂ)/2+(n : ℂ)) n := by
    simp only [collisionScalar, mul_zero, neg_zero, zpow_zero, Units.val_one, mul_one,
      binomialSeries_coeff, smul_eq_mul]
    congr 1
    push_cast
    ring
  rw [scalar] at jac
  have index : -(-((n+1 : ℕ) : ℤ))-1 = n := by omega
  have exponent : v-(-((n+1 : ℕ) : ℤ))-(-((n+1 : ℕ) : ℤ))-1 = v+2*n+1 := by omega
  have pole : localPoleCoefficient (-((n+1 : ℕ) : ℤ)) (-((n+1 : ℕ) : ℤ)) v =
      (1/2 : ℂ) * Ring.choose ((v : ℂ)/2+(n : ℂ)) n := by
    unfold localPoleCoefficient
    rw [index]
    simp only [scalarSignedCoeff, ite_eq_right (by omega : ¬ (n : ℤ) < 0), Int.toNat_natCast]
    rw [exponent]
    have power : -2*(0 : ℤ)-(n : ℤ)-1 = -((n+1 : ℕ) : ℤ) := by omega
    rw [power] at jac
    norm_num only [mul_zero, zero_add, zpow_one] at jac
    linear_combination -(1/2 : ℂ) * jac
  simp only [localPoleTotal, pole]
  ring

private theorem choose_negative_nat (k n : ℕ) :
    Ring.choose (-((k+1 : ℕ) : ℂ)) n = (-1 : ℂ)^n * ((k+n).choose n : ℂ) := by
  rw [Ring.choose_neg]
  have exponent : ((k+1 : ℕ) : ℂ)+(n : ℂ)-1 = ((k+n : ℕ) : ℂ) := by push_cast; ring
  rw [exponent, Ring.choose_natCast]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_negOnePow_natCast, smul_eq_mul]

private theorem symmetric_base (n : ℕ) (v : ℤ) :
    chamberDifference (-((n+1 : ℕ) : ℤ)) (-((n+1 : ℕ) : ℤ)) v =
      localPoleTotal (-((n+1 : ℕ) : ℤ)) (-((n+1 : ℕ) : ℤ)) v := by
  rw [symmetric_poles]
  obtain parity | parity := Int.emod_two_eq_zero_or_one v
  · let j := v/2
    have even : v = 2*j := by dsimp [j]; omega
    rw [even]
    have sign : (-1 : ℂ)^(2*j) = 1 := (even_two_mul j).neg_one_zpow
    rw [sign]
    norm_num only [one_add_one_eq_two, div_self (by norm_num : (2 : ℂ) ≠ 0), one_mul]
    have exponent : ((2*j : ℤ) : ℂ)/2+(n : ℂ) = ((j+(n : ℤ) : ℤ) : ℂ) := by push_cast; ring
    rw [exponent]
    unfold chamberDifference
    rw [symmetric_even, show -((n+1 : ℕ) : ℤ)+ -((n+1 : ℕ) : ℤ)-2*j =
      2*(-((n+1 : ℕ) : ℤ)-j) by omega, symmetric_even]
    by_cases positive : 0 ≤ j
    · have reverse : -((n+1 : ℕ) : ℤ)-j < 0 := by omega
      rw [ite_eq_right (by omega : ¬ j < 0), ite_eq_left reverse, mul_zero, sub_zero]
      have natural : j+(n : ℤ) = ((n+j.toNat : ℕ) : ℤ) := by omega
      rw [natural]
      norm_cast
      rw [Ring.choose_natCast]
    · have negative : j < 0 := by omega
      rw [ite_eq_left negative, zero_sub]
      by_cases middle : 0 ≤ j+(n : ℤ)
      · have reverse : -((n+1 : ℕ) : ℤ)-j < 0 := by omega
        rw [ite_eq_left reverse, mul_zero, neg_zero]
        have natural : j+(n : ℤ) = (((j+(n : ℤ)).toNat : ℕ) : ℤ) := by omega
        rw [natural]
        rw [Int.cast_natCast, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      · let k := (-((n+1 : ℕ) : ℤ)-j).toNat
        have reverse : ¬ -((n+1 : ℕ) : ℤ)-j < 0 := by omega
        rw [ite_eq_right reverse]
        have top : j+(n : ℤ) = -((k+1 : ℕ) : ℤ) := by dsimp [k]; omega
        rw [top]
        rw [Int.cast_neg, Int.cast_natCast, choose_negative_nat]
        have signn : -((-1 : ℂ)^(-((n+1 : ℕ) : ℤ))) = (-1 : ℂ)^n := by
          rw [zpow_neg, zpow_natCast, pow_succ, mul_neg_one]
          simp only [inv_neg, neg_neg]
          rw [← inv_pow]
          norm_num
        rw [← neg_mul, signn]
        congr 1
        rw [Nat.add_comm]
  · let j := v/2
    have odd : v = 2*j+1 := by dsimp [j]; omega
    rw [odd]
    have sign : (-1 : ℂ)^(2*j+1) = -1 := by
      rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), (even_two_mul j).neg_one_zpow]
      simp
    rw [sign]
    norm_num only [add_neg_cancel, zero_div, zero_mul]
    unfold chamberDifference
    rw [symmetric_odd, show -((n+1 : ℕ) : ℤ)+ -((n+1 : ℕ) : ℤ)-(2*j+1) =
      2*(-((n+1 : ℕ) : ℤ)-j-1)+1 by omega, symmetric_odd]
    ring

/- proof_shape: two_chamber_coefficient: content
   admission_basis: escape-witness
   escape_witness: Arbitrary integer chamber exponents are obtained from a
   common negative exponent by two finite recurrences. The negative base
   uses the quadratic Jacobian and signed binomial reflection, including the
   interval where both original coefficients vanish.
   literature_status: classical rational residue identity at the two poles. -/
theorem two_chamber_coefficient (a b v : ℤ) :
    chamberDifference a b v = localPoleTotal a b v := by
  let m := a.natAbs+b.natAbs+1
  have positive : 0 < m := by dsimp [m]; omega
  have lowera : -a ≤ ((-a).natAbs : ℤ) := Int.le_natAbs
  have lowerb : -b ≤ ((-b).natAbs : ℤ) := Int.le_natAbs
  rw [Int.natAbs_neg] at lowera lowerb
  have ia : -(m : ℤ)+((a+(m : ℤ)).toNat : ℤ) = a := by dsimp [m]; omega
  have ib : -(m : ℤ)+((b+(m : ℤ)).toNat : ℤ) = b := by dsimp [m]; omega
  have base : ∀ z : ℤ, chamberDifference (-(m : ℤ)) (-(m : ℤ)) z =
      localPoleTotal (-(m : ℤ)) (-(m : ℤ)) z := by
    intro z
    have value : m = (m-1)+1 := by omega
    rw [value]
    exact symmetric_base (m-1) z
  simpa only [ia, ib] using propagate m base (a+(m : ℤ)).toNat (b+(m : ℤ)).toNat v

private theorem pole_collision (q B v : ℤ) :
    localPoleCoefficient (q+B) (q-B) v =
      (1/2 : ℂ) * (2 : ℂ)^(-2*B) *
        (if -q-1-B < 0 then 0 else collisionScalar (v-2*q-2) B (-q-1-B).toNat) := by
  let degree := -q-1-B
  have index : -(q+B)-1 = degree := by dsimp [degree]; omega
  have exponent : v-(q+B)-(q-B)-1 = (v-2*q-2)+1 := by omega
  unfold localPoleCoefficient
  rw [index, exponent]
  change _ = (1/2 : ℂ) * (2 : ℂ)^(-2*B) *
    (if degree < 0 then 0 else collisionScalar (v-2*q-2) B degree.toNat)
  by_cases negative : degree < 0
  · simp only [scalarSignedCoeff, ite_eq_left negative, mul_zero]
  · simp only [scalarSignedCoeff, ite_eq_right negative]
    have coordinate := collision_scalar_coordinate (v-2*q-2) B degree.toNat
    have power : -2*B-(degree.toNat : ℤ)-1 = q-B := by dsimp [degree] at *; omega
    rw [power] at coordinate
    have factor : (1/2 : ℂ) * (2 : ℂ)^(-2*B) * (2 : ℂ)^(2*B+1) = 1 := by
      rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
        show -2*B+(2*B+1) = 1 by ring, zpow_one]
      norm_num
    change _ = (1/2 : ℂ) * (2 : ℂ)^(-2*B) * collisionScalar (v-2*q-2) B degree.toNat
    rw [coordinate, ← mul_assoc, factor, one_mul]

/- proof_shape: signed_two_chamber_scalar: content
   admission_basis: escape-witness
   escape_witness: The two-chamber rational residue identity is transported
   back through the actual quadratic collision coefficient change of variables.
   Each pole keeps its own negative-degree branch and its normalization.
   literature_status: classical two-pole residue identity. -/
theorem signed_two_chamber_scalar (q B v : ℤ) :
    chamberDifference (q+B) (q-B) v =
      (1/2 : ℂ) * (2 : ℂ)^(-2*B) *
        (if -q-1-B < 0 then 0 else collisionScalar (v-2*q-2) B (-q-1-B).toNat) +
      (-1 : ℂ)^v * (1/2 : ℂ) * (2 : ℂ)^(2*B) *
        (if -q-1+B < 0 then 0 else collisionScalar (v-2*q-2) (-B) (-q-1+B).toNat) := by
  rw [two_chamber_coefficient]
  unfold localPoleTotal
  rw [pole_collision q B v]
  have other := pole_collision q (-B) v
  simp only [sub_neg_eq_add, ← sub_eq_add_neg, mul_neg, neg_mul, neg_neg] at other
  rw [other]
  ring

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
