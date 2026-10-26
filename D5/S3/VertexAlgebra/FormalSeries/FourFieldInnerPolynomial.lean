/- GID: D5/S3/VertexAlgebra/FormalSeries/FourFieldInnerPolynomial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/FourFieldInnerPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal four-field clearing and its five finite cross-factor fibers. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldPolynomialCovariance
import Batteries.Tactic.OpenPrivate

/-! Finite Laurent polynomial identities for arbitrary signed distributions.
The five binomial fibers expand the untouched spectator pair and its four
cross factors. No substitution on a raw distribution is defined or used.
proof_shape: inner_action_expansion, clearing_four: bind-only
These polynomial helpers are consumed by the actual four-field inner transport.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.FourFieldInnerPolynomial
open UniformGradedLocalCorrelator SupportedChannelSeries
open scoped BigOperators
noncomputable section
open private plus_pow minus_pow from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldPolynomialCovariance

/-- A finite binomial weight. -/
def weight (k i : ℕ) : ℂ := (-1 : ℂ) ^ i * (k.choose i : ℂ)

private theorem five_expansion {T : Type*} [CommRing T] [Algebra ℂ T]
    (U V S Z : T) (k A B H C : ℕ) :
    U ^ A * V ^ B * S ^ H * Z ^ C *
      (U - V) ^ k * (U - S) ^ k * (U - Z) ^ k *
      (V - S) ^ k * (V - Z) ^ k =
    ∑ s ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k + 1),
    ∑ q ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (k + 1),
    ∑ h ∈ Finset.range (k + 1),
      weight k h • (weight k p • (weight k q • (weight k r • (weight k s •
        (U ^ (A + (k - h) + (k - p) + (k - q)) *
         V ^ (B + h + (k - r) + (k - s)) *
         S ^ (H + p + r) * Z ^ (C + q + s)))))) := by
  rw [minus_pow U V, minus_pow U S, minus_pow U Z,
    minus_pow V S, minus_pow V Z]
  simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro h hh
  simp only [weight, pow_add, Algebra.smul_def]
  ring

private theorem act_monomial {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 4 V) (L M H B : ℕ) (e : Exponent 4) :
    polynomialAction (variablePolynomial 0 ^ L * variablePolynomial 1 ^ M *
      variablePolynomial 2 ^ H * variablePolynomial 3 ^ B) F e =
      F ![e 0 - L, e 1 - M, e 2 - H, e 3 - B] := by
  have h : variablePolynomial 0 ^ L * variablePolynomial 1 ^ M *
      variablePolynomial 2 ^ H * variablePolynomial 3 ^ B =
      AddMonoidAlgebra.single
        (L • Pi.single 0 1 + M • Pi.single 1 1 +
          H • Pi.single 2 1 + B • Pi.single 3 1 : Exponent 4) 1 := by
    simp [variablePolynomial, AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.single_mul_single]
  rw [h, polynomialAction, AddMonoidAlgebra.lift_single]
  change (1 : ℂ) • F (e - _) = _
  rw [one_smul]
  congr 1
  funext i
  fin_cases i <;> simp [nsmul_eq_mul]

private theorem act_positive {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 4 V) (L M K A B : ℕ) (e : Exponent 4) :
    polynomialAction (variablePolynomial 0 ^ L * variablePolynomial 1 ^ M *
      variablePolynomial 2 ^ K * (variablePolynomial 2 + variablePolynomial 3) ^ A *
      variablePolynomial 3 ^ B) F e =
    ∑ j ∈ Finset.range (A + 1), (A.choose j : ℂ) •
      F ![e 0 - L, e 1 - M, e 2 - K - j, e 3 - B - A + j] := by
  rw [plus_pow]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hjA : j ≤ A := by simpa using Finset.mem_range.mp hj
  apply congrArg (fun v : V => (A.choose j : ℂ) • v)
  have poly : (variablePolynomial (0 : Fin 4)) ^ L * variablePolynomial 1 ^ M *
      variablePolynomial 2 ^ K *
      (variablePolynomial 2 ^ j * variablePolynomial 3 ^ (A - j)) *
      variablePolynomial 3 ^ B =
      variablePolynomial 0 ^ L * variablePolynomial 1 ^ M *
      variablePolynomial 2 ^ (K + j) * variablePolynomial 3 ^ (B + A - j) := by
    rw [show B + A - j = B + (A - j) by omega]
    simp only [pow_add]
    ring
  rw [poly, act_monomial]
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add, Nat.cast_sub (show j ≤ B + A by omega)] <;> omega

/-- The literal full multiplier in native x,y,b,z coordinates. -/
def innerPolynomial (k : ℕ) (a : Fin 4 → ℕ) : LaurentPolynomial 4 :=
  variablePolynomial 0 ^ a 0 * variablePolynomial 1 ^ a 1 *
  (variablePolynomial 2 + variablePolynomial 3) ^ a 2 * variablePolynomial 3 ^ a 3 *
  (variablePolynomial 0 - variablePolynomial 1) ^ k *
  (variablePolynomial 0 - variablePolynomial 2 - variablePolynomial 3) ^ k *
  (variablePolynomial 0 - variablePolynomial 3) ^ k *
  (variablePolynomial 1 - variablePolynomial 2 - variablePolynomial 3) ^ k *
  (variablePolynomial 1 - variablePolynomial 3) ^ k * variablePolynomial 2 ^ k

/-- Finite clearing, defined directly from coefficient shifts. -/
def finiteClearing {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (a : Fin 4 → ℕ) (F : Distribution 4 V) (e : Exponent 4) : V :=
  ∑ s ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k + 1),
  ∑ q ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (k + 1),
  ∑ h ∈ Finset.range (k + 1),
    weight k h • (weight k p • (weight k q • (weight k r • (weight k s •
      (∑ j ∈ Finset.range (a 2 + p + r + 1), ((a 2 + p + r).choose j : ℂ) •
        F ![e 0 - a 0 - 3 * k + h + p + q,
          e 1 - a 1 - 2 * k - h + r + s,
          e 2 - k - j, e 3 - (a 3 + q + s) - (a 2 + p + r) + j])))))

/-- Finite cross expansion of the literal multiplier; all signed exponents
are permitted and no support or iterate identity is a premise. -/
theorem inner_action_expansion {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (a : Fin 4 → ℕ) (F : Distribution 4 V) (e : Exponent 4) :
    polynomialAction (innerPolynomial k a) F e = finiteClearing k a F e := by
  let U : LaurentPolynomial 4 := variablePolynomial 0
  let Y : LaurentPolynomial 4 := variablePolynomial 1
  let T : LaurentPolynomial 4 := variablePolynomial 2
  let Z : LaurentPolynomial 4 := variablePolynomial 3
  have poly : innerPolynomial k a =
      (U ^ a 0 * Y ^ a 1 * (T + Z) ^ a 2 * Z ^ a 3 *
        (U - Y) ^ k * (U - (T + Z)) ^ k * (U - Z) ^ k *
        (Y - (T + Z)) ^ k * (Y - Z) ^ k) * T ^ k := by
    dsimp only [innerPolynomial, U, Y, T, Z]
    rw [show variablePolynomial (0 : Fin 4) - variablePolynomial 2 - variablePolynomial 3 =
      variablePolynomial 0 - (variablePolynomial 2 + variablePolynomial 3) by ring,
      show variablePolynomial (1 : Fin 4) - variablePolynomial 2 - variablePolynomial 3 =
      variablePolynomial 1 - (variablePolynomial 2 + variablePolynomial 3) by ring]
  rw [poly, five_expansion]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply]
  unfold finiteClearing
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ k := by simpa using Finset.mem_range.mp hs
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r ≤ k := by simpa using Finset.mem_range.mp hr
  apply Finset.sum_congr rfl
  intro q hq
  have hq' : q ≤ k := by simpa using Finset.mem_range.mp hq
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ≤ k := by simpa using Finset.mem_range.mp hp
  apply Finset.sum_congr rfl
  intro h hh
  have hh' : h ≤ k := by simpa using Finset.mem_range.mp hh
  apply congrArg (fun v => weight k h • (weight k p • (weight k q •
    (weight k r • (weight k s • v)))))
  have reorder : U ^ (a 0 + (k - h) + (k - p) + (k - q)) *
      Y ^ (a 1 + h + (k - r) + (k - s)) * (T + Z) ^ (a 2 + p + r) *
      Z ^ (a 3 + q + s) * T ^ k =
      U ^ (a 0 + (k - h) + (k - p) + (k - q)) *
      Y ^ (a 1 + h + (k - r) + (k - s)) * T ^ k *
      (T + Z) ^ (a 2 + p + r) * Z ^ (a 3 + q + s) := by ring
  rw [reorder]
  dsimp only [U, Y, T, Z]
  rw [act_positive]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add, Nat.cast_sub hh', Nat.cast_sub hp',
    Nat.cast_sub hq', Nat.cast_sub hr', Nat.cast_sub hs'] <;> omega

/-- The five original cross factors, with all labels still in original
x,y,t-position,q-position coordinates. -/
def crossPolynomial (k : ℕ) : LaurentPolynomial 4 :=
  pairPolynomial 0 1 ^ k * pairPolynomial 0 2 ^ k * pairPolynomial 0 3 ^ k *
    pairPolynomial 1 2 ^ k * pairPolynomial 1 3 ^ k

/-- The finite five-index cross convolution in the original coordinates. -/
def cross {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 4 V) (x y t z : ℤ) : V :=
  ∑ s ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k + 1),
  ∑ q ∈ Finset.range (k + 1), ∑ p ∈ Finset.range (k + 1),
  ∑ h ∈ Finset.range (k + 1),
    weight k h • (weight k p • (weight k q • (weight k r • (weight k s •
      F ![x - 3 * k + h + p + q, y - 2 * k - h + r + s,
        t - p - r, z - q - s]))))

private theorem cross_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 4 V) (e : Exponent 4) :
    polynomialAction (crossPolynomial k) F e = cross k F (e 0) (e 1) (e 2) (e 3) := by
  have poly : crossPolynomial k =
      variablePolynomial 0 ^ 0 * variablePolynomial 1 ^ 0 *
      variablePolynomial 2 ^ 0 * variablePolynomial 3 ^ 0 *
      (variablePolynomial 0 - variablePolynomial 1) ^ k *
      (variablePolynomial 0 - variablePolynomial 2) ^ k *
      (variablePolynomial 0 - variablePolynomial 3) ^ k *
      (variablePolynomial 1 - variablePolynomial 2) ^ k *
      (variablePolynomial 1 - variablePolynomial 3) ^ k := by
    simp only [pow_zero, one_mul, crossPolynomial, pairPolynomial]
  rw [poly, five_expansion]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  unfold cross
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ k := by simpa using Finset.mem_range.mp hs
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r ≤ k := by simpa using Finset.mem_range.mp hr
  apply Finset.sum_congr rfl
  intro q hq
  have hq' : q ≤ k := by simpa using Finset.mem_range.mp hq
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ≤ k := by simpa using Finset.mem_range.mp hp
  apply Finset.sum_congr rfl
  intro h hh
  have hh' : h ≤ k := by simpa using Finset.mem_range.mp hh
  rw [act_monomial]
  congr 6
  funext i
  fin_cases i <;> simp [Nat.cast_add, Nat.cast_sub hh', Nat.cast_sub hp',
    Nat.cast_sub hq', Nat.cast_sub hr', Nat.cast_sub hs'] <;> omega

private theorem last_pair_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 4 V) (e : Exponent 4) :
    polynomialAction (pairPolynomial 2 3 ^ k) F e =
      clear k (fun x y => F ![e 0, e 1, x, y]) (e 2) (e 3) := by
  rw [pairPolynomial, minus_pow]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  unfold clear
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ k := by simpa using Finset.mem_range.mp hj
  have mon : (variablePolynomial (2 : Fin 4)) ^ (k - j) * variablePolynomial 3 ^ j =
      variablePolynomial 0 ^ 0 * variablePolynomial 1 ^ 0 *
        variablePolynomial 2 ^ (k - j) * variablePolynomial 3 ^ j := by simp
  rw [mon, act_monomial]
  congr 2
  funext i
  fin_cases i <;> simp [Nat.cast_sub hj'] <;> omega

/-- All six pair localities are retained: only the inner t,q factor is
cleared after the five finite cross factors. -/
theorem clearing_four {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 4 V) (e : Exponent 4) :
    polynomialAction (clearingPolynomial 4 k) F e =
      clear k (cross k F (e 0) (e 1)) (e 2) (e 3) := by
  classical
  have pairs : labelledPairs 4 =
      {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by
    ext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> decide
  have poly : clearingPolynomial 4 k = pairPolynomial 2 3 ^ k * crossPolynomial k := by
    simp [clearingPolynomial, pairs, crossPolynomial, mul_comm, mul_left_comm, mul_assoc]
  rw [poly, map_mul, Module.End.mul_apply, last_pair_action]
  unfold clear
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  rw [cross_action]
  rfl

end
end D5.S3.VertexAlgebra.FourFieldInnerPolynomial
