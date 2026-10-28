/- GID: D5/S3/VertexAlgebra/FormalSeries/FourFieldMiddlePolynomial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/FourFieldMiddlePolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite spectator recombination for the middle four-field collision. -/
import D5.S3.VertexAlgebra.FormalSeries.FourFieldInnerPolynomial
import D5.S3.VertexAlgebra.Sectors.LatticeSectorChannelTransport
import Batteries.Tactic.OpenPrivate

/-! Finite Laurent convolution on arbitrary signed distributions. No raw
series substitution occurs. The helpers are used by the actual middle channel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.FourFieldMiddlePolynomial
open UniformGradedLocalCorrelator SupportedChannelSeries FourFieldInnerPolynomial
open LatticeSectorChannelTransport
open scoped BigOperators
noncomputable section
open private minus_pow plus_pow from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldPolynomialCovariance
open private act_monomial from
  D5.S3.VertexAlgebra.FormalSeries.FourFieldInnerPolynomial

private theorem five_expansion {T : Type*} [CommRing T] [Algebra ℂ T]
    (U V Z Y : T) (k A H B C : ℕ) :
    U ^ A * V ^ H * Z ^ B * Y ^ C *
      (U - V) ^ k * (U - Z) ^ k * (U - Y) ^ k *
      (V - Y) ^ k * (Z - Y) ^ k =
    ∑ p ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k + 1),
    ∑ s ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    ∑ l ∈ Finset.range (k + 1),
      weight k p • (weight k r • (weight k s • (weight k j • (weight k l •
        (U ^ (A + (k - p) + (k - r) + (k - s)) *
         V ^ (H + p + (k - j)) * Z ^ (B + r + (k - l)) * Y ^ (C + s + j + l)))))) := by
  have reorder : U ^ A * V ^ H * Z ^ B * Y ^ C *
      (U - V) ^ k * (U - Z) ^ k * (U - Y) ^ k *
      (V - Y) ^ k * (Z - Y) ^ k =
      U ^ A * V ^ H * Z ^ B * Y ^ C * (Z - Y) ^ k *
        (V - Y) ^ k * (U - Y) ^ k * (U - Z) ^ k * (U - V) ^ k := by ring
  rw [reorder, minus_pow Z Y, minus_pow V Y, minus_pow U Y,
    minus_pow U Z, minus_pow U V]
  simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  simp only [weight, pow_add, Algebra.smul_def]
  ring

/-- The literal multiplier in output coordinates x,b,z,y. -/
def middlePolynomial (k : ℕ) (a : Fin 4 → ℕ) : LaurentPolynomial 4 :=
  variablePolynomial 0 ^ a 0 * (variablePolynomial 1 + variablePolynomial 2) ^ a 1 *
  variablePolynomial 2 ^ a 2 * variablePolynomial 3 ^ a 3 *
  (variablePolynomial 0 - variablePolynomial 1 - variablePolynomial 2) ^ k *
  (variablePolynomial 0 - variablePolynomial 2) ^ k *
  (variablePolynomial 0 - variablePolynomial 3) ^ k * variablePolynomial 1 ^ k *
  (variablePolynomial 1 + variablePolynomial 2 - variablePolynomial 3) ^ k *
  (variablePolynomial 2 - variablePolynomial 3) ^ k

/-- Three spectator fibers followed by the original balanced clearing. -/
def middleClearing {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (a : Fin 4 → ℕ) (F : Distribution 4 V) (e : Exponent 4) : V :=
  ∑ p ∈ Finset.range (k + 1), ∑ r ∈ Finset.range (k + 1),
  ∑ s ∈ Finset.range (k + 1),
    weight k p • (weight k r • (weight k s •
      (∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
        weight k j • (weight k l •
          clearIterate k (a 1 + p + k - j) (a 2 + r + k - l)
            (fun b z => F ![e 0 - a 0 - 3 * k + p + r + s, b, z,
              e 3 - a 3 - s - j - l]) (e 1) (e 2)))))

private theorem positive_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 4 V) (L k H B C : ℕ) (e : Exponent 4) :
    polynomialAction (variablePolynomial 0 ^ L * variablePolynomial 1 ^ k *
      variablePolynomial 2 ^ B * (variablePolynomial 1 + variablePolynomial 2) ^ H *
      variablePolynomial 3 ^ C) F e =
    clearIterate k H B (fun b z => F ![e 0 - L,b,z,e 3 - C]) (e 1) (e 2) := by
  rw [plus_pow]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  unfold clearIterate
  apply Finset.sum_congr rfl
  intro h hh
  have hhH : h ≤ H := by simpa using Finset.mem_range.mp hh
  have poly : variablePolynomial (0 : Fin 4) ^ L * variablePolynomial 1 ^ k *
      variablePolynomial 2 ^ B *
      (variablePolynomial 1 ^ h * variablePolynomial 2 ^ (H - h)) * variablePolynomial 3 ^ C =
      variablePolynomial 0 ^ L * variablePolynomial 1 ^ (k + h) *
        variablePolynomial 2 ^ (B + H - h) * variablePolynomial 3 ^ C := by
    rw [show B + H - h = B + (H - h) by omega]
    simp only [pow_add]
    ring
  rw [poly, act_monomial]
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add, Nat.cast_sub (show h ≤ B + H by omega)] <;> omega

theorem middle_action_expansion {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (a : Fin 4 → ℕ) (F : Distribution 4 V) (e : Exponent 4) :
    polynomialAction (middlePolynomial k a) F e = middleClearing k a F e := by
  let U : LaurentPolynomial 4 := variablePolynomial 0
  let V0 : LaurentPolynomial 4 := variablePolynomial 1
  let Z : LaurentPolynomial 4 := variablePolynomial 2
  let Y : LaurentPolynomial 4 := variablePolynomial 3
  have poly : middlePolynomial k a =
      (U ^ a 0 * (V0 + Z) ^ a 1 * Z ^ a 2 * Y ^ a 3 *
      (U - (V0 + Z)) ^ k * (U - Z) ^ k * (U - Y) ^ k *
      (V0 + Z - Y) ^ k * (Z - Y) ^ k) * V0 ^ k := by
    dsimp only [middlePolynomial,U,V0,Z,Y]
    rw [show variablePolynomial (0 : Fin 4) - variablePolynomial 1 - variablePolynomial 2 =
      variablePolynomial 0 - (variablePolynomial 1 + variablePolynomial 2) by ring]
    ring
  rw [poly, five_expansion]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply]
  unfold middleClearing
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ≤ k := by simpa using Finset.mem_range.mp hp
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r ≤ k := by simpa using Finset.mem_range.mp hr
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ k := by simpa using Finset.mem_range.mp hs
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  have reorder : U ^ (a 0 + (k-p) + (k-r) + (k-s)) *
      (V0+Z) ^ (a 1+p+(k-j)) * Z ^ (a 2+r+(k-l)) * Y ^ (a 3+s+j+l) * V0^k =
      U ^ (a 0 + (k-p) + (k-r) + (k-s)) * V0^k * Z ^ (a 2+r+(k-l)) *
        (V0+Z) ^ (a 1+p+(k-j)) * Y ^ (a 3+s+j+l) := by ring
  rw [reorder]
  dsimp only [U,V0,Z,Y]
  rw [positive_action]
  have hj' : j ≤ k := by simpa using Finset.mem_range.mp hj
  have hl' : l ≤ k := by simpa using Finset.mem_range.mp hl
  simp only [show a 1+p+(k-j)=a 1+p+k-j by omega,
    show a 2+r+(k-l)=a 2+r+k-l by omega]
  congr 5
  apply Finset.sum_congr rfl
  intro h hh
  dsimp only
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add, Nat.cast_sub hp', Nat.cast_sub hr', Nat.cast_sub hs'] <;> omega

/-- All pair factors except the v,t factor, with original labels fixed. -/
def middleCross {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 4 V) (x v t y : ℤ) : V :=
  ∑ p ∈ Finset.range (k+1), ∑ r ∈ Finset.range (k+1),
  ∑ s ∈ Finset.range (k+1), ∑ j ∈ Finset.range (k+1), ∑ l ∈ Finset.range (k+1),
    weight k p • (weight k r • (weight k s • (weight k j • (weight k l •
      F ![x-3*k+p+r+s,v-p-k+j,t-r-k+l,y-s-j-l]))))

private def crossPolynomial (k : ℕ) : LaurentPolynomial 4 :=
  pairPolynomial 0 1 ^ k * pairPolynomial 0 2 ^ k * pairPolynomial 0 3 ^ k *
    pairPolynomial 1 3 ^ k * pairPolynomial 2 3 ^ k

private theorem cross_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 4 V) (e : Exponent 4) :
    polynomialAction (crossPolynomial k) F e = middleCross k F (e 0) (e 1) (e 2) (e 3) := by
  have poly : crossPolynomial k =
      variablePolynomial 0 ^ 0 * variablePolynomial 1 ^ 0 * variablePolynomial 2 ^ 0 *
      variablePolynomial 3 ^ 0 * (variablePolynomial 0 - variablePolynomial 1)^k *
      (variablePolynomial 0 - variablePolynomial 2)^k * (variablePolynomial 0 - variablePolynomial 3)^k *
      (variablePolynomial 1 - variablePolynomial 3)^k * (variablePolynomial 2 - variablePolynomial 3)^k := by
    simp only [pow_zero,one_mul,crossPolynomial,pairPolynomial]
  rw [poly,five_expansion]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply]
  unfold middleCross
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ≤ k := by simpa using Finset.mem_range.mp hp
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r ≤ k := by simpa using Finset.mem_range.mp hr
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ k := by simpa using Finset.mem_range.mp hs
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ k := by simpa using Finset.mem_range.mp hj
  apply Finset.sum_congr rfl
  intro l hl
  have hl' : l ≤ k := by simpa using Finset.mem_range.mp hl
  rw [act_monomial]
  congr 6
  funext i
  fin_cases i <;> simp [Nat.cast_add,Nat.cast_sub hp',Nat.cast_sub hr',Nat.cast_sub hs',
    Nat.cast_sub hj',Nat.cast_sub hl'] <;> omega

private theorem middle_pair_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 4 V) (e : Exponent 4) :
    polynomialAction (pairPolynomial 1 2 ^ k) F e =
      clear k (fun v t => F ![e 0,v,t,e 3]) (e 1) (e 2) := by
  rw [pairPolynomial,minus_pow]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply]
  unfold clear
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ k := by simpa using Finset.mem_range.mp hj
  have mon : variablePolynomial (1 : Fin 4) ^ (k-j) * variablePolynomial 2 ^ j =
      variablePolynomial 0 ^ 0 * variablePolynomial 1 ^ (k-j) * variablePolynomial 2 ^ j *
        variablePolynomial 3 ^ 0 := by simp
  rw [mon,act_monomial]
  congr 2
  funext i
  fin_cases i <;> simp [Nat.cast_sub hj'] <;> omega

theorem clearing_four_middle {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 4 V) (e : Exponent 4) :
    polynomialAction (clearingPolynomial 4 k) F e =
      clear k (fun v t => middleCross k F (e 0) v t (e 3)) (e 1) (e 2) := by
  classical
  have pairs : labelledPairs 4 = {(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)} := by
    ext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> decide
  have poly : clearingPolynomial 4 k = pairPolynomial 1 2 ^ k * crossPolynomial k := by
    simp [clearingPolynomial,pairs,crossPolynomial,mul_comm,mul_left_comm,mul_assoc]
  rw [poly,map_mul,Module.End.mul_apply,middle_pair_action]
  unfold clear
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  rw [cross_action]
  rfl

end
end D5.S3.VertexAlgebra.FourFieldMiddlePolynomial
