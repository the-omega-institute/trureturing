/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldPolynomialCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldPolynomialCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite polynomial recoupling and supported signed residue covariance. -/
import D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision

/-! Finite polynomial algebra only. The signed-binomial group law is reused
from SupportedChannelSeries, retaining its Carnahan attribution. The sector
consumer uses these identities on the original canonical Jacobi products. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldPolynomialCovariance
open UniformGradedLocalCorrelator SupportedChannelSeries
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section

private theorem plus_pow {T : Type*} [CommRing T] [Algebra ℂ T]
    (U V : T) (n : ℕ) :
    (U + V) ^ n = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℂ) • (U ^ j * V ^ (n - j)) := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]

private theorem minus_pow {T : Type*} [CommRing T] [Algebra ℂ T]
    (U V : T) (n : ℕ) :
    (U - V) ^ n = ∑ j ∈ Finset.range (n + 1),
      (((-1 : ℂ) ^ j) * (n.choose j : ℂ)) • (U ^ (n - j) * V ^ j) := by
  rw [show U - V = -V + U by ring, plus_pow]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [neg_pow]
  ring

private theorem old_expansion {T : Type*} [CommRing T] [Algebra ℂ T]
    (U V Z : T) (k A H B : ℕ) :
    U ^ A * (U - V - Z) ^ k * (U - Z) ^ k * V ^ k * (V + Z) ^ H * Z ^ B =
      ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
        (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
          ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) •
            (U ^ (A + 2 * k - p - q) * V ^ k * (V + Z) ^ (H + p) * Z ^ (B + q))) := by
  calc
    _ = U ^ A * ((U - (V + Z)) ^ k * (U - Z) ^ k) *
        V ^ k * (V + Z) ^ H * Z ^ B := by
      rw [show U - V - Z = U - (V + Z) by ring]
      ring
    _ = _ := by
      rw [minus_pow U (V + Z), minus_pow U Z, Finset.sum_mul_sum]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
      apply Finset.sum_congr rfl
      intro p hp
      have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
      apply Finset.sum_congr rfl
      intro q hq
      have hqk : q ≤ k := by simpa using Finset.mem_range.mp hq
      rw [show A + 2 * k - p - q = A + (k - p) + (k - q) by omega]
      simp only [pow_add, Algebra.smul_def]
      ring

private theorem new_expansion {T : Type*} [CommRing T] [Algebra ℂ T]
    (U V Z : T) (k A H B : ℕ) :
    U ^ A * (U - V - Z) ^ k * (U - Z) ^ k * V ^ k * (V + Z) ^ H * Z ^ B =
      ∑ p ∈ Finset.range (k + 1),
        (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
          (U ^ A * (U - Z) ^ (2 * k - p) * V ^ (k + p) * (V + Z) ^ H * Z ^ B) := by
  rw [show U - V - Z = (U - Z) - V by ring, minus_pow (U - Z) V]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
  rw [show 2 * k - p = (k - p) + k by omega]
  simp only [pow_add, Algebra.smul_def]
  ring

private theorem act_monomial {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (L K B : ℕ) (x b z : ℤ) :
    polynomialAction (variablePolynomial 0 ^ L * variablePolynomial 1 ^ K *
      variablePolynomial 2 ^ B) F ![x, b, z] =
      F ![x - L, b - K, z - B] := by
  have h : variablePolynomial 0 ^ L * variablePolynomial 1 ^ K *
      variablePolynomial 2 ^ B =
      AddMonoidAlgebra.single
        (L • Pi.single 0 1 + K • Pi.single 1 1 + B • Pi.single 2 1 : Exponent 3) 1 := by
    simp [variablePolynomial, AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.single_mul_single]
  rw [h, polynomialAction, AddMonoidAlgebra.lift_single]
  change (1 : ℂ) • F (![x, b, z] -
    (L • Pi.single 0 1 + K • Pi.single 1 1 + B • Pi.single 2 1)) = _
  rw [one_smul]
  congr 1
  funext i
  fin_cases i <;> simp [nsmul_eq_mul]

private theorem act_positive {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (L K H B : ℕ) (x b z : ℤ) :
    polynomialAction (variablePolynomial 0 ^ L * variablePolynomial 1 ^ K *
      (variablePolynomial 1 + variablePolynomial 2) ^ H * variablePolynomial 2 ^ B)
      F ![x, b, z] =
      ∑ h ∈ Finset.range (H + 1), (H.choose h : ℂ) •
        F ![x - L, b - K - h, z - B - H + h] := by
  rw [plus_pow]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro h hh
  have hhH : h ≤ H := by simpa using Finset.mem_range.mp hh
  apply congrArg (fun v : V => (H.choose h : ℂ) • v)
  have poly : (variablePolynomial (0 : Fin 3)) ^ L * variablePolynomial 1 ^ K *
      (variablePolynomial 1 ^ h * variablePolynomial 2 ^ (H - h)) *
      variablePolynomial 2 ^ B =
      variablePolynomial 0 ^ L * variablePolynomial 1 ^ (K + h) *
        variablePolynomial 2 ^ (B + H - h) := by
    rw [show B + H - h = B + (H - h) by omega]
    simp only [pow_add]
    ring
  rw [poly, act_monomial]
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add,
    Nat.cast_sub (show h ≤ B + H by omega)] <;> omega

private theorem act_cross {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (A M K H B : ℕ) (x b z : ℤ) :
    polynomialAction (variablePolynomial 0 ^ A *
      (variablePolynomial 0 - variablePolynomial 2) ^ M * variablePolynomial 1 ^ K *
      (variablePolynomial 1 + variablePolynomial 2) ^ H * variablePolynomial 2 ^ B)
      F ![x, b, z] =
      ∑ h ∈ Finset.range (H + 1), (H.choose h : ℂ) •
        clear M (fun s t => F ![s - A, b - K - h, t - (B + H - h : ℕ)]) x z := by
  rw [minus_pow]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply]
  have terms (q : ℕ) (hq : q ∈ Finset.range (M + 1)) :
      polynomialAction (variablePolynomial 0 ^ A *
        (variablePolynomial 0 ^ (M - q) * variablePolynomial 2 ^ q) *
        variablePolynomial 1 ^ K * (variablePolynomial 1 + variablePolynomial 2) ^ H *
        variablePolynomial 2 ^ B) F ![x, b, z] =
      ∑ h ∈ Finset.range (H + 1), (H.choose h : ℂ) •
        F ![x - A - M + q, b - K - h, z - (B + H - h : ℕ) - q] := by
    have hqM : q ≤ M := by simpa using Finset.mem_range.mp hq
    have poly : (variablePolynomial (0 : Fin 3)) ^ A *
        (variablePolynomial 0 ^ (M - q) * variablePolynomial 2 ^ q) *
        variablePolynomial 1 ^ K * (variablePolynomial 1 + variablePolynomial 2) ^ H *
        variablePolynomial 2 ^ B =
        variablePolynomial 0 ^ (A + M - q) * variablePolynomial 1 ^ K *
          (variablePolynomial 1 + variablePolynomial 2) ^ H * variablePolynomial 2 ^ (B + q) := by
      rw [show A + M - q = A + (M - q) by omega]
      simp only [pow_add]
      ring
    rw [poly, act_positive]
    apply Finset.sum_congr rfl
    intro h hh
    have hhH : h ≤ H := by simpa using Finset.mem_range.mp hh
    apply congrArg (fun v : V => (H.choose h : ℂ) • v)
    congr 1
    funext i
    fin_cases i <;> simp [Nat.cast_add, Nat.cast_sub hqM,
      Nat.cast_sub (show q ≤ A + M by omega), Nat.cast_sub (show h ≤ B + H by omega)] <;> omega
  calc
    _ = ∑ q ∈ Finset.range (M + 1),
        (((-1 : ℂ) ^ q) * (M.choose q : ℂ)) •
          (∑ h ∈ Finset.range (H + 1), (H.choose h : ℂ) •
            F ![x - A - M + q, b - K - h, z - (B + H - h : ℕ) - q]) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [terms q hq]
    _ = _ := by
      simp only [clear, Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro q hq
      simp only [smul_smul]
      have hx : x - A - M + q = x - M + q - A := by omega
      have hz : z - (B + H - h : ℕ) - q = z - q - (B + H - h : ℕ) := by omega
      rw [hx, hz]
      congr 1
      ring

/-- The two literal finite expansions of the full old inner multiplier agree.
This is an identity for arbitrary signed distributions, with no support premise.
It is the missing regrouping from p,q,h to p,h and a (z0-z)^(2k-p) factor. -/
theorem finite_inner_recoupling {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (k : ℕ) (a : Fin 3 → ℕ) (x b z : ℤ) :
    (∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
      (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
        ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) •
          (∑ h ∈ Finset.range (a 1 + p + 1), ((a 1 + p).choose h : ℂ) •
            F ![x - a 0 - 2 * k + p + q, b - k - h,
              z - (a 2 + q) - (a 1 + p) + h]))) =
    ∑ p ∈ Finset.range (k + 1), ∑ h ∈ Finset.range (a 1 + 1),
      (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
        (((a 1).choose h : ℂ) •
          clear (2 * k - p)
            (fun s t => F ![s - a 0, b - k - p - h, t - (a 2 + a 1 - h : ℕ)]) x z) := by
  classical
  let U : LaurentPolynomial 3 := variablePolynomial 0
  let Y : LaurentPolynomial 3 := variablePolynomial 1
  let Z : LaurentPolynomial 3 := variablePolynomial 2
  let q := U ^ a 0 * (U - Y - Z) ^ k * (U - Z) ^ k * Y ^ k * (Y + Z) ^ a 1 * Z ^ a 2
  have old := congrArg (fun r : LaurentPolynomial 3 => polynomialAction r F ![x, b, z])
    (old_expansion U Y Z k (a 0) (a 1) (a 2))
  have new := congrArg (fun r : LaurentPolynomial 3 => polynomialAction r F ![x, b, z])
    (new_expansion U Y Z k (a 0) (a 1) (a 2))
  change polynomialAction q F ![x, b, z] = _ at old new
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply] at old new
  have old' : polynomialAction q F ![x, b, z] =
      ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
        (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
          ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) •
            (∑ h ∈ Finset.range (a 1 + p + 1), ((a 1 + p).choose h : ℂ) •
              F ![x - a 0 - 2 * k + p + q, b - k - h,
                z - (a 2 + q) - (a 1 + p) + h])) := by
    rw [old]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p ≤ k := by simpa using Finset.mem_range.mp hp
    apply Finset.sum_congr rfl
    intro q hq
    have hq' : q ≤ k := by simpa using Finset.mem_range.mp hq
    dsimp only [U, Y, Z]
    rw [act_positive]
    apply congrArg (fun v : V => (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
      ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) • v))
    apply Finset.sum_congr rfl
    intro h hh
    apply congrArg (fun v : V => ((a 1 + p).choose h : ℂ) • v)
    congr 1
    funext i
    fin_cases i <;> simp [Nat.cast_add,
      Nat.cast_sub (show p ≤ a 0 + 2 * k by omega),
      Nat.cast_sub (show q ≤ a 0 + 2 * k - p by omega)] <;> omega
  rw [← old', new]
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only [U, Y, Z]
  rw [act_cross, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun v : V => (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) • v)
  apply congrArg (fun v : V => ((a 1).choose h : ℂ) • v)
  apply congrArg (fun G : ℤ → ℤ → V => clear (2 * k - p) G x z)
  funext s t
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add] <;> omega


end
end D5.S3.VertexAlgebra.ThreeFieldPolynomialCovariance
