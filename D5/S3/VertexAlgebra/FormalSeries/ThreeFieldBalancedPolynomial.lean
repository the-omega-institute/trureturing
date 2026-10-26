/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldBalancedPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal balanced clearing and supported cancellation in s,z,x order. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerPolynomial
import Batteries.Tactic.OpenPrivate

/-! Cancellation uses the actual first cutoff and each fixed-first second cutoff. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldBalancedPolynomial
open UniformGradedLocalCorrelator SupportedChannelSeries SupportedFinalRInjectivity
open scoped BigOperators
noncomputable section
open private variable_xyz variable_preserves variable_zero nested_add nested_sub
  power_preserves power_zero positive_row_zero from
  D5.S3.VertexAlgebra.FormalSeries.SupportedFinalRInjectivity
open private difference_row_zero yz_difference_zero from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldInnerPolynomial

def balancedPolynomial (k : ℕ) (a : Fin 3 → ℕ) : LaurentPolynomial 3 :=
  (variablePolynomial 0 + variablePolynomial 1) ^ a 0 * variablePolynomial 1 ^ a 1 *
    variablePolynomial 2 ^ a 2 * variablePolynomial 0 ^ k *
    (variablePolynomial 0 + variablePolynomial 1 - variablePolynomial 2) ^ k *
    (variablePolynomial 1 - variablePolynomial 2) ^ k

def balancedRotate {V : Type*} (F : Distribution 3 V) : Distribution 3 V :=
  fun e => F ![e 0, e 2, e 1]

private def swapExponent : Exponent 3 →+ Exponent 3 where
  toFun e := ![e 0, e 2, e 1]
  map_zero' := by
    funext i
    fin_cases i <;> rfl
  map_add' e d := by
    funext i
    fin_cases i <;> rfl

private def swapPolynomial : LaurentPolynomial 3 →ₐ[ℂ] LaurentPolynomial 3 :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ swapExponent

private theorem balancedRotate_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : LaurentPolynomial 3) (F : Distribution 3 V) :
    polynomialAction (swapPolynomial p) (balancedRotate F) =
      balancedRotate (polynomialAction p F) := by
  induction p using AddMonoidAlgebra.induction_on with
  | of e =>
    change polynomialAction (swapPolynomial (AddMonoidAlgebra.single e 1)) _ =
      balancedRotate (polynomialAction (AddMonoidAlgebra.single e 1) F)
    simp only [swapPolynomial, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single, polynomialAction, AddMonoidAlgebra.lift_single]
    funext d
    change (1 : ℂ) • F ![(d - swapExponent e) 0, (d - swapExponent e) 2,
      (d - swapExponent e) 1] = (1 : ℂ) • F (![d 0, d 2, d 1] - e)
    congr 2
    funext i
    fin_cases i <;> simp [swapExponent]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
    rfl
  | smul r p hp =>
    simp only [map_smul, LinearMap.smul_apply, hp]
    rfl

/-- The multiplier in coefficient order [s,z,x]. -/
def balancedRotatedPolynomial (k : ℕ) (a : Fin 3 → ℕ) : LaurentPolynomial 3 :=
  (variablePolynomial 2 + variablePolynomial 0) ^ a 0 * variablePolynomial 2 ^ a 1 *
    variablePolynomial 1 ^ a 2 * variablePolynomial 0 ^ k *
    (variablePolynomial 0 + variablePolynomial 2 - variablePolynomial 1) ^ k *
    (variablePolynomial 2 - variablePolynomial 1) ^ k

private theorem swap_balanced (k : ℕ) (a : Fin 3 → ℕ) :
    swapPolynomial (balancedPolynomial k a) = balancedRotatedPolynomial k a := by
  have cv (i : Fin 3) : swapPolynomial (variablePolynomial i) =
      variablePolynomial (![0, 2, 1] i) := by
    simp only [swapPolynomial, variablePolynomial, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single]
    congr 1
    funext j
    fin_cases i <;> fin_cases j <;> simp [swapExponent]
  simp only [balancedPolynomial, balancedRotatedPolynomial, map_mul, map_pow, map_sub, map_add, cv]
  dsimp
  rw [add_comm (variablePolynomial 0) (variablePolynomial 2)]

theorem balanced_action_rotate {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (a : Fin 3 → ℕ) (F : Distribution 3 V) :
    polynomialAction (balancedRotatedPolynomial k a) (balancedRotate F) =
      balancedRotate (polynomialAction (balancedPolynomial k a) F) := by
  rw [← swap_balanced]
  exact balancedRotate_action _ F

open private plus_pow minus_pow act_monomial from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldPolynomialCovariance

private theorem clearing_expansion {T : Type*} [CommRing T] [Algebra ℂ T]
    (X Y Z : T) (k A B C : ℕ) :
    (X + Y) ^ A * Y ^ B * Z ^ C * X ^ k * (X + Y - Z) ^ k * (Y - Z) ^ k =
    ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
      (((-1 : ℂ) ^ j) * (k.choose j : ℂ)) •
        ((((-1 : ℂ) ^ l) * (k.choose l : ℂ)) •
          (X ^ k * Y ^ (B + k - l) * (X + Y) ^ (A + k - j) * Z ^ (C + j + l))) := by
  rw [mul_assoc ((X + Y) ^ A * Y ^ B * Z ^ C * X ^ k),
    minus_pow (X + Y) Z, minus_pow Y Z, Finset.sum_mul_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simpa using Finset.mem_range.mp hj
  apply Finset.sum_congr rfl
  intro l hl
  have hlk : l ≤ k := by simpa using Finset.mem_range.mp hl
  rw [show B + k - l = B + (k - l) by omega,
    show A + k - j = A + (k - j) by omega]
  simp only [pow_add, Algebra.smul_def]
  ring

private theorem positive_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (k B H C : ℕ) (s x z : ℤ) :
    polynomialAction (variablePolynomial 0 ^ k * variablePolynomial 1 ^ B *
      (variablePolynomial 0 + variablePolynomial 1) ^ H * variablePolynomial 2 ^ C)
      F ![s, x, z] =
    ∑ h ∈ Finset.range (H + 1), (H.choose h : ℂ) •
      F ![s - k - h, x - B - H + h, z - C] := by
  rw [plus_pow]
  simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro h hh
  have hhH : h ≤ H := by simpa using Finset.mem_range.mp hh
  have poly : variablePolynomial (0 : Fin 3) ^ k * variablePolynomial 1 ^ B *
      (variablePolynomial 0 ^ h * variablePolynomial 1 ^ (H - h)) *
      variablePolynomial 2 ^ C =
      variablePolynomial 0 ^ (k + h) * variablePolynomial 1 ^ (B + H - h) *
        variablePolynomial 2 ^ C := by
    rw [show B + H - h = B + (H - h) by omega]
    simp only [pow_add]
    ring
  rw [poly, act_monomial]
  congr 2
  funext i
  fin_cases i <;> simp [Nat.cast_add, Nat.cast_sub (show h ≤ B + H by omega)] <;> omega

/-- The literal balanced multiplier gives exactly the finite clearing sum. -/
theorem balanced_action_expansion {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : Distribution 3 V) (k : ℕ) (a : Fin 3 → ℕ) (s x z : ℤ) :
    polynomialAction (balancedPolynomial k a) F ![s, x, z] =
    ∑ j ∈ Finset.range (k + 1), ∑ l ∈ Finset.range (k + 1),
      (((-1 : ℂ) ^ j) * (k.choose j : ℂ)) •
        ((((-1 : ℂ) ^ l) * (k.choose l : ℂ)) •
          (∑ h ∈ Finset.range (a 0 + k - j + 1), ((a 0 + k - j).choose h : ℂ) •
            F ![s - k - h,
              x - (a 1 + k - l : ℕ) - (a 0 + k - j : ℕ) + h,
              z - a 2 - j - l])) := by
  rw [balancedPolynomial, clearing_expansion]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  rw [positive_action]
  congr 2
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add] <;> omega

variable {R : Type*} [CommRing R] [Algebra ℂ R]

private theorem triple_difference_zero (F : Distribution 3 R) (hF : NestedSupport F)
    (hz : polynomialAction
      (variablePolynomial 0 + variablePolynomial 2 - variablePolynomial 1) F = 0) :
    F = 0 := by
  obtain ⟨U, hu⟩ := hF.1
  have rows : ∀ n : ℕ, ∀ x z : ℤ, F ![(n : ℤ) - U, z, x] = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have prev (x z : ℤ) : F ![(n : ℤ) - U - 1, z, x] = 0 := by
        by_cases hn : n = 0
        · apply hu
          omega
        · have hp := ih (n - 1) (by omega) x z
          have eq : ((n - 1 : ℕ) : ℤ) - U = (n : ℤ) - U - 1 := by omega
          simpa only [eq] using hp
      obtain ⟨B, hb⟩ := hF.2 ((n : ℤ) - U)
      apply difference_row_zero (fun x z => F ![(n : ℤ) - U, z, x]) B
        (fun x z h => hb z x h)
      intro x z
      have h := congrFun hz ![(n : ℤ) - U, z, x]
      simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply,
        Pi.sub_apply, Pi.add_apply, variable_xyz] at h
      simp only [Fin.isValue, reduceIte, zero_add, prev] at h
      simpa [clear, Finset.sum_range_succ, sub_eq_add_neg] using h
  funext e
  change F e = 0
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  by_cases hx : 0 ≤ e 0 + U
  · have h := rows (e 0 + U).toNat (e 2) (e 1)
    have nx : ((e 0 + U).toNat : ℤ) - U = e 0 := by
      rw [Int.toNat_of_nonneg hx]
      omega
    simpa only [nx, ee] using h
  · simpa only [ee] using hu (e 0) (e 1) (e 2) (by omega)

private theorem xz_positive_zero {R : Type*} [CommRing R] [Algebra ℂ R]
    (F : Distribution 3 R) (hF : NestedSupport F)
    (hz : polynomialAction (variablePolynomial 2 + variablePolynomial 0) F = 0) : F = 0 := by
  obtain ⟨U, hu⟩ := hF.1
  have rows (y : ℤ) : ∀ x z : ℤ, F ![x, y, z] = 0 := by
    apply positive_row_zero (fun x z => F ![x, y, z]) U (fun x z h => hu x y z h)
    intro x z
    have h := congrFun hz ![x, y, z + 1]
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, variable_xyz] at h
    simpa [positiveClear, Finset.sum_range_succ, add_comm] using h
  funext e
  change F e = 0
  have h := rows (e 1) (e 0) (e 2)
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  simpa only [ee] using h

private theorem balanced_rotated_zero (k : ℕ) (a : Fin 3 → ℕ)
    (F : Distribution 3 R) (hF : NestedSupport F)
    (hz : polynomialAction (balancedRotatedPolynomial k a) F = 0) : F = 0 := by
  let X : LaurentPolynomial 3 := variablePolynomial 0
  let Y : LaurentPolynomial 3 := variablePolynomial 1
  let Z : LaurentPolynomial 3 := variablePolynomial 2
  have cv (i : Fin 3) := variable_preserves (R := R) i
  have cd : ∀ G : Distribution 3 R, NestedSupport G →
      NestedSupport (polynomialAction (Z - Y) G) := by
    intro G hG
    simpa only [Z, Y, map_sub, LinearMap.sub_apply] using
      nested_sub _ _ (cv 2 G hG) (cv 1 G hG)
  have ct : ∀ G : Distribution 3 R, NestedSupport G →
      NestedSupport (polynomialAction (X + Z - Y) G) := by
    intro G hG
    rw [show X + Z - Y = X + (Z - Y) by ring, map_add, LinearMap.add_apply]
    exact nested_add _ _ (cv 0 G hG) (cd G hG)
  have cp : ∀ G : Distribution 3 R, NestedSupport G →
      NestedSupport (polynomialAction (Z + X) G) := by
    intro G hG
    simpa only [Z, X, map_add, LinearMap.add_apply] using
      nested_add _ _ (cv 2 G hG) (cv 0 G hG)
  let FD := polynomialAction ((Z - Y) ^ k) F
  let FT := polynomialAction ((X + Z - Y) ^ k) FD
  let FX := polynomialAction (X ^ k) FT
  let FY := polynomialAction (Y ^ a 2) FX
  let FZ := polynomialAction (Z ^ a 1) FY
  have sd : NestedSupport FD := power_preserves (Z - Y) cd k F hF
  have st : NestedSupport FT := power_preserves (X + Z - Y) ct k FD sd
  have sx : NestedSupport FX := power_preserves X (cv 0) k FT st
  have sy : NestedSupport FY := power_preserves Y (cv 1) (a 2) FX sx
  have sz : NestedSupport FZ := power_preserves Z (cv 2) (a 1) FY sy
  have hp : polynomialAction ((Z + X) ^ a 0) FZ = 0 := by
    simpa only [balancedRotatedPolynomial, X, Y, Z, FZ, FY, FX, FT, FD,
      map_mul, Module.End.mul_apply] using hz
  have hz' : FZ = 0 := power_zero (Z + X) cp xz_positive_zero (a 0) FZ sz hp
  have hy : FY = 0 := power_zero Z (cv 2)
    (fun G _ h => variable_zero 2 G h) (a 1) FY sy hz'
  have hx : FX = 0 := power_zero Y (cv 1)
    (fun G _ h => variable_zero 1 G h) (a 2) FX sx hy
  have ht : FT = 0 := power_zero X (cv 0)
    (fun G _ h => variable_zero 0 G h) k FT st hx
  have hd : FD = 0 := power_zero (X + Z - Y) ct triple_difference_zero k FD sd ht
  exact power_zero (Z - Y) cd yz_difference_zero k F hF hd

theorem balanced_injective (k : ℕ) (a : Fin 3 → ℕ) (F G : Distribution 3 R)
    (hF : NestedSupport (balancedRotate F)) (hG : NestedSupport (balancedRotate G))
    (same : polynomialAction (balancedPolynomial k a) F =
      polynomialAction (balancedPolynomial k a) G) : F = G := by
  have eq : balancedRotate F = balancedRotate G := by
    apply sub_eq_zero.mp
    apply balanced_rotated_zero k a _ (nested_sub _ _ hF hG)
    rw [map_sub, balanced_action_rotate, balanced_action_rotate, same, sub_self]
  funext e
  have h := congrFun eq ![e 0, e 2, e 1]
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  simpa only [balancedRotate, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ee] using h

end
end D5.S3.VertexAlgebra.ThreeFieldBalancedPolynomial
