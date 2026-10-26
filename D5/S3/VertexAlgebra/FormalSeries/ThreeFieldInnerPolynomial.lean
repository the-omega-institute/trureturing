/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal inner clearing and cancellation on its actual nested chamber. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldPolynomialCovariance
import D5.S3.VertexAlgebra.FormalSeries.SupportedFinalRInjectivity
import Batteries.Tactic.OpenPrivate

/-! The chamber is b << z << x. The two cross factors are cancelled using
the fixed-b z bound; the triple factor first uses induction in b. The finite
polynomial expansions and Carnahan binomial inversions are reused. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldInnerPolynomial
open UniformGradedLocalCorrelator SupportedChannelSeries SupportedFinalRInjectivity
open scoped BigOperators
noncomputable section

open private old_expansion act_positive from
  D5.S3.VertexAlgebra.FormalSeries.ThreeFieldPolynomialCovariance
open private variable_action variable_xyz variable_zero variable_preserves
  nested_sub nested_add xy_zero power_preserves power_zero from
  D5.S3.VertexAlgebra.FormalSeries.SupportedFinalRInjectivity

/-- The original multiplier, in the original x,b,z coordinates. -/
def innerPolynomial (k : ℕ) (a : Fin 3 → ℕ) : LaurentPolynomial 3 :=
  variablePolynomial 0 ^ a 0 * (variablePolynomial 0 - variablePolynomial 1 -
    variablePolynomial 2) ^ k * (variablePolynomial 0 - variablePolynomial 2) ^ k *
    variablePolynomial 1 ^ k * (variablePolynomial 1 + variablePolynomial 2) ^ a 1 *
    variablePolynomial 2 ^ a 2

/-- This only reorders coefficient arguments; it substitutes no raw variable. -/
def rotate {V : Type*} (F : Distribution 3 V) : Distribution 3 V :=
  fun e => F ![e 2, e 0, e 1]

private def cycleExponent : Exponent 3 →+ Exponent 3 where
  toFun e := ![e 1, e 2, e 0]
  map_zero' := by
    funext i
    fin_cases i <;> rfl
  map_add' e d := by
    funext i
    fin_cases i <;> rfl

private def cyclePolynomial : LaurentPolynomial 3 →ₐ[ℂ] LaurentPolynomial 3 :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ cycleExponent

private theorem rotate_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : LaurentPolynomial 3) (F : Distribution 3 V) :
    polynomialAction (cyclePolynomial p) (rotate F) = rotate (polynomialAction p F) := by
  induction p using AddMonoidAlgebra.induction_on with
  | of e =>
    change polynomialAction (cyclePolynomial (AddMonoidAlgebra.single e 1)) _ =
      rotate (polynomialAction (AddMonoidAlgebra.single e 1) F)
    simp only [cyclePolynomial, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single, polynomialAction, AddMonoidAlgebra.lift_single]
    funext d
    change (1 : ℂ) • F ![(d - cycleExponent e) 2, (d - cycleExponent e) 0,
      (d - cycleExponent e) 1] = (1 : ℂ) • F (![d 2, d 0, d 1] - e)
    congr 2
    funext i
    fin_cases i <;> simp [cycleExponent]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
    rfl
  | smul r p hp =>
    simp only [map_smul, LinearMap.smul_apply, hp]
    rfl

/-- The same multiplier in [b,z,x] coefficient order. -/
def rotatedPolynomial (k : ℕ) (a : Fin 3 → ℕ) : LaurentPolynomial 3 :=
  variablePolynomial 2 ^ a 0 * (variablePolynomial 2 - variablePolynomial 0 -
    variablePolynomial 1) ^ k * (variablePolynomial 2 - variablePolynomial 1) ^ k *
    variablePolynomial 0 ^ k * (variablePolynomial 0 + variablePolynomial 1) ^ a 1 *
    variablePolynomial 1 ^ a 2

private theorem cycle_inner (k : ℕ) (a : Fin 3 → ℕ) :
    cyclePolynomial (innerPolynomial k a) = rotatedPolynomial k a := by
  have cv (i : Fin 3) : cyclePolynomial (variablePolynomial i) =
      variablePolynomial (![2, 0, 1] i) := by
    simp only [cyclePolynomial, variablePolynomial, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single]
    congr 1
    funext j
    fin_cases i <;> fin_cases j <;> simp [cycleExponent]
  simp only [innerPolynomial, rotatedPolynomial, map_mul, map_pow, map_sub, map_add, cv]
  rfl

theorem inner_action_rotate {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (a : Fin 3 → ℕ) (F : Distribution 3 V) :
    polynomialAction (rotatedPolynomial k a) (rotate F) =
      rotate (polynomialAction (innerPolynomial k a) F) := by
  rw [← cycle_inner]
  exact rotate_action _ F

/-- The literal accepted old expansion, with no support premise. -/
theorem inner_action_expansion {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (a : Fin 3 → ℕ) (F : Distribution 3 V) (x b z : ℤ) :
    polynomialAction (innerPolynomial k a) F ![x, b, z] =
      ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
        (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
          ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) •
            (∑ h ∈ Finset.range (a 1 + p + 1), ((a 1 + p).choose h : ℂ) •
              F ![x - a 0 - 2 * k + p + q, b - k - h,
                z - (a 2 + q) - (a 1 + p) + h])) := by
  rw [innerPolynomial, old_expansion]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
  apply Finset.sum_congr rfl
  intro q hq
  have hqk : q ≤ k := by simpa using Finset.mem_range.mp hq
  rw [act_positive]
  apply congrArg (fun v : V => (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
    ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) • v))
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp [Nat.cast_add,
    Nat.cast_sub (show p ≤ a 0 + 2 * k by omega),
    Nat.cast_sub (show q ≤ a 0 + 2 * k - p by omega)]; omega

variable {R : Type*} [CommRing R] [Algebra ℂ R]

private theorem difference_row_zero (I : ℤ → ℤ → R) (B : ℕ)
    (lower : ∀ x z : ℤ, z < -(B : ℤ) → I x z = 0)
    (hz : ∀ x z : ℤ, clear 1 I x z = 0) : ∀ x z : ℤ, I x z = 0 := by
  intro x z
  by_cases h : 0 ≤ z + B
  · rw [supported_reconstruction I 1 B lower x z h]
    simp only [hz, smul_zero, Finset.sum_const_zero]
  · exact lower x z (by omega)

private theorem yz_difference_zero (F : Distribution 3 R) (hF : NestedSupport F)
    (hz : polynomialAction (variablePolynomial 2 - variablePolynomial 1) F = 0) :
    F = 0 := by
  have rows (b : ℤ) : ∀ x z : ℤ, F ![b, z, x] = 0 := by
    obtain ⟨B, hb⟩ := hF.2 b
    apply difference_row_zero (fun x z => F ![b, z, x]) B (fun x z h => hb z x h)
    intro x z
    have h := congrFun hz ![b, z, x]
    simp only [map_sub, LinearMap.sub_apply, Pi.sub_apply, variable_xyz] at h
    simpa [clear, Finset.sum_range_succ, sub_eq_add_neg] using h
  funext e
  change F e = 0
  have h := rows (e 0) (e 2) (e 1)
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  simpa only [ee] using h

/-- Earlier b rows vanish inductively; only the current row's own z cutoff
is used to cancel x-z. No uniform x cutoff or global z cutoff is present. -/
private theorem triple_difference_zero (F : Distribution 3 R) (hF : NestedSupport F)
    (hz : polynomialAction
      (variablePolynomial 2 - variablePolynomial 0 - variablePolynomial 1) F = 0) :
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
      simp only [map_sub, LinearMap.sub_apply, Pi.sub_apply, variable_xyz] at h
      simp only [Fin.isValue, reduceIte, sub_zero, prev] at h
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

private theorem rotated_zero (k : ℕ) (a : Fin 3 → ℕ)
    (F : Distribution 3 R) (hF : NestedSupport F)
    (hz : polynomialAction (rotatedPolynomial k a) F = 0) : F = 0 := by
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
      NestedSupport (polynomialAction (Z - X - Y) G) := by
    intro G hG
    have eq : Z - X - Y = (Z - Y) - X := by ring
    rw [eq, map_sub, LinearMap.sub_apply]
    exact nested_sub _ _ (cd G hG) (cv 0 G hG)
  have cp : ∀ G : Distribution 3 R, NestedSupport G →
      NestedSupport (polynomialAction (X + Y) G) := by
    intro G hG
    simpa only [X, Y, map_add, LinearMap.add_apply] using
      nested_add _ _ (cv 0 G hG) (cv 1 G hG)
  let FY := polynomialAction (Y ^ a 2) F
  let FP := polynomialAction ((X + Y) ^ a 1) FY
  let FX := polynomialAction (X ^ k) FP
  let FD := polynomialAction ((Z - Y) ^ k) FX
  let FT := polynomialAction ((Z - X - Y) ^ k) FD
  have sy : NestedSupport FY := power_preserves Y (cv 1) (a 2) F hF
  have sp : NestedSupport FP := power_preserves (X + Y) cp (a 1) FY sy
  have sx : NestedSupport FX := power_preserves X (cv 0) k FP sp
  have sd : NestedSupport FD := power_preserves (Z - Y) cd k FX sx
  have st : NestedSupport FT := power_preserves (Z - X - Y) ct k FD sd
  have ht : polynomialAction (Z ^ a 0) FT = 0 := by
    simpa only [rotatedPolynomial, X, Y, Z, FT, FD, FX, FP, FY,
      map_mul, Module.End.mul_apply] using hz
  have hd : FT = 0 := power_zero Z (cv 2)
    (fun G _ h => variable_zero 2 G h) (a 0) FT st ht
  have hx : FD = 0 := power_zero (Z - X - Y) ct triple_difference_zero k FD sd hd
  have hp : FX = 0 := power_zero (Z - Y) cd yz_difference_zero k FX sx hx
  have hpos : FP = 0 := power_zero X (cv 0)
    (fun G _ h => variable_zero 0 G h) k FP sp hp
  have hy : FY = 0 := power_zero (X + Y) cp
    xy_zero (a 1) FY sy hpos
  exact power_zero Y (cv 1) (fun G _ h => variable_zero 1 G h) (a 2) F hF hy

theorem inner_injective (k : ℕ) (a : Fin 3 → ℕ) (F G : Distribution 3 R)
    (hF : NestedSupport (rotate F)) (hG : NestedSupport (rotate G))
    (same : polynomialAction (innerPolynomial k a) F =
      polynomialAction (innerPolynomial k a) G) : F = G := by
  have eq : rotate F = rotate G := by
    apply sub_eq_zero.mp
    apply rotated_zero k a _ (nested_sub _ _ hF hG)
    rw [map_sub, inner_action_rotate, inner_action_rotate, same, sub_self]
  funext e
  have h := congrFun eq ![e 1, e 2, e 0]
  have ee : (![e 0, e 1, e 2] : Exponent 3) = e := by
    funext i
    fin_cases i <;> rfl
  simpa only [rotate, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ee] using h

end
end D5.S3.VertexAlgebra.ThreeFieldInnerPolynomial
