/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalClearedHermite
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalClearedHermite
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Cleared Hermite coefficients. -/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Four-node Hermite interpolation with independent weights and logarithmic slopes. -/

public section

namespace UniformMPSHorizontalSpectral

open scoped BigOperators
open MvPolynomial

noncomputable section

private def others : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

private def cross {A : Type*} [CommRing A] (v : Fin 4 → A) (i : Fin 4) (j : Fin 3) : A :=
  v i - v (others i j)

private def gapProduct {A : Type*} [CommRing A] (v : Fin 4 → A) (i : Fin 4) : A :=
  ∏ j : Fin 3, cross v i j

private def gapDerivative {A : Type*} [CommRing A] (v : Fin 4 → A) (i : Fin 4) : A :=
  cross v i 0 * cross v i 1 + cross v i 0 * cross v i 2 + cross v i 1 * cross v i 2

private def oppositeGaps {A : Type*} [CommRing A] (v : Fin 4 → A) (i : Fin 4) : A :=
  (v (others i 0) - v (others i 1)) *
  (v (others i 0) - v (others i 2)) *
  (v (others i 1) - v (others i 2))

/-- The spectral denominator used in both projections. -/
def hermiteClearing {A : Type*} [CommRing A] (v : Fin 4 → A) : A :=
  (∏ i, v i) *
  ((v 0 - v 1) * (v 0 - v 2) * (v 0 - v 3) *
    (v 1 - v 2) * (v 1 - v 3) * (v 2 - v 3)) ^ 3

private def complementaryClearing {A : Type*} [CommRing A] (v : Fin 4 → A) (i : Fin 4) : A :=
  (-1) ^ i.val * (∏ j : Fin 3, v (others i j)) * oppositeGaps v i ^ 3

private theorem hermiteClearing_factor {A : Type*} [CommRing A] (v : Fin 4 → A) (i : Fin 4) :
    hermiteClearing v = complementaryClearing v i * (v i * gapProduct v i ^ 3) := by
  fin_cases i <;>
    simp [hermiteClearing, complementaryClearing, oppositeGaps, gapProduct, cross,
      others, Fin.prod_univ_succ] <;> ring

private def nodalExpr {A : Type*} [CommRing A] (v : Fin 4 → A) (x : A) (i : Fin 4) : A :=
  ∏ j : Fin 3, (x - v (others i j))

private def clearedExpr {A : Type*} [CommRing A] (v w : Fin 4 → A) (μ x : A) : A :=
  ∑ i, complementaryClearing v i * w i *
    (v i * (gapProduct v i - 2 * gapDerivative v i * (x - v i)) +
      μ * gapProduct v i * (x - v i)) * nodalExpr v x i ^ 2

/-- The cleared interpolant is defined over the coefficient ring, even at colliding nodes. -/
def clearedHermite {A : Type*} [CommRing A] (v w : Fin 4 → A) (μ : A) : Polynomial A :=
  clearedExpr (Polynomial.C ∘ v) (Polynomial.C ∘ w) (Polynomial.C μ) Polynomial.X

private theorem map_clearedExpr {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (v w : Fin 4 → A) (μ x : A) :
    f (clearedExpr v w μ x) = clearedExpr (f ∘ v) (f ∘ w) (f μ) (f x) := by
  simp [clearedExpr, complementaryClearing, gapProduct, gapDerivative, oppositeGaps,
    nodalExpr, cross, map_ofNat]

private theorem degree_mul_le {σ R : Type*} [CommRing R]
    {p q : MvPolynomial σ R} {a b : ℕ} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)

private theorem degree_pow_le {σ R : Type*} [CommRing R]
    {p : MvPolynomial σ R} {a : ℕ} (hp : p.totalDegree ≤ a) (n : ℕ) :
    (p ^ n).totalDegree ≤ n * a :=
  (totalDegree_pow _ _).trans (Nat.mul_le_mul_left n hp)

private theorem degree_add_le {σ R : Type*} [CommRing R]
    {p q : MvPolynomial σ R} {a : ℕ} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ a) :
    (p + q).totalDegree ≤ a :=
  (totalDegree_add _ _).trans (max_le hp hq)

private theorem degree_sub_le {σ R : Type*} [CommRing R]
    {p q : MvPolynomial σ R} {a : ℕ} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ a) :
    (p - q).totalDegree ≤ a :=
  (totalDegree_sub _ _).trans (max_le hp hq)

private theorem degree_prod_three {σ R : Type*} [CommRing R]
    (p : Fin 3 → MvPolynomial σ R) (h : ∀ j, (p j).totalDegree ≤ 1) :
    (∏ j, p j).totalDegree ≤ 3 := by
  apply (totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum fun j _ => h j).trans (by simp)

private theorem clearedExpr_totalDegree {σ R : Type*} [CommRing R]
    (v w : Fin 4 → MvPolynomial σ R) (μ x : MvPolynomial σ R)
    (hv : ∀ i, (v i).totalDegree ≤ 1) (hw : ∀ i, (w i).totalDegree ≤ 0)
    (hμ : μ.totalDegree ≤ 0) (hx : x.totalDegree ≤ 1) :
    (clearedExpr v w μ x).totalDegree ≤ 22 := by
  have hdiff (i j : Fin 4) : (v i - v j).totalDegree ≤ 1 := degree_sub_le (hv i) (hv j)
  have hcross (i : Fin 4) (j : Fin 3) : (cross v i j).totalDegree ≤ 1 := hdiff _ _
  unfold clearedExpr
  apply totalDegree_finsetSum_le
  intro i _
  have hcomp : (complementaryClearing v i).totalDegree ≤ 12 := by
    unfold complementaryClearing oppositeGaps
    have hs : (((-1 : MvPolynomial σ R) ^ i.val)).totalDegree ≤ 0 := by
      exact degree_pow_le (p := (-1 : MvPolynomial σ R)) (a := 0) (by simp) i.val
    exact degree_mul_le (degree_mul_le hs (degree_prod_three _ fun _ => hv _))
      (degree_pow_le (degree_mul_le (degree_mul_le (hdiff _ _) (hdiff _ _)) (hdiff _ _)) 3)
  have hgap : (gapProduct v i).totalDegree ≤ 3 := degree_prod_three _ (hcross i)
  have hder : (gapDerivative v i).totalDegree ≤ 2 :=
    degree_add_le (degree_add_le (degree_mul_le (hcross i 0) (hcross i 1))
      (degree_mul_le (hcross i 0) (hcross i 2))) (degree_mul_le (hcross i 1) (hcross i 2))
  have hlinear : (x - v i).totalDegree ≤ 1 := degree_sub_le hx (hv i)
  have htwo : (2 : MvPolynomial σ R).totalDegree ≤ 0 := by
    rw [← map_ofNat (C : R →+* MvPolynomial σ R) 2, totalDegree_C]
  have hvalue :
      (v i * (gapProduct v i - 2 * gapDerivative v i * (x - v i))).totalDegree ≤ 4 :=
    degree_mul_le (hv i) (degree_sub_le hgap (degree_mul_le (degree_mul_le htwo hder) hlinear))
  have hslope : (μ * gapProduct v i * (x - v i)).totalDegree ≤ 4 :=
    degree_mul_le (degree_mul_le hμ hgap) hlinear
  have hnodal : (nodalExpr v x i).totalDegree ≤ 3 :=
    degree_prod_three _ fun _ => degree_sub_le hx (hv _)
  exact degree_mul_le (degree_mul_le (degree_mul_le hcomp (hw i))
    (degree_add_le hvalue hslope)) (degree_pow_le hnodal 2)

private theorem optionEquivLeft_rename_some {σ R : Type*} [CommRing R]
    (p : MvPolynomial σ R) :
    optionEquivLeft R σ (rename some p) = Polynomial.C p := by
  let f : MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
    (optionEquivLeft R σ).toAlgHom.comp (rename some)
  let g : MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
    IsScalarTower.toAlgHom R (MvPolynomial σ R) (Polynomial (MvPolynomial σ R))
  have he : f = g := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [f, g]
  exact DFunLike.congr_fun he p

/-- For arbitrary affine spectral nodes, the coefficient of the formal transfer power
has spectral degree at most `22 - r`. The weights and the slope are scalars. -/
theorem clearedHermite_coeff_totalDegree {σ R : Type*} [CommRing R]
    (v : Fin 4 → MvPolynomial σ R) (w : Fin 4 → R) (μ : R)
    (hv : ∀ i, (v i).totalDegree ≤ 1) (r : ℕ) :
    ((clearedHermite v (C ∘ w) (C μ)).coeff r).totalDegree ≤ 22 - r := by
  let p := clearedExpr (rename some ∘ v) (C ∘ w) (C μ) (X (R := R) (none : Option σ))
  have hp : p.totalDegree ≤ 22 := by
    apply clearedExpr_totalDegree
    · exact fun i => (totalDegree_rename_le some (v i)).trans (hv i)
    · intro i
      simp
    · simp
    · rcases subsingleton_or_nontrivial R with hR | hR
      · rw [Subsingleton.elim (X (none : Option σ) : MvPolynomial (Option σ) R) 0]
        simp
      · exact (totalDegree_X _).le
  have he : optionEquivLeft R σ p = clearedHermite v (C ∘ w) (C μ) := by
    change (optionEquivLeft R σ).toRingHom (clearedExpr _ _ _ _) = _
    rw [map_clearedExpr]
    simp [clearedHermite, optionEquivLeft_rename_some, Function.comp_def]
  rw [← he]
  by_cases hr : r ≤ p.totalDegree
  · have h := totalDegree_coeff_optionEquivLeft_add_le R σ p r hr
    omega
  · have hlt : (optionEquivLeft R σ p).natDegree < r := by
      rw [natDegree_optionEquivLeft]
      exact (degreeOf_le_totalDegree p none).trans_lt (Nat.lt_of_not_ge hr)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, totalDegree_zero]
    exact Nat.zero_le _

section Field

open Polynomial

variable {F : Type*} [Field F]

private def lagrangeCardinal (v : Fin 4 → F) (i : Fin 4) : Polynomial F :=
  Polynomial.C (gapProduct v i)⁻¹ * nodalExpr (Polynomial.C ∘ v) Polynomial.X i

private theorem lagrangeCardinal_eq_basis (v : Fin 4 → F) (i : Fin 4) :
    lagrangeCardinal v i = Lagrange.basis Finset.univ v i := by
  have himage : Finset.univ.image (others i) = Finset.univ.erase i := by
    fin_cases i <;> decide
  have hinj : Function.Injective (others i) := by
    fin_cases i <;> decide
  rw [Lagrange.basis, ← himage, Finset.prod_image hinj.injOn]
  simp only [lagrangeCardinal, gapProduct, nodalExpr, Lagrange.basisDivisor, cross,
    Function.comp_apply, Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib]

private theorem lagrangeCardinal_derivative (v : Fin 4 → F) (i : Fin 4) :
    (lagrangeCardinal v i).derivative.eval (v i) =
      (gapProduct v i)⁻¹ * gapDerivative v i := by
  have hone : (0 : Fin 2).succ = (1 : Fin 3) := by decide
  have htwo : (0 : Fin 1).succ.succ = (2 : Fin 3) := by decide
  simp only [lagrangeCardinal, nodalExpr, Fin.prod_univ_succ, Fin.prod_univ_zero,
    mul_one, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_sub, Polynomial.derivative_X, sub_zero,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, one_mul, Function.comp_apply, gapDerivative, cross, hone, htwo]
  ring

/-- The usual cardinal formula for values `w i` and slopes `μ * w i / v i`. -/
def hermiteInterpolant (v w : Fin 4 → F) (μ : F) : Polynomial F :=
  ∑ i, Polynomial.C (w i) *
    ((1 - 2 * Polynomial.C ((Lagrange.basis Finset.univ v i).derivative.eval (v i)) *
        (Polynomial.X - Polynomial.C (v i))) * (Lagrange.basis Finset.univ v i) ^ 2 +
      Polynomial.C (μ / v i) *
        ((Polynomial.X - Polynomial.C (v i)) * (Lagrange.basis Finset.univ v i) ^ 2))

private theorem clearing_summand {A : Type*} [CommRing A]
    (a b a' b' c q w μ x u : A) (ha : a * a' = 1) (hb : b * b' = 1) :
    q * w * (a * (b - 2 * c * x) + μ * b * x) * u ^ 2 =
      q * (a * b ^ 3) *
        (w * ((1 - 2 * (b' * c) * x) * (b' * u) ^ 2 + (μ * a') * (x * (b' * u) ^ 2))) := by
  calc
    _ = q * w *
        (a * (b * (b * b') ^ 2 - 2 * c * x * (b * b') ^ 3) +
          μ * b * x * (b * b') ^ 2 * (a * a')) * u ^ 2 := by rw [ha, hb]; ring
    _ = _ := by ring

/-- The polynomial numerator agrees with the cleared cardinal formula at simple,
nonzero nodes. The proof also applies after any specialization into a field. -/
theorem clearedHermite_eq_clear_mul (v w : Fin 4 → F) (μ : F)
    (hv : Function.Injective v) (h₀ : ∀ i, v i ≠ 0) :
    clearedHermite v w μ = Polynomial.C (hermiteClearing v) * hermiteInterpolant v w μ := by
  unfold clearedHermite hermiteInterpolant clearedExpr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hd : gapProduct v i ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply sub_ne_zero.mpr
    intro h
    have hne : i ≠ others i j := by
      fin_cases i <;> fin_cases j <;> decide
    exact hne (hv h)
  rw [hermiteClearing_factor v i]
  simp only [← lagrangeCardinal_eq_basis v i, lagrangeCardinal_derivative]
  simp only [lagrangeCardinal, Function.comp_apply, map_mul, map_pow, div_eq_mul_inv]
  have hc : complementaryClearing (Polynomial.C ∘ v) i =
      Polynomial.C (complementaryClearing v i) := by
    simp [complementaryClearing, oppositeGaps]
  have hgap : gapProduct (Polynomial.C ∘ v) i = Polynomial.C (gapProduct v i) := by
    simp [gapProduct, cross]
  have hder : gapDerivative (Polynomial.C ∘ v) i = Polynomial.C (gapDerivative v i) := by
    simp [gapDerivative, cross]
  rw [hc, hgap, hder]
  apply clearing_summand
  · rw [← map_mul, mul_inv_cancel₀ (h₀ i), map_one]
  · rw [← map_mul, mul_inv_cancel₀ hd, map_one]

/-- Specialization of the polynomial numerator by a coefficient homomorphism. -/
theorem clearedHermite_map {A : Type*} [CommRing A] (f : A →+* F)
    (v w : Fin 4 → A) (μ : A) :
    (clearedHermite v w μ).map f = clearedHermite (f ∘ v) (f ∘ w) (f μ) := by
  rw [clearedHermite, ← Polynomial.coe_mapRingHom, map_clearedExpr]
  simp [clearedHermite, Function.comp_def]

end Field

end

end UniformMPSHorizontalSpectral
