/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSingletNorm
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalSingletNorm
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Coprimality of the singlet and middle expressions. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformTernaryRemainder
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalBoundaryCoprime
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Resultants.PeriodicMPSUniformVerticalMiddle
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
Specialize the fourth root to zero, take the norm of the ternary power
remainder on the singlet hypersurface, and cancel the coordinate product
using pure-axis evaluations. Homogeneous zero-specialization lifts relative
primality to the four-root ring.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalSingletNorm

open MvPolynomial
open PeriodicMPSUniformTernaryRemainder
open scoped BigOperators Matrix

noncomputable section

section MiddleBridge

variable {R : Type*} [CommRing R]

/-- The complete homogeneous spectral expression for the middle factor,
indexed by `m = k + 4`. -/
def middlePolynomial (K : Type*) [CommSemiring K] (k : ℕ) : MvPolynomial (Fin 4) K :=
  hsymm (Fin 4) K (k + 1) ^ 2 * hsymm (Fin 4) K (k + 4) +
    hsymm (Fin 4) K (k + 3) ^ 2 * hsymm (Fin 4) K k

/-- The series in the checked literal middle calculation is the geometric
product of the four actual roots. -/
theorem section_completeSeries_eq_rootSeries (r s t u p : R) :
    PeriodicMPSUniformVerticalMiddle.completeSeries
        (PeriodicMPSUniformVerticalMiddle.sectionB0 r s)
        (PeriodicMPSUniformVerticalMiddle.sectionB1 t u p) = rootSeries ![r, s, t, u] := by
  let f := PeriodicMPSUniformVerticalMiddle.completeSeries
    (PeriodicMPSUniformVerticalMiddle.sectionB0 r s)
    (PeriodicMPSUniformVerticalMiddle.sectionB1 t u p)
  let g := rootSeries ![r, s, t, u]
  let d := ((1 - PowerSeries.X * PowerSeries.C r) * (1 - PowerSeries.X * PowerSeries.C s)) *
    ((1 - PowerSeries.X * PowerSeries.C t) * (1 - PowerSeries.X * PowerSeries.C u))
  have hdf : d * f = 1 :=
    PeriodicMPSUniformVerticalMiddle.section_rootFactors_mul_completeSeries r s t u p
  have hdg : d * g = 1 := by
    have h := rootFactors_mul_rootSeries ![r, s, t, u]
    rw [Fin.prod_univ_four] at h
    simpa only [d, g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_assoc] using h
  change f = g
  calc
    f = (d * g) * f := by rw [hdg, one_mul]
    _ = g * (d * f) := by ac_rfl
    _ = g := by rw [hdf, mul_one]

/-- The spectral expression evaluates to the factor of the literal middle
determinant for exponent `k + 4`. -/
theorem aeval_middlePolynomial (K : Type*) [CommSemiring K] [Algebra K R]
    (r s t u p : R) (k : ℕ) :
    aeval ![r, s, t, u] (middlePolynomial K k) =
      PeriodicMPSUniformVerticalMiddle.middleFactor
        (PeriodicMPSUniformVerticalMiddle.sectionB0 r s)
        (PeriodicMPSUniformVerticalMiddle.sectionB1 t u p) (k + 2) := by
  simp only [middlePolynomial, map_add, map_mul, map_pow,
    PeriodicMPSUniformVerticalMiddle.middleFactor, section_completeSeries_eq_rootSeries,
    PeriodicMPSUniformVerticalMiddle.shiftedCoeff, ite_eq_left (show 1 ≤ k + 2 by omega),
    ite_eq_left (show 2 ≤ k + 2 by omega), show k + 2 - 1 = k + 1 by omega,
    show k + 2 - 2 = k by omega, ← coeff_rootSeries K]

end MiddleBridge

section Polynomials

variable {K : Type*} [Field K]

local notation "T" => MvPolynomial (Fin 3) K
local notation "F" => MvPolynomial (Fin 4) K
local notation "x₀" => (X (0 : Fin 3) : T)
local notation "x₁" => (X (1 : Fin 3) : T)
local notation "x₂" => (X (2 : Fin 3) : T)
local notation "c₃" => (x₀ * x₁ * x₂)
local notation "H₃" => (hsymm (Fin 3) K)
local notation "H₄" => (hsymm (Fin 4) K)

private theorem hsymm_homogeneous {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    (hsymm ι K n).IsHomogeneous n := by
  have hprod (s : Multiset ι) : ((s.map (X : ι → MvPolynomial ι K)).prod).IsHomogeneous s.card := by
    induction s using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one ι K
    | cons i s ih =>
      simpa only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Nat.add_comm] using
        (isHomogeneous_X K i).mul ih
  unfold hsymm
  apply IsHomogeneous.sum
  intro s _
  simpa only [s.property] using hprod s.val

private theorem aeval_hsymm_axis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι) (n : ℕ) : aeval (Pi.single j (1 : K)) (hsymm ι K n) = 1 := by
  classical
  simp only [hsymm, map_sum, ← Multiset.prod_hom', aeval_X]
  rw [Finset.sum_eq_single (Sym.replicate n j)]
  · simp [Sym.coe_replicate]
  · intro s _ hs
    have h : ¬ ∀ i ∈ s, i = j := fun h => hs (Sym.eq_replicate.mpr h)
    push Not at h
    obtain ⟨i, hi, hij⟩ := h
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨i, hi, by simp [hij]⟩)
  · simp

private theorem ternaryH_variables (n : ℕ) : ternaryH x₀ x₁ x₂ n = H₃ n := by
  have hv : (![x₀, x₁, x₂] : Fin 3 → T) = X := by
    funext i
    fin_cases i <;> rfl
  rw [ternaryH_eq_aeval_hsymm K, hv, aeval_X_left_apply]

private def killFourth : F →ₐ[K] T := killCompl (Fin.castSucc_injective 3)

private theorem killFourth_eq_aeval :
    (killFourth : F →ₐ[K] T) = aeval (![x₀, x₁, x₂, 0] : Fin 4 → T) := by
  apply algHom_ext
  intro i
  have hX (j : Fin 3) : (killFourth : F →ₐ[K] T) (X j.castSucc) = X j := by
    rw [killFourth, ← rename_X (R := K) (Fin.castSucc : Fin 3 → Fin 4) j,
      killCompl_rename_app]
  have hlast : Fin.last 3 ∉ Set.range (Fin.castSucc : Fin 3 → Fin 4) := by
    rintro ⟨j, hj⟩
    exact (Fin.ne_of_lt j.castSucc_lt_last) hj
  simp only [aeval_X]
  fin_cases i
  · exact hX 0
  · exact hX 1
  · exact hX 2
  · change killFourth (X (Fin.last 3) : F) = 0
    rw [killFourth, killCompl, aeval_X, dite_eq_right hlast]

private theorem killFourth_hsymm (n : ℕ) : (killFourth : F →ₐ[K] T) (H₄ n) = H₃ n := by
  have hseries :
      rootSeries (![x₀, x₁, x₂, 0] : Fin 4 → T) = rootSeries (![x₀, x₁, x₂] : Fin 3 → T) := by
    simp only [rootSeries, Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, geometric_zero (R := T), mul_one]
  calc
    (killFourth : F →ₐ[K] T) (H₄ n) =
        PowerSeries.coeff n (rootSeries (![x₀, x₁, x₂, 0] : Fin 4 → T)) := by
      rw [killFourth_eq_aeval]
      exact (coeff_rootSeries K (![x₀, x₁, x₂, 0] : Fin 4 → T) n).symm
    _ = PowerSeries.coeff n (rootSeries (![x₀, x₁, x₂] : Fin 3 → T)) :=
      congrArg (fun f : PowerSeries T => PowerSeries.coeff (R := T) n f) hseries
    _ = H₃ n := ternaryH_variables n

private theorem hsymm_three_isRelPrime_coordinates (n : ℕ) : IsRelPrime (H₃ n) c₃ := by
  have hcoord (i : Fin 3) : IsRelPrime (H₃ n) (X i) := by
    apply ((X_prime (R := K) (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr ?_).symm
    intro h
    let j := i + 1
    have hne : i ≠ j := by fin_cases i <;> decide
    let axis : Fin 3 → K := Pi.single j 1
    have hz := map_dvd (aeval axis) h
    have hvar : aeval axis (X i : T) = 0 := by simp [axis, Pi.single_eq_of_ne hne]
    change aeval axis (X i : T) ∣ aeval (Pi.single j (1 : K)) (H₃ n) at hz
    rw [hvar, aeval_hsymm_axis, zero_dvd_iff] at hz
    exact one_ne_zero hz
  exact ((hcoord 0).mul_right (hcoord 1)).mul_right (hcoord 2)

private theorem hsymm_three_ne_zero (n : ℕ) : (H₃ n : T) ≠ 0 := by
  intro h
  have he := aeval_hsymm_axis (K := K) (0 : Fin 3) n
  rw [h, map_zero] at he
  exact zero_ne_one he

private theorem hsymm_dvd_scaled_ternaryMiddle_sub_power (k : ℕ) :
    H₃ (k + 2) ∣ c₃ ^ 2 * (ternaryMiddle x₀ x₁ x₂ k - c₃ ^ (k + 2)) := by
  let I : Ideal T := Ideal.span {H₃ (k + 2)}
  let q : T →+* T ⧸ I := Ideal.Quotient.mk I
  have hz : ternaryH (q x₀) (q x₁) (q x₂) (k + 2) = 0 := by
    rw [← map_ternaryH q x₀ x₁ x₂ (k + 2), ternaryH_variables]
    exact Ideal.Quotient.mk_singleton_self (H₃ (k + 2))
  have hq : q (c₃ ^ (k + 4)) = q (c₃ ^ 2 * ternaryMiddle x₀ x₁ x₂ k) := by
    simpa only [map_mul, map_pow, map_add, ternaryMiddle, map_ternaryH q] using
      ternaryNorm_of_h_zero (q x₀) (q x₁) (q x₂) k hz
  refine (Ideal.Quotient.eq_zero_iff_dvd (H₃ (k + 2)) _).mp ?_
  change q (c₃ ^ 2 * (ternaryMiddle x₀ x₁ x₂ k - c₃ ^ (k + 2))) = 0
  have hpow : c₃ ^ 2 * c₃ ^ (k + 2) = c₃ ^ (k + 4) := by
    rw [← pow_add, show 2 + (k + 2) = k + 4 by omega]
  rw [mul_sub, hpow, map_sub, sub_eq_zero]
  exact hq.symm

private theorem hsymm_dvd_killCompl_middlePolynomial_sub_power (k : ℕ) :
    H₃ (k + 2) ∣ killCompl (Fin.castSucc_injective 3) (middlePolynomial K k) - c₃ ^ (k + 2) := by
  have hJ : killFourth (middlePolynomial K k) = ternaryMiddle x₀ x₁ x₂ k := by
    simp only [middlePolynomial, map_add, map_mul, map_pow, killFourth_hsymm, ternaryMiddle,
      ternaryH_variables]
  change H₃ (k + 2) ∣ killFourth (middlePolynomial K k) - c₃ ^ (k + 2)
  rw [hJ]
  have hcoords := hsymm_three_isRelPrime_coordinates (K := K) (k + 2)
  exact (hcoords.pow_right (n := 2)).dvd_of_dvd_mul_left
    (hsymm_dvd_scaled_ternaryMiddle_sub_power k)

/-- With `u = 0`, the difference `J_m - (rst)^(m-2)` is divisible by the
specialized complete homogeneous singlet factor. -/
theorem hsymm_dvd_aeval_middlePolynomial_sub_power (m : ℕ) (hm : 4 ≤ m) :
    aeval ![x₀, x₁, x₂, 0] (H₄ (m - 2)) ∣
      aeval ![x₀, x₁, x₂, 0] (middlePolynomial K (m - 4)) - c₃ ^ (m - 2) := by
  rw [← killFourth_eq_aeval (K := K), killFourth_hsymm,
    show m - 2 = m - 4 + 2 by omega]
  exact hsymm_dvd_killCompl_middlePolynomial_sub_power (K := K) (m - 4)

/-- Relative primality of the complete homogeneous singlet polynomial and
the literal middle spectral factor for every exponent `m ≥ 4`. -/
theorem hsymm_isRelPrime_middlePolynomial (m : ℕ) (hm : 4 ≤ m) :
    IsRelPrime (H₄ (m - 2)) (middlePolynomial K (m - 4)) := by
  generalize hk : m - 4 = k
  rw [show m - 2 = k + 2 by omega]
  refine PeriodicMPSUniformVerticalBoundaryCoprime.isRelPrime_of_killCompl
    (Fin.castSucc_injective 3) (w := 1) (by simp) (hsymm_homogeneous (K := K) (k + 2)) ?_ ?_
  · change killFourth (H₄ (k + 2)) ≠ 0
    rw [killFourth_hsymm]
    exact hsymm_three_ne_zero (k + 2)
  · change IsRelPrime (killFourth (H₄ (k + 2))) (killFourth (middlePolynomial K k))
    rw [killFourth_hsymm]
    obtain ⟨g, hg⟩ := hsymm_dvd_killCompl_middlePolynomial_sub_power (K := K) k
    have hJ : killFourth (middlePolynomial K k) = c₃ ^ (k + 2) + H₃ (k + 2) * g :=
      (sub_eq_iff_eq_add.mp hg).trans (add_comm _ _)
    rw [hJ]
    have hcoords := hsymm_three_isRelPrime_coordinates (K := K) (k + 2)
    exact (hcoords.pow_right (n := k + 2)).add_mul_left_right g

/-- Relative primality phrased directly using the checked literal middle
factor on the four-variable spectral section. -/
theorem hsymm_isRelPrime_literalMiddle (m : ℕ) (hm : 4 ≤ m) (p : F) :
    IsRelPrime (H₄ (m - 2))
      (PeriodicMPSUniformVerticalMiddle.middleFactor
        (PeriodicMPSUniformVerticalMiddle.sectionB0 (X (0 : Fin 4)) (X 1))
        (PeriodicMPSUniformVerticalMiddle.sectionB1 (X 2) (X 3) p) (m - 2)) := by
  have hv : (![X (0 : Fin 4), X 1, X 2, X 3] : Fin 4 → F) = X := by
    funext i
    fin_cases i <;> rfl
  have hJ := aeval_middlePolynomial K (X (0 : Fin 4)) (X 1) (X 2) (X 3) p (m - 4)
  rw [hv, aeval_X_left_apply, show m - 4 + 2 = m - 2 by omega] at hJ
  rw [← hJ]
  exact hsymm_isRelPrime_middlePolynomial m hm

end Polynomials

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalSingletNorm
