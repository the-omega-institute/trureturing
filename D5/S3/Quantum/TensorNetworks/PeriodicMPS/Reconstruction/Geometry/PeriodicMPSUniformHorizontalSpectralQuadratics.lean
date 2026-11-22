/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalSpectralQuadratics
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalSpectralQuadratics
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Spectral degrees of the determinant square rules. -/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring

/-! Spectral degrees of the square rules in the two determinant charts. -/

public section

noncomputable section

namespace UniformMPSHorizontalSpectral

open MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- The sum of the first two ambient determinants in both charts. -/
def firstSum (a b : MvPolynomial σ R) (U k : R) : MvPolynomial σ R :=
  a + C (4 * U + k ^ 2) - C 2 * b

/-- Sum of the second pair in the U chart. Here `ki` stands for the inverse of `k`. -/
def secondSumU (b c : MvPolynomial σ R) (U ki : R) : MvPolynomial σ R :=
  (c - b ^ 2) * C (ki ^ 2) + b - C (2 * U)

/-- Sum of the second pair in the k chart, scaled by `k^2`. -/
def secondSumK (b c : MvPolynomial σ R) (U k : R) : MvPolynomial σ R :=
  c - b ^ 2 + (b - C (2 * U)) * C (k ^ 2)

/-- The right-hand side of the square rule for the first difference. -/
def firstSquare (L : MvPolynomial σ R) (U : R) : MvPolynomial σ R :=
  L ^ 2 - C (4 * U)

/-- Right-hand side for the second difference. The final argument is `1` in the U chart
and `k^4` in the k chart. -/
def secondSquare (W b : MvPolynomial σ R) (U scale : R) : MvPolynomial σ R :=
  W ^ 2 - C (4 * U * scale) * (C U - b)

private theorem mul_bound
    {p q : MvPolynomial σ R} {a b : ℕ} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) :
    (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)

private theorem add_bound
    {p q : MvPolynomial σ R} {a : ℕ} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ a) :
    (p + q).totalDegree ≤ a :=
  (totalDegree_add _ _).trans (max_le hp hq)

private theorem sub_bound
    {p q : MvPolynomial σ R} {a : ℕ} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ a) :
    (p - q).totalDegree ≤ a :=
  (totalDegree_sub _ _).trans (max_le hp hq)

private theorem pow_bound {p : MvPolynomial σ R} {a : ℕ}
    (hp : p.totalDegree ≤ a) (n : ℕ) : (p ^ n).totalDegree ≤ n * a :=
  (totalDegree_pow _ _).trans (Nat.mul_le_mul_left n hp)

private theorem C_bound (r : R) (n : ℕ) : (C (σ := σ) r).totalDegree ≤ n := by simp

open scoped BigOperators in
/-- Elementary symmetric polynomial evaluated at the four spectral nodes. -/
def spectralElementary (v : Fin 4 → MvPolynomial σ R) (n : ℕ) : MvPolynomial σ R :=
  ∑ s ∈ Finset.univ.powersetCard n, ∏ i ∈ s, v i

/-- The degree is bounded by the size of the subsets even for affine nodes. -/
theorem spectralElementary_totalDegree (v : Fin 4 → MvPolynomial σ R)
    (hv : ∀ i, (v i).totalDegree ≤ 1) (n : ℕ) :
    (spectralElementary v n).totalDegree ≤ n := by
  classical
  unfold spectralElementary
  apply totalDegree_finsetSum_le
  intro s hs
  apply (totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum fun i _ => hv i).trans
    (by simpa using (Finset.mem_powersetCard.mp hs).2.le)

/-- The square estimates use only the elementary symmetric degree bounds.
The two choices of the second sum are recorded in the same statement. -/
theorem chart_quadratic_totalDegrees (a b c : MvPolynomial σ R) (U k ki : R)
    (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 3) (hc : c.totalDegree ≤ 4) :
    let L := firstSum a b U k
    let W := secondSumU b c U ki
    let V := secondSumK b c U k
    L.totalDegree ≤ 3 ∧ W.totalDegree ≤ 6 ∧ V.totalDegree ≤ 6 ∧
      (firstSquare L U).totalDegree ≤ 6 ∧
      (secondSquare W b U 1).totalDegree ≤ 12 ∧
      (secondSquare V b U (k ^ 4)).totalDegree ≤ 12 := by
  dsimp only
  have hL : (firstSum a b U k).totalDegree ≤ 3 := by
    unfold firstSum
    exact sub_bound (add_bound (ha.trans (by decide)) (C_bound _ _))
      (mul_bound (C_bound _ 0) hb)
  have hcb : (c - b ^ 2).totalDegree ≤ 6 :=
    sub_bound (hc.trans (by decide)) (pow_bound hb 2)
  have hW : (secondSumU b c U ki).totalDegree ≤ 6 := by
    unfold secondSumU
    exact sub_bound (add_bound (mul_bound hcb (C_bound _ 0)) (hb.trans (by decide)))
      (C_bound _ _)
  have hV : (secondSumK b c U k).totalDegree ≤ 6 := by
    unfold secondSumK
    exact add_bound hcb ((mul_bound (sub_bound hb (C_bound _ _)) (C_bound _ 0)).trans (by decide))
  have hX : (firstSquare (firstSum a b U k) U).totalDegree ≤ 6 :=
    sub_bound (pow_bound hL 2) (C_bound _ _)
  have hY (W : MvPolynomial σ R) (scale : R) (h : W.totalDegree ≤ 6) :
      (secondSquare W b U scale).totalDegree ≤ 12 :=
    sub_bound (pow_bound h 2) ((mul_bound (C_bound _ 0)
      (sub_bound (C_bound _ _) hb)).trans (by decide))
  exact ⟨hL, hW, hV, hX, hY _ _ hW, hY _ _ hV⟩

/-- Reduction of an arbitrary monomial by the two square rules preserves the spectral
budget when the first and second differences have weights three and six. The factor
on the right uses only exponents zero or one for each difference. -/
theorem reduce_quadratic_monomial {A : Type*} [CommRing A]
    [Algebra (MvPolynomial σ R) A]
    (p D E : MvPolynomial σ R) (x y : A) (i j : ℕ)
    (hD : D.totalDegree ≤ 6) (hE : E.totalDegree ≤ 12)
    (hx : x ^ 2 = algebraMap (MvPolynomial σ R) A D)
    (hy : y ^ 2 = algebraMap (MvPolynomial σ R) A E) :
    let reduced := p * D ^ (i / 2) * E ^ (j / 2)
    algebraMap (MvPolynomial σ R) A p * x ^ i * y ^ j =
      algebraMap (MvPolynomial σ R) A reduced * x ^ (i % 2) * y ^ (j % 2) ∧
    reduced.totalDegree + 3 * (i % 2) + 6 * (j % 2) ≤
      p.totalDegree + 3 * i + 6 * j := by
  dsimp only
  constructor
  · have hpow (z t : A) (n : ℕ) (h : z ^ 2 = t) : z ^ n = t ^ (n / 2) * z ^ (n % 2) := by
      conv_lhs => rw [show n = 2 * (n / 2) + n % 2 by omega]
      rw [pow_add, pow_mul, h]
    rw [hpow x _ i hx, hpow y _ j hy]
    simp only [map_mul, map_pow]
    ring
  · have h := mul_bound (mul_bound (le_refl p.totalDegree) (pow_bound hD (i / 2)))
      (pow_bound hE (j / 2))
    omega

end UniformMPSHorizontalSpectral
