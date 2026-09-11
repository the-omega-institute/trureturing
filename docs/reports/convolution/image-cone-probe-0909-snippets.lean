import D5.S3.Zeros.Convolution.MatchingPolynomial
import D5.S3.Zeros.CoefficientBounds.SexticEnvelope
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

noncomputable section
open Polynomial
open scoped BigOperators
open D5.S3.Zeros.Convolution.FiniteFreeCommutatorDegreeFour
open D5.S3.Zeros.Convolution.MatchingFiber
open D5.S3.Zeros.Convolution.MatchingPolynomial

namespace ImageConeProbe0909

def reducedSym (m : ℕ) (r : Fin (2 * m) → ℝ) : ℝ[X] :=
  Polynomial.contract 2 (symmetrize (2 * m) (rootPolynomial r))

def imageCone (m : ℕ) : Set ℝ[X] := Set.range (reducedSym m)

example (m k : ℕ) (hk : k ≤ m) (r : Fin (2 * m) → ℝ) :
    elementaryCoeff m (reducedSym m r) k =
      matchingSum r k / ((2 * m).descFactorial k : ℝ) := by
  simpa only [elementaryCoeff, reducedSym, coeff_contract (by norm_num : (2 : ℕ) ≠ 0),
    Nat.sub_mul, Nat.mul_comm] using matching_identity (2 * m) k (by omega) r

example (n k : ℕ) (hk : 2 * k ≤ n) (r : Fin n → ℝ) :
    0 ≤ (-1 : ℝ)^k * (symmetrize n (rootPolynomial r)).coeff (n-2*k) := by
  rw [matching_identity n k hk r]
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro M _
  apply Finset.prod_nonneg
  intro e _
  induction e using Sym2.ind with
  | _ i j => exact sq_nonneg (r i - r j)

example (u v w : ℝ) (hp : RealRooted4 (centeredQuartic u v w)) :
    0 ≤ 2*w+u^2/6 ∧ 6*(2*w+u^2/6) ≤ (-2*u)^2 := by
  obtain ⟨_, hlo, hhi⟩ := centered_quartic_invariant_bounds u v w hp
  constructor <;> linarith only [hlo, hhi]

example (n : ℕ) (r : Fin n → ℝ) :
    (∑ i, r i^2)^2 ≤ (n : ℝ) * ∑ i, (r i^2)^2 := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => r i^2))

example (n : ℕ) (r : Fin n → ℝ) (hc : ∑ i, r i = 0) :
    let E := fun k => MvPolynomial.eval r (MvPolynomial.esymm (Fin n) ℝ k)
    (∑ i, r i^2) = -2 * E 2 ∧
      (∑ i, r i^4) = 2 * (E 2)^2 - 4 * E 4 := by
  dsimp
  have h2 := congrArg (MvPolynomial.eval r)
    (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) ℝ 2 (by decide))
  have h4 := congrArg (MvPolynomial.eval r)
    (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) ℝ 4 (by decide))
  have ha2 : Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := by decide
  have ha4 : Finset.antidiagonal (4 : ℕ) =
      {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} := by decide
  norm_num [ha2, ha4, Finset.sum_filter, Finset.sum_insert, Finset.sum_singleton,
    MvPolynomial.psum, MvPolynomial.esymm_one, hc] at h2 h4
  refine ⟨by linarith only [h2], ?_⟩
  rw [h2] at h4
  linarith only [h4]

example (r : Fin 6 → ℝ) (hc : ∑ i, r i = 0) :
    let p : ℝ[X] := ∏ i, (X - C (r i))
    let u := p.coeff 4
    let v := p.coeff 3
    let w := p.coeff 2
    let s := p.coeff 0
    let b1 := -2*u
    let b2 := 2*w+2*u^2/5
    let b3 := -(2*s+2*u*w/15-v^2/20)
    9*b3*(4*b1^2-5*b2) ≤ 5*b1*b2^2 := by
  have h := D5.S3.Zeros.CoefficientBounds.SexticEnvelope.centered_real_sextic_envelope r hc
  dsimp only at h ⊢
  obtain ⟨_, _, _, _, _, hb⟩ := h
  linarith only [hb]

end ImageConeProbe0909
