/- GID: D5/S3/Constants/Moments/CountableHankelNegativeIndex
   generality: G
   mirror-B: D5/B/S3/Constants/Moments/CountableHankelNegativeIndex
   mirror-E: none(waiver:countable-spectrum-classical-analysis)
   anchors: []
   utility: none
   digest: Complete-spectrum negative index is bounded by an exhaustive finite active-pair cover. -/

import D5.S3.Constants.Moments.CountableHankelNegativeWitness
import D5.S3.Weil.ZetaLinear.ExactStickyReduction
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
The form uses ordinary complex squares on real polynomials and the entire
absolutely convergent spectrum. A finite cover must contain every nonreal
index of nonzero weight, on one of its two indicated sides.

The index type is arbitrary: summability, rather than an enumeration, controls
the full spectrum. Neither node/selector injectivity nor involutivity of the
permutation is needed. The theorem's telescope is preserved from the input.

This implements the classical upper-index argument in the existing owning
theory, section 6 / editorial note n29. It makes no new existence or novelty
claim about a zeta spectrum. The lower-family theorem has additional hypotheses
which are deliberately absent from this upper bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Polynomial
open scoped BigOperators ComplexConjugate

namespace D5.S3.Constants.Moments.CountableHankelNegativeIndex

open D5.S3.Constants.Moments.CountableHankelNegativeWitness
open D5.S3.Weil.ZetaLinear.ExactStickyReduction

/-- Vanishing of the one imaginary readout for each covered pair makes every
individual summand's real part nonnegative. No rearrangement is needed. -/
private theorem nonneg_of_readouts_eq_zero {ι : Type*} {r : ℕ}
    (z w : ι → ℂ) (c : Equiv.Perm ι)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hzc : ∀ i, z (c i) = conj (z i))
    (hwc : ∀ i, w (c i) = conj (w i))
    (hw : Summable (fun i => ‖w i‖))
    (s : Fin r → ι)
    (hcover : ∀ i, conj (z i) ≠ z i → w i ≠ 0 →
      ∃ j, i = s j ∨ i = c (s j))
    (hreal : ∀ i, conj (z i) = z i → 0 ≤ (w i).re)
    (b : Fin r → ℂ) (hb : ∀ j, (b j) ^ 2 = w (s j))
    (p : ℝ[X])
    (hp : ∀ j, (b j * p.eval₂ Complex.ofRealHom (z (s j))).im = 0) :
    0 ≤ (∑' i, w i * (p.eval₂ Complex.ofRealHom (z i)) ^ 2).re := by
  classical
  have heval_conj (i : ι) :
      p.eval₂ Complex.ofRealHom (z (c i)) =
        conj (p.eval₂ Complex.ofRealHom (z i)) := by
    rw [hzc]
    exact Polynomial.aeval_conj p (z i)
  have hpair_re (i : ι) :
      (w (c i) * (p.eval₂ Complex.ofRealHom (z (c i))) ^ 2).re =
        (w i * (p.eval₂ Complex.ofRealHom (z i)) ^ 2).re := by
    rw [hwc, heval_conj, ← map_pow, ← map_mul, Complex.conj_re]
  have hselected (j : Fin r) :
      0 ≤ (w (s j) * (p.eval₂ Complex.ofRealHom (z (s j))) ^ 2).re := by
    calc
      0 ≤ (b j * p.eval₂ Complex.ofRealHom (z (s j))).re ^ 2 := sq_nonneg _
      _ = ((b j * p.eval₂ Complex.ofRealHom (z (s j))) ^ 2).re := by
        simp only [pow_two, Complex.mul_re, hp j, mul_zero, sub_zero]
      _ = (w (s j) * (p.eval₂ Complex.ofRealHom (z (s j))) ^ 2).re := by
        rw [mul_pow, hb j]
  have hterm (i : ι) :
      0 ≤ (w i * (p.eval₂ Complex.ofRealHom (z i)) ^ 2).re := by
    by_cases hzi : conj (z i) = z i
    · have hpconj : p.eval₂ Complex.ofRealHom (conj (z i)) =
          conj (p.eval₂ Complex.ofRealHom (z i)) := Polynomial.aeval_conj p (z i)
      rw [hzi] at hpconj
      have hpim : (p.eval₂ Complex.ofRealHom (z i)).im = 0 := by
        have him := congrArg Complex.im hpconj
        simp only [Complex.conj_im] at him
        linarith
      calc
        0 ≤ (w i).re * (p.eval₂ Complex.ofRealHom (z i)).re ^ 2 :=
          mul_nonneg (hreal i hzi) (sq_nonneg _)
        _ = (w i * (p.eval₂ Complex.ofRealHom (z i)) ^ 2).re := by
          simp only [pow_two, Complex.mul_re, Complex.mul_im, hpim,
            mul_zero, zero_mul, sub_zero, add_zero]
    · by_cases hwi : w i = 0
      · simp only [hwi, zero_mul, Complex.zero_re, le_refl]
      · rcases hcover i hzi hwi with ⟨j, hij | hij⟩
        · rw [hij]
          exact hselected j
        · rw [hij, hpair_re]
          exact hselected j
  have hsum : Summable (fun i => w i *
      (p.eval₂ Complex.ofRealHom (z i)) ^ 2) := square_summable z w hz hw p
  rw [Complex.re_tsum hsum]
  exact tsum_nonneg hterm

/-- An exhaustive cover by `r` conjugate pairs bounds the complete negative
index of the full ordinary-square form on real polynomials. Nodes and selectors
may repeat; real-node weights need only have nonnegative real part. -/
theorem negativeIndex_le {ι : Type*} (z w : ι → ℂ) (c : Equiv.Perm ι)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hzc : ∀ i, z (c i) = conj (z i))
    (hwc : ∀ i, w (c i) = conj (w i))
    (hw : Summable (fun i => ‖w i‖))
    (r : ℕ) (s : Fin r → ι)
    (hcover : ∀ i, conj (z i) ≠ z i → w i ≠ 0 →
      ∃ j, i = s j ∨ i = c (s j))
    (hreal : ∀ i, conj (z i) = z i → 0 ≤ (w i).re) :
    negativeIndex (fun p : ℝ[X] =>
      (∑' i, w i * (p.eval₂ Complex.ofRealHom (z i)) ^ 2).re) ≤ (r : WithTop ℕ) := by
  classical
  have hsqrt : ∀ j : Fin r, ∃ b : ℂ, b ^ 2 = w (s j) := fun j =>
    IsAlgClosed.exists_pow_nat_eq (w (s j)) (by decide : 0 < (2 : ℕ))
  choose b hb using hsqrt
  let L : ℝ[X] →ₗ[ℝ] (Fin r → ℝ) := LinearMap.pi (fun j =>
    Complex.imLm.comp ((LinearMap.mulLeft ℝ (b j)).comp
      (Polynomial.aeval (z (s j)) : ℝ[X] →ₐ[ℝ] ℂ).toLinearMap))
  have hL_apply (p : ℝ[X]) (j : Fin r) :
      L p j = (b j * p.eval₂ Complex.ofRealHom (z (s j))).im := rfl
  have hnonneg (p : ℝ[X]) (hp : L p = 0) :
      0 ≤ (∑' i, w i * (p.eval₂ Complex.ofRealHom (z i)) ^ 2).re := by
    apply nonneg_of_readouts_eq_zero z w c hz hzc hwc hw s hcover hreal b hb p
    intro j
    have hj := congrFun hp j
    rw [hL_apply] at hj
    exact hj
  unfold negativeIndex
  apply sSup_le
  rintro _a ⟨n, hn, rfl⟩
  obtain ⟨T, _hTInjective, hTNegative⟩ := hn
  have hLTzero : ∀ x : Fin n → ℝ, (L.comp T) x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    have hzero : L (T x) = 0 := hx
    exact (not_lt_of_ge (hnonneg (T x) hzero)) (hTNegative x hx0)
  have hLT : Function.Injective (L.comp T) :=
    LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hLTzero)
  have hnr : n ≤ r := by
    simpa only [Module.finrank_fin_fun] using
      (LinearMap.finrank_le_finrank_of_injective (f := L.comp T) hLT)
  exact WithTop.coe_le_coe.mpr hnr

end D5.S3.Constants.Moments.CountableHankelNegativeIndex
