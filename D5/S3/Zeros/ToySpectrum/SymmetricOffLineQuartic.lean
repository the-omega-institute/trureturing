/- GID: D5/S3/Zeros/ToySpectrum/SymmetricOffLineQuartic
   generality: I
   mirror-B: D5/B/S3/Zeros/ToySpectrum/SymmetricOffLineQuartic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A symmetric entire quartic has four distinct zeros, all off the critical line. -/

import D5.S3.Weil.Convention
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace D5.S3.Zeros.ToySpectrum.SymmetricOffLineQuartic

open D5.S3.Weil.Convention
open Polynomial
open scoped ComplexConjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For every nondegenerate pair of real displacements, the source quartic is
entire, has exactly the displayed four distinct zeros, obeys reflection and
conjugation symmetry, and has no zero on the critical line. The same quartic
therefore witnesses that these symmetries do not force fixed-line
localization. -/
theorem symmetric_off_line_quartic_spec
    (delta gamma : Real) (hDelta : delta ≠ 0) (hGamma : gamma ≠ 0) :
    let centered : Complex[X] := X - C (criticalAbscissa : Complex)
    let quartic : Complex[X] :=
      ((centered - C (delta : Complex)) ^ 2 + C ((gamma : Complex) ^ 2)) *
        ((centered + C (delta : Complex)) ^ 2 + C ((gamma : Complex) ^ 2))
    Differentiable Complex (fun s => quartic.eval s) ∧
      (∀ s : Complex, quartic.eval s = 0 ↔
        s = (criticalAbscissa : Complex) + (delta : Complex) +
            Complex.I * (gamma : Complex) ∨
        s = (criticalAbscissa : Complex) + (delta : Complex) -
            Complex.I * (gamma : Complex) ∨
        s = (criticalAbscissa : Complex) - (delta : Complex) +
            Complex.I * (gamma : Complex) ∨
        s = (criticalAbscissa : Complex) - (delta : Complex) -
            Complex.I * (gamma : Complex)) ∧
      ({(criticalAbscissa : Complex) + (delta : Complex) +
            Complex.I * (gamma : Complex),
          (criticalAbscissa : Complex) + (delta : Complex) -
            Complex.I * (gamma : Complex),
          (criticalAbscissa : Complex) - (delta : Complex) +
            Complex.I * (gamma : Complex),
          (criticalAbscissa : Complex) - (delta : Complex) -
            Complex.I * (gamma : Complex)} : Finset Complex).card = 4 ∧
      (∀ s : Complex, quartic.eval (1 - s) = quartic.eval s) ∧
      (∀ s : Complex,
        quartic.eval (conj s) = conj (quartic.eval s)) ∧
      (∀ s : Complex,
        quartic.eval s = 0 → s.re ≠ criticalAbscissa) ∧
      ¬ (∀ s : Complex,
        quartic.eval s = 0 → s.re = criticalAbscissa) := by
  dsimp only
  let centered : Complex[X] := X - C (criticalAbscissa : Complex)
  let quartic : Complex[X] :=
    ((centered - C (delta : Complex)) ^ 2 + C ((gamma : Complex) ^ 2)) *
      ((centered + C (delta : Complex)) ^ 2 + C ((gamma : Complex) ^ 2))
  have hFactor (s : Complex) :
      quartic.eval s =
        (s - ((criticalAbscissa : Complex) + (delta : Complex) +
          Complex.I * (gamma : Complex))) *
        (s - ((criticalAbscissa : Complex) + (delta : Complex) -
          Complex.I * (gamma : Complex))) *
        (s - ((criticalAbscissa : Complex) - (delta : Complex) +
          Complex.I * (gamma : Complex))) *
        (s - ((criticalAbscissa : Complex) - (delta : Complex) -
          Complex.I * (gamma : Complex))) := by
    simp only [quartic, centered, eval_mul, eval_add, eval_sub, eval_pow,
      eval_X, eval_C]
    ring_nf
    simp [sub_eq_add_neg]
  have hRoots (s : Complex) : quartic.eval s = 0 ↔
      s = (criticalAbscissa : Complex) + (delta : Complex) +
          Complex.I * (gamma : Complex) ∨
      s = (criticalAbscissa : Complex) + (delta : Complex) -
          Complex.I * (gamma : Complex) ∨
      s = (criticalAbscissa : Complex) - (delta : Complex) +
          Complex.I * (gamma : Complex) ∨
      s = (criticalAbscissa : Complex) - (delta : Complex) -
          Complex.I * (gamma : Complex) := by
    rw [hFactor]
    simp only [mul_eq_zero, sub_eq_zero]
    tauto
  have hRightDistinct :
      (criticalAbscissa : Complex) + (delta : Complex) +
          Complex.I * (gamma : Complex) ≠
        (criticalAbscissa : Complex) + (delta : Complex) -
          Complex.I * (gamma : Complex) := by
    intro h
    have hIm := congrArg Complex.im h
    simp at hIm
    exact hGamma (by linarith)
  have hUpperDistinct :
      (criticalAbscissa : Complex) + (delta : Complex) +
          Complex.I * (gamma : Complex) ≠
        (criticalAbscissa : Complex) - (delta : Complex) +
          Complex.I * (gamma : Complex) := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    exact hDelta (by linarith)
  have hDiagonalDistinct :
      (criticalAbscissa : Complex) + (delta : Complex) +
          Complex.I * (gamma : Complex) ≠
        (criticalAbscissa : Complex) - (delta : Complex) -
          Complex.I * (gamma : Complex) := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    exact hDelta (by linarith)
  have hLowerDiagonalDistinct :
      (criticalAbscissa : Complex) + (delta : Complex) -
          Complex.I * (gamma : Complex) ≠
        (criticalAbscissa : Complex) - (delta : Complex) +
          Complex.I * (gamma : Complex) := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    exact hDelta (by linarith)
  have hLowerDistinct :
      (criticalAbscissa : Complex) + (delta : Complex) -
          Complex.I * (gamma : Complex) ≠
        (criticalAbscissa : Complex) - (delta : Complex) -
          Complex.I * (gamma : Complex) := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    exact hDelta (by linarith)
  have hLeftDistinct :
      (criticalAbscissa : Complex) - (delta : Complex) +
          Complex.I * (gamma : Complex) ≠
        (criticalAbscissa : Complex) - (delta : Complex) -
          Complex.I * (gamma : Complex) := by
    intro h
    have hIm := congrArg Complex.im h
    simp at hIm
    exact hGamma (by linarith)
  have hCard :
      ({(criticalAbscissa : Complex) + (delta : Complex) +
            Complex.I * (gamma : Complex),
          (criticalAbscissa : Complex) + (delta : Complex) -
            Complex.I * (gamma : Complex),
          (criticalAbscissa : Complex) - (delta : Complex) +
            Complex.I * (gamma : Complex),
          (criticalAbscissa : Complex) - (delta : Complex) -
            Complex.I * (gamma : Complex)} : Finset Complex).card = 4 := by
    norm_num [hRightDistinct, hUpperDistinct, hDiagonalDistinct,
      hLowerDiagonalDistinct, hLowerDistinct, hLeftDistinct]
  have hReflection (s : Complex) :
      quartic.eval (1 - s) = quartic.eval s := by
    simp only [quartic, centered, eval_mul, eval_add, eval_sub, eval_pow,
      eval_X, eval_C, criticalAbscissa]
    norm_num
    ring
  have hConjugation (s : Complex) :
      quartic.eval (conj s) = conj (quartic.eval s) := by
    simp only [quartic, centered, eval_mul, eval_add, eval_sub, eval_pow,
      eval_X, eval_C, map_mul, map_add, map_sub, map_pow]
    simp
  have hOffLine (s : Complex) (hs : quartic.eval s = 0) :
      s.re ≠ criticalAbscissa := by
    rcases (hRoots s).1 hs with h | h | h | h <;> rw [h] <;>
      simp only [Complex.add_re, Complex.sub_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    all_goals
      intro hEq
      apply hDelta
      linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact quartic.differentiable
  · exact hRoots
  · exact hCard
  · exact hReflection
  · exact hConjugation
  · exact hOffLine
  · intro hLocalized
    let root : Complex :=
      (criticalAbscissa : Complex) + (delta : Complex) +
        Complex.I * (gamma : Complex)
    have hRoot : quartic.eval root = 0 := by
      apply (hRoots root).2
      exact Or.inl rfl
    exact hOffLine root hRoot (hLocalized root hRoot)

#print axioms symmetric_off_line_quartic_spec

end D5.S3.Zeros.ToySpectrum.SymmetricOffLineQuartic
