/- GID: D5/S3/Zeros/Symmetry/SignedZeckendorfOrbitCode
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/SignedZeckendorfOrbitCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realize the three zero symmetries as two sign-bit flips with fixed W data. -/

import D5.S0.Conventions.WDigits
import Mathlib.Data.Sign.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/-!
Library-search audit trail (2026-09-03):
* D5 searches for the three named sign flips, signed zero codes, and code bodies
  combining `SignType.sign` with `wEncoding` found no whole-statement owner.
* The frozen zero-symmetry modules own the complex and index actions and the
  four-point orbit count, but none constructs the source's signed W code.
* Pinned Mathlib supplies `SignType.sign`, `Left.sign_neg`, absolute-value
  negation, complex coordinate laws, and golden-ratio powers. It has no theorem
  packaging these source-specific code transformations.
* A search of all other installed Lean packages with the same names and body
  shapes found no exact theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Symmetry.SignedZeckendorfOrbitCode

open D5.S0.Conventions
open scoped ComplexConjugate

/-- Conjugation flips only the height sign, conjugate reflection flips only
the transverse sign, and reflection flips both signs in the source's orbit
code. The two unsigned magnitude words and the multiplicity word stay fixed.
When both centered coordinates are nonzero, the four orbit codes are exactly
the four listed sign states and are pairwise distinct. -/
theorem klein_actions_two_sign_bits (delta gamma : Real) (N multiplicity : Nat) :
    let rho : Complex := (1 / 2 : Complex) + delta + Complex.I * gamma
    let unsignedThread : Real -> WDigitString := fun x =>
      wEncoding ⌊Real.goldenRatio ^ N * |x|⌋₊
    let code : Complex ->
        SignType × WDigitString × SignType × WDigitString × WDigitString := fun z =>
      (SignType.sign (z.re - 1 / 2), unsignedThread (z.re - 1 / 2),
        SignType.sign z.im, unsignedThread z.im, wEncoding multiplicity)
    let states : List
        (SignType × WDigitString × SignType × WDigitString × WDigitString) :=
      [(SignType.sign delta, unsignedThread delta,
          SignType.sign gamma, unsignedThread gamma, wEncoding multiplicity),
        (SignType.sign delta, unsignedThread delta,
          -SignType.sign gamma, unsignedThread gamma, wEncoding multiplicity),
        (-SignType.sign delta, unsignedThread delta,
          SignType.sign gamma, unsignedThread gamma, wEncoding multiplicity),
        (-SignType.sign delta, unsignedThread delta,
          -SignType.sign gamma, unsignedThread gamma, wEncoding multiplicity)]
    let orbitCodes : List
        (SignType × WDigitString × SignType × WDigitString × WDigitString) :=
      [code rho, code (conj rho), code (1 - conj rho), code (1 - rho)]
    code (conj rho) =
        (SignType.sign delta, unsignedThread delta,
          -SignType.sign gamma, unsignedThread gamma, wEncoding multiplicity) ∧
      code (1 - conj rho) =
        (-SignType.sign delta, unsignedThread delta,
          SignType.sign gamma, unsignedThread gamma, wEncoding multiplicity) ∧
      code (1 - rho) =
        (-SignType.sign delta, unsignedThread delta,
          -SignType.sign gamma, unsignedThread gamma, wEncoding multiplicity) ∧
      orbitCodes = states ∧
      (delta ≠ 0 -> gamma ≠ 0 -> orbitCodes.Nodup) := by
  dsimp only
  constructor
  · congr 1 <;> simp [Left.sign_neg]
  constructor
  · congr 1 <;> simp
    all_goals ring_nf
    all_goals simp [Left.sign_neg]
  constructor
  · congr 1 <;> simp <;> ring_nf <;> simp [Left.sign_neg]
  constructor
  · congr 1 <;> simp
    all_goals ring_nf
    all_goals simp [Left.sign_neg]
  · intro hdelta hgamma
    have hsd : SignType.sign delta ≠ 0 := sign_ne_zero.mpr hdelta
    have hsg : SignType.sign gamma ≠ 0 := sign_ne_zero.mpr hgamma
    have hsdNeg : SignType.sign delta ≠ -SignType.sign delta := by
      intro heq
      exact hsd (SignType.self_eq_neg_iff.mp heq)
    have hsgNeg : SignType.sign gamma ≠ -SignType.sign gamma := by
      intro heq
      exact hsg (SignType.self_eq_neg_iff.mp heq)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.one_re, Complex.one_im, Complex.sub_re,
      Complex.sub_im]
    norm_num
    ring_nf
    simp [Left.sign_neg, hsdNeg, hsgNeg]

-- The theorem has no global hypotheses; this checks its empty context.
example : True := trivial

-- The four public source parameters have a concrete inhabitant.
example : Real × Real × Nat × Nat := (1, 1, 0, 1)

-- The generic nonzero conditions used by the final public clause are satisfiable.
example : (1 : Real) ≠ 0 ∧ (1 : Real) ≠ 0 := by norm_num

#print axioms klein_actions_two_sign_bits

end D5.S3.Zeros.Symmetry.SignedZeckendorfOrbitCode
