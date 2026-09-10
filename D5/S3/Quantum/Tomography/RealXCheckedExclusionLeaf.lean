/- GID: D5/S3/Quantum/Tomography/RealXCheckedExclusionLeaf
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/RealXCheckedExclusionLeaf
   mirror-E: none(waiver:single-numeric-leaf-not-full-cover)
   anchors: []
   digest: A literal rational interval expression bounds the actual first seed residual on a positive-volume Cayley box, without an assumed numerical enclosure. -/

import D5.S0.Certificates.RationalIntervalExpression
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/- The matrix seed used by the existing verifier has first column
   (b,1,1,conj(e),1,1), b=(-3+4i)/5, e=(-2+i*sqrt(21))/5.
   Its adjoint measurement is therefore conj(b)+u1+u2+e*u3+u4+u5.
   Only this column is used: no second public matrix-seed carrier is defined.
   The 76 local rational annotations below are checked from literal data.
   This is ONE real, positive-volume exclusion leaf, not the complete atlas
   or the millions of nodes in the previously executed external cover.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Tomography.RealXCheckedExclusionLeaf

open D5.S0.Certificates.RationalIntervalExpression

private def seedBox : Fin 6 → ℚ × ℚ :=
  Fin.cases (4, 5) (fun _ : Fin 5 ↦ (-1 / 1024, 1 / 1024))

private def seedLeaf : Expr 6 :=
  let e0 : Expr 6 := .const (-3 / 5 : ℚ) (-3 / 5 : ℚ) (-3 / 5 : ℚ)
  let e1 : Expr 6 := .const (1 : ℚ) (1 : ℚ) (1 : ℚ)
  let e2 : Expr 6 := .input 1 (-1 / 1024 : ℚ) (1 / 1024 : ℚ)
  let e3 : Expr 6 := .square (0 : ℚ) (1 / 1048576 : ℚ) e2
  let e4 : Expr 6 := .neg (-1 / 1048576 : ℚ) (0 : ℚ) e3
  let e5 : Expr 6 := .add (1048575 / 1048576 : ℚ) (1 : ℚ) e1 e4
  let e6 : Expr 6 := .add (1 : ℚ) (1048577 / 1048576 : ℚ) e1 e3
  let e7 : Expr 6 := .inv (1048575 / 1048576 : ℚ) (1 : ℚ) e6
  let e8 : Expr 6 := .mul (524287 / 524288 : ℚ) (1 : ℚ) e5 e7
  let e9 : Expr 6 := .add (104857 / 262144 : ℚ) (419431 / 1048576 : ℚ) e0 e8
  let e10 : Expr 6 := .input 2 (-1 / 1024 : ℚ) (1 / 1024 : ℚ)
  let e11 : Expr 6 := .square (0 : ℚ) (1 / 1048576 : ℚ) e10
  let e12 : Expr 6 := .neg (-1 / 1048576 : ℚ) (0 : ℚ) e11
  let e13 : Expr 6 := .add (1048575 / 1048576 : ℚ) (1 : ℚ) e1 e12
  let e14 : Expr 6 := .add (1 : ℚ) (1048577 / 1048576 : ℚ) e1 e11
  let e15 : Expr 6 := .inv (1048575 / 1048576 : ℚ) (1 : ℚ) e14
  let e16 : Expr 6 := .mul (524287 / 524288 : ℚ) (1 : ℚ) e13 e15
  let e17 : Expr 6 := .add (734001 / 524288 : ℚ) (1468007 / 1048576 : ℚ) e9 e16
  let e18 : Expr 6 := .const (-2 / 5 : ℚ) (-2 / 5 : ℚ) (-2 / 5 : ℚ)
  let e19 : Expr 6 := .input 3 (-1 / 1024 : ℚ) (1 / 1024 : ℚ)
  let e20 : Expr 6 := .square (0 : ℚ) (1 / 1048576 : ℚ) e19
  let e21 : Expr 6 := .neg (-1 / 1048576 : ℚ) (0 : ℚ) e20
  let e22 : Expr 6 := .add (1048575 / 1048576 : ℚ) (1 : ℚ) e1 e21
  let e23 : Expr 6 := .add (1 : ℚ) (1048577 / 1048576 : ℚ) e1 e20
  let e24 : Expr 6 := .inv (1048575 / 1048576 : ℚ) (1 : ℚ) e23
  let e25 : Expr 6 := .mul (524287 / 524288 : ℚ) (1 : ℚ) e22 e24
  let e26 : Expr 6 := .mul (-419431 / 1048576 : ℚ) (-419429 / 1048576 : ℚ) e18 e25
  let e27 : Expr 6 := .input 0 (4 : ℚ) (5 : ℚ)
  let e28 : Expr 6 := .const (1 / 5 : ℚ) (1 / 5 : ℚ) (1 / 5 : ℚ)
  let e29 : Expr 6 := .mul (209715 / 262144 : ℚ) (1 : ℚ) e27 e28
  let e30 : Expr 6 := .const (2 : ℚ) (2 : ℚ) (2 : ℚ)
  let e31 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e30 e19
  let e32 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e31 e24
  let e33 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e29 e32
  let e34 : Expr 6 := .neg (-1 / 512 : ℚ) (1 / 512 : ℚ) e33
  let e35 : Expr 6 := .add (-421479 / 1048576 : ℚ) (-417381 / 1048576 : ℚ) e26 e34
  let e36 : Expr 6 := .add (1046523 / 1048576 : ℚ) (525313 / 524288 : ℚ) e17 e35
  let e37 : Expr 6 := .input 4 (-1 / 1024 : ℚ) (1 / 1024 : ℚ)
  let e38 : Expr 6 := .square (0 : ℚ) (1 / 1048576 : ℚ) e37
  let e39 : Expr 6 := .neg (-1 / 1048576 : ℚ) (0 : ℚ) e38
  let e40 : Expr 6 := .add (1048575 / 1048576 : ℚ) (1 : ℚ) e1 e39
  let e41 : Expr 6 := .add (1 : ℚ) (1048577 / 1048576 : ℚ) e1 e38
  let e42 : Expr 6 := .inv (1048575 / 1048576 : ℚ) (1 : ℚ) e41
  let e43 : Expr 6 := .mul (524287 / 524288 : ℚ) (1 : ℚ) e40 e42
  let e44 : Expr 6 := .add (2095097 / 1048576 : ℚ) (1049601 / 524288 : ℚ) e36 e43
  let e45 : Expr 6 := .input 5 (-1 / 1024 : ℚ) (1 / 1024 : ℚ)
  let e46 : Expr 6 := .square (0 : ℚ) (1 / 1048576 : ℚ) e45
  let e47 : Expr 6 := .neg (-1 / 1048576 : ℚ) (0 : ℚ) e46
  let e48 : Expr 6 := .add (1048575 / 1048576 : ℚ) (1 : ℚ) e1 e47
  let e49 : Expr 6 := .add (1 : ℚ) (1048577 / 1048576 : ℚ) e1 e46
  let e50 : Expr 6 := .inv (1048575 / 1048576 : ℚ) (1 : ℚ) e49
  let e51 : Expr 6 := .mul (524287 / 524288 : ℚ) (1 : ℚ) e48 e50
  let e52 : Expr 6 := .add (3143671 / 1048576 : ℚ) (1573889 / 524288 : ℚ) e44 e51
  let e53 : Expr 6 := .square (4712423 / 524288 : ℚ) (9449489 / 1048576 : ℚ) e52
  let e54 : Expr 6 := .const (-4 / 5 : ℚ) (-4 / 5 : ℚ) (-4 / 5 : ℚ)
  let e55 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e30 e2
  let e56 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e55 e7
  let e57 : Expr 6 := .add (-840909 / 1048576 : ℚ) (-209203 / 262144 : ℚ) e54 e56
  let e58 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e30 e10
  let e59 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e58 e15
  let e60 : Expr 6 := .add (-842957 / 1048576 : ℚ) (-208691 / 262144 : ℚ) e57 e59
  let e61 : Expr 6 := .mul (-205 / 262144 : ℚ) (205 / 262144 : ℚ) e18 e32
  let e62 : Expr 6 := .mul (419429 / 524288 : ℚ) (1 : ℚ) e29 e25
  let e63 : Expr 6 := .add (419019 / 524288 : ℚ) (262349 / 262144 : ℚ) e61 e62
  let e64 : Expr 6 := .add (-4919 / 1048576 : ℚ) (26829 / 131072 : ℚ) e60 e63
  let e65 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e30 e37
  let e66 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e65 e42
  let e67 : Expr 6 := .add (-6967 / 1048576 : ℚ) (27085 / 131072 : ℚ) e64 e66
  let e68 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e30 e45
  let e69 : Expr 6 := .mul (-1 / 512 : ℚ) (1 / 512 : ℚ) e68 e50
  let e70 : Expr 6 := .add (-9015 / 1048576 : ℚ) (27341 / 131072 : ℚ) e67 e69
  let e71 : Expr 6 := .square (0 : ℚ) (22813 / 524288 : ℚ) e70
  let e72 : Expr 6 := .add (4712423 / 524288 : ℚ) (9495115 / 1048576 : ℚ) e53 e71
  let e73 : Expr 6 := .const (6 : ℚ) (6 : ℚ) (6 : ℚ)
  let e74 : Expr 6 := .neg (-6 : ℚ) (-6 : ℚ) e73
  let e75 : Expr 6 := .add (2 : ℚ) (4 : ℚ) e72 e74
  e75

set_option maxRecDepth 8192 in
private theorem seedLeaf_checked : check seedBox seedLeaf = true := by
  decide +kernel

private abbrev phase (t : ℝ) : ℂ :=
  ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩

private theorem seedLeaf_value (s : ℝ) (t : Fin 5 → ℝ) :
    value (Fin.cases s t) seedLeaf =
      Complex.normSq
        ((⟨-3 / 5, -4 / 5⟩ : ℂ) + phase (t 0) + phase (t 1) +
          (⟨-2 / 5, s / 5⟩ : ℂ) * phase (t 2) + phase (t 3) + phase (t 4)) - 6 := by
  norm_num [seedLeaf, value, phase, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    div_eq_mul_inv] <;>
    dsimp [Fin.cases, Fin.induction, Fin.induction.go] <;> ring

/-- The actual first residual of the exact Q(i,sqrt(21)) seed is in [2,4]
on the whole all-positive Cayley box with each free coordinate in
[-1/1024,1/1024]. The desired real enclosure is derived from the literal
rational checker, not supplied as a premise. In particular this box contains
no point of the all-six residual sublevel with tolerance 1/64.

This theorem supplies one `LocalStep.excluded` premise to FiniteSublevelCover.
It does not assert that the entire external traversal has been reflected. -/
theorem origin_chart_first_seed_residual_enclosed
    (t : Fin 5 → ℝ)
    (ht : ∀ i, -(1 / 1024 : ℝ) ≤ t i ∧ t i ≤ (1 / 1024 : ℝ)) :
    let c : ℝ → ℂ := fun q ↦
      ⟨(1 - q ^ 2) / (1 + q ^ 2), 2 * q / (1 + q ^ 2)⟩
    let z : ℂ := (⟨-3 / 5, -4 / 5⟩ : ℂ) + c (t 0) + c (t 1) +
      (⟨-2 / 5, Real.sqrt 21 / 5⟩ : ℂ) * c (t 2) + c (t 3) + c (t 4)
    (2 : ℝ) ≤ Complex.normSq z - 6 ∧ Complex.normSq z - 6 ≤ (4 : ℝ) := by
  have hs : (4 : ℝ) ≤ Real.sqrt 21 ∧ Real.sqrt 21 ≤ (5 : ℝ) := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)
    have hnonneg := Real.sqrt_nonneg (21 : ℝ)
    constructor <;> nlinarith
  have hx : ∀ i : Fin 6,
      ((seedBox i).1 : ℝ) ≤ Fin.cases (Real.sqrt 21) t i ∧
        Fin.cases (Real.sqrt 21) t i ≤ ((seedBox i).2 : ℝ) := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change (4 : ℝ) ≤ Real.sqrt 21 ∧ Real.sqrt 21 ≤ (5 : ℝ)
      exact hs
    · change (((-1 / 1024 : ℚ) : ℝ) ≤ t j ∧ t j ≤ ((1 / 1024 : ℚ) : ℝ))
      have hj := ht j
      norm_num at hj ⊢
      exact hj
  have h := checked_expression_encloses seedBox (Fin.cases (Real.sqrt 21) t)
    hx seedLeaf seedLeaf_checked
  change (2 : ℝ) ≤ value (Fin.cases (Real.sqrt 21) t) seedLeaf ∧
    value (Fin.cases (Real.sqrt 21) t) seedLeaf ≤ (4 : ℝ) at h
  rw [seedLeaf_value] at h
  exact h

#print axioms origin_chart_first_seed_residual_enclosed

end D5.S3.Quantum.Tomography.RealXCheckedExclusionLeaf
