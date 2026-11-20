/- GID: D5/S3/Quantum/Algebra/Polynomials/ComplexPolynomialCoefficients
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Polynomials/ComplexPolynomialCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Eval]
   utility: none
   digest: Real and imaginary coefficient projections commute with evaluation on real inputs. -/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Basic.Complex.Basic

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.Polynomials.ComplexPolynomialCoefficients

open MvPolynomial

/-- Take the real part of every coefficient. -/
def realCoeff {σ : Type*} (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange Complex.re (by simp)
    (AddMonoidAlgebra.coeff p))

/-- Take the imaginary part of every coefficient. -/
def imagCoeff {σ : Type*} (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange Complex.im (by simp)
    (AddMonoidAlgebra.coeff p))

/-- Reconstruct a complex polynomial from its two real coefficient projections. -/
lemma coefficient_split {σ : Type*} (p : MvPolynomial σ ℂ) :
    map Complex.ofRealHom (realCoeff p) +
      C Complex.I * map Complex.ofRealHom (imagCoeff p) = p := by
  ext m
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, coeff_map]
  change ((p.coeff m).re : ℂ) + Complex.I * (p.coeff m).im = p.coeff m
  simpa only [mul_comm] using Complex.re_add_im (p.coeff m)

/-- The coefficient projections give the real and imaginary parts of evaluation at real inputs. -/
lemma coefficient_eval {σ : Type*} (p : MvPolynomial σ ℂ) (x : σ → ℝ) :
    eval x (realCoeff p) = (eval (fun i => (x i : ℂ)) p).re ∧
    eval x (imagCoeff p) = (eval (fun i => (x i : ℂ)) p).im := by
  have h := congrArg (eval (fun i => (x i : ℂ))) (coefficient_split p)
  have hcast (q : MvPolynomial σ ℝ) :
      eval (fun i => (x i : ℂ)) (map Complex.ofRealHom q) = (eval x q : ℂ) :=
    (MvPolynomial.map_eval Complex.ofRealHom x q).symm
  simp only [map_add, map_mul, eval_C, hcast] at h
  constructor
  · simpa using congrArg Complex.re h
  · simpa using congrArg Complex.im h

end D5.S3.Quantum.Algebra.Polynomials.ComplexPolynomialCoefficients
