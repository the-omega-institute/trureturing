import D5.S3.Constants.NewtonHankelRealRootCriterion
import D5.S3.Zeros.CoefficientBounds.SexticDiscriminant

noncomputable section
open Matrix Polynomial
open scoped BigOperators

namespace ConstrainedGramProbe0909

-- B0: a signed identity, not a positivity assertion for complex roots.
example (m : Nat) (roots : Fin m -> Complex) (c : Fin m -> Real) :
    dotProduct c
        (D5.S3.Constants.NewtonHankelRealRootCriterion.newtonHankel roots *ᵥ c) =
      (∑ j, (D5.S3.Constants.NewtonHankelRealRootCriterion.vectorPolynomialValue
        c (roots j) ^ 2).re) / m := by
  exact D5.S3.Constants.NewtonHankelRealRootCriterion.companion_trace_hankel_quadratic_identity
    roots c

-- B1: completion of the square uses no root criterion.
example (a b u v : Real) :
    2*u^2 + 2*a*u*v + (a^2-2*b)*v^2 =
      2*(u+a*v/2)^2 + (a^2-4*b)/2*v^2 := by
  ring

example (B C b d : Real) :
    (4*B*C/15)^2-4*(3*b*d/5) =
      B^2*C^2/225 + (2/5)*B^2*(C^2/6-d) + (12/5)*d*(B^2/6-b) := by
  ring

example (B C b d : Real) (hd : 0 ≤ d)
    (hb : b ≤ B^2/6) (ht : d ≤ C^2/6) :
    0 ≤ (4*B*C/15)^2-4*(3*b*d/5) := by
  have h1 := sq_nonneg (B*C)
  have h2 := mul_nonneg (sq_nonneg B) (sub_nonneg.mpr ht)
  have h3 := mul_nonneg hd (sub_nonneg.mpr hb)
  have he : (4*B*C/15)^2-4*(3*b*d/5) =
      (B*C)^2/225 + (2/5)*(B^2*(C^2/6-d)) + (12/5)*(d*(B^2/6-b)) := by ring
  linarith only [h1, h2, h3, he]

-- B2: denominator-cleared Gram identity; dividing requires a positive pivot.
example (a b d u v w : Real) :
    3 * (2 * a^2 - 6 * b) *
      (3 * u^2 + 2 * a * u * v + 2 * (a^2 - 2 * b) * u * w +
        (a^2 - 2 * b) * v^2 + 2 * (a^3 - 3 * a * b + 3 * d) * v * w +
        (a^4 - 4 * a^2 * b + 2 * b^2 + 4 * a * d) * w^2) =
    (2 * a^2 - 6 * b) * (3 * u + a * v + (a^2 - 2 * b) * w)^2 +
      ((2 * a^2 - 6 * b) * v + (2 * a^3 - 7 * a * b + 9 * d) * w)^2 +
      3 * (a^2 * b^2 - 4 * b^3 - 4 * a^3 * d - 27 * d^2 + 18 * a * b * d) * w^2 := by
  ring

-- The existing root-dependent discriminant supplies that sign by direct binding.
example (r t : Fin 6 -> Real) (hr : ∑ i, r i = 0) (ht : ∑ i, t i = 0) :
    let p : Real[X] := ∏ i, (X-C (r i))
    let q : Real[X] := ∏ i, (X-C (t i))
    let A := -p.coeff 4
    let B := (p.coeff 4)^2+5*p.coeff 2
    let Z := -(2*p.coeff 0+2*p.coeff 4*p.coeff 2/15-(p.coeff 3)^2/20)
    let A' := -q.coeff 4
    let B' := (q.coeff 4)^2+5*q.coeff 2
    let Z' := -(2*q.coeff 0+2*q.coeff 4*q.coeff 2/15-(q.coeff 3)^2/20)
    let a := 24*A*A'/35
    let b := 2*B*B'/105
    let d := 4*Z*Z'/7
    0 ≤ a^2*b^2-4*b^3-4*a^3*d-27*d^2+18*a*b*d := by
  exact D5.S3.Zeros.CoefficientBounds.SexticDiscriminant.centered_real_sextic_discriminant
    r t hr ht

end ConstrainedGramProbe0909
