/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumFormula
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factored scaled forms of the five Schur polynomials. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumData
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumFormulas

/-! The five cleared Schur-complement polynomials. Scaled formulas are stated
over arbitrary rings so integer packing and real evaluation use the same expression. -/

namespace RefinedBMV.ZeroSpectrum

inductive SignPolynomial where
  | A | B | P1 | P2 | P3

def SignPolynomial.groups : SignPolynomial → List Group
  | .A => groupsA
  | .B => groupsB
  | .P1 => groupsP1
  | .P2 => groupsP2
  | .P3 => groupsP3

def SignPolynomial.denominator : SignPolynomial → ℕ
  | .A | .B => 4
  | .P1 | .P2 => 48
  | .P3 => 96

/-- Three times the determinant table clears the denominators of the individual
factored terms. The other four tables already use their factored denominators. -/
def SignPolynomial.multiplier : SignPolynomial → ℕ
  | .P3 => 3
  | _ => 1

def scaledFormula {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ]
    [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4] [OfNat R 6] [OfNat R 8]
    (k : SignPolynomial) (x b y : R) : R :=
  let p := x + 1
  let q := p + 1
  let C2 := q*(q+1)
  let D4 := q*(q+2)
  let N6 := q*(q+1)*(q+2)
  let w := 1-b
  let Rr := 1+y^4
  let s := 1-b*y^8
  let u := 1-(p+2)*b*y^8+q*b^2*y^8
  let v := q-(p+2)*b+b^2*y^8
  let f6 := 6-3*(p+2)*(p+3)*b*y^8+6*q*(p+3)*b^2*y^8-
    3*C2*b^3*y^8-N6*y^6*w^3
  let j6 := 3*C2-6*q*(p+3)*b+3*(p+2)*(p+3)*b^2-
    6*b^3*y^8-N6*y^2*w^3
  let g6 := 6*q-6*(p+3)*b+6*(p+3)*b^2*y^8-6*q*b^3*y^8-N6*y^4*w^3
  let a4 := 4*u*Rr-2*q*y^4*s*w-D4*y^5*w^2*Rr
  let b4 := 4*v*Rr-2*q*s*w-D4*y^4*w^2*Rr
  let z := s*Rr^2
  match k with
  | .A => 4*u*Rr^2-4*s^2-D4*y^8*w^2*Rr^2
  | .B => 4*v*Rr^2-4*s^2-D4*y^2*w^2*Rr^2
  | .P1 => 8*f6*z-3*a4^2
  | .P2 => 8*j6*z-3*b4^2
  | .P3 => 2*(4*f6*j6-g6^2)*z-3*j6*a4^2-3*f6*b4^2+3*g6*a4*b4

noncomputable section

open RefinedBMV.ThreeBlockGram.ZeroSpectrum

def SignPolynomial.closed (k : SignPolynomial) (p b y : ℝ) : ℝ :=
  match k with
  | .A => Astar p b y
  | .B => Bstar p b y
  | .P1 => ThreeBlockGram.ZeroSpectrum.P1 p b y
  | .P2 => ThreeBlockGram.ZeroSpectrum.P2 p b y
  | .P3 => ThreeBlockGram.ZeroSpectrum.P3 p b y

/-- Factored scaling identities, with denominators exactly as in the oracle certificate. -/
theorem scaledFormula_eq (k : SignPolynomial) (p b y : ℝ) :
    scaledFormula k (p-1) b y =
      ((k.multiplier : ℝ) * (k.denominator : ℝ)) * k.closed p b y := by
  have hp : p - 1 + 1 = p := by ring
  -- Keep the geometric numerators factored while identifying their scalar multiples.
  have hf : 6*fNum p b y =
      6-3*(p+2)*(p+3)*b*y^8+6*q p*(p+3)*b^2*y^8-
      3*(q p*(q p+1))*b^3*y^8-(q p*(q p+1)*(q p+2))*y^6*(w b)^3 := by
    unfold fNum C N
    ring
  have hj : 6*jNum p b y =
      3*(q p*(q p+1))-6*q p*(p+3)*b+3*(p+2)*(p+3)*b^2-
      6*b^3*y^8-(q p*(q p+1)*(q p+2))*y^2*(w b)^3 := by
    unfold jNum C N
    ring
  have hg : 6*gNum p b y =
      6*q p-6*(p+3)*b+6*(p+3)*b^2*y^8-6*q p*b^3*y^8-
      (q p*(q p+1)*(q p+2))*y^4*(w b)^3 := by
    unfold gNum N
    ring
  have ha : 4*alpha p b y =
      4*u p b y*R y-2*q p*y^4*s b y*w b-(q p*(q p+2))*y^5*(w b)^2*R y := by
    unfold alpha c D
    ring
  have hb : 4*beta p b y =
      4*v p b y*R y-2*q p*s b y*w b-(q p*(q p+2))*y^4*(w b)^2*R y := by
    unfold beta c D
    ring
  cases k <;>
    simp only [scaledFormula, hp, SignPolynomial.closed, SignPolynomial.multiplier,
      SignPolynomial.denominator, Nat.cast_ofNat, Nat.cast_one]
  · unfold Astar D u w R s q
    ring
  · unfold Bstar D v w R s q
    ring
  · change 8 * (6-3*(p+2)*(p+3)*b*y^8+6*q p*(p+3)*b^2*y^8-
      3*(q p*(q p+1))*b^3*y^8-(q p*(q p+1)*(q p+2))*y^6*(w b)^3)*z b y -
      3*(4*u p b y*R y-2*q p*y^4*s b y*w b-(q p*(q p+2))*y^5*(w b)^2*R y)^2 = _
    rw [← hf, ← ha]
    unfold P1
    ring
  · change 8 * (3*(q p*(q p+1))-6*q p*(p+3)*b+3*(p+2)*(p+3)*b^2-
      6*b^3*y^8-(q p*(q p+1)*(q p+2))*y^2*(w b)^3)*z b y -
      3*(4*v p b y*R y-2*q p*s b y*w b-(q p*(q p+2))*y^4*(w b)^2*R y)^2 = _
    rw [← hj, ← hb]
    unfold P2
    ring
  · change 2*(4*(6-3*(p+2)*(p+3)*b*y^8+6*q p*(p+3)*b^2*y^8-
      3*(q p*(q p+1))*b^3*y^8-(q p*(q p+1)*(q p+2))*y^6*(w b)^3)*
      (3*(q p*(q p+1))-6*q p*(p+3)*b+3*(p+2)*(p+3)*b^2-
      6*b^3*y^8-(q p*(q p+1)*(q p+2))*y^2*(w b)^3)-
      (6*q p-6*(p+3)*b+6*(p+3)*b^2*y^8-6*q p*b^3*y^8-
      (q p*(q p+1)*(q p+2))*y^4*(w b)^3)^2)*z b y -
      3*(3*(q p*(q p+1))-6*q p*(p+3)*b+3*(p+2)*(p+3)*b^2-
      6*b^3*y^8-(q p*(q p+1)*(q p+2))*y^2*(w b)^3)*
      (4*u p b y*R y-2*q p*y^4*s b y*w b-(q p*(q p+2))*y^5*(w b)^2*R y)^2 -
      3*(6-3*(p+2)*(p+3)*b*y^8+6*q p*(p+3)*b^2*y^8-
      3*(q p*(q p+1))*b^3*y^8-(q p*(q p+1)*(q p+2))*y^6*(w b)^3)*
      (4*v p b y*R y-2*q p*s b y*w b-(q p*(q p+2))*y^4*(w b)^2*R y)^2 +
      3*(6*q p-6*(p+3)*b+6*(p+3)*b^2*y^8-6*q p*b^3*y^8-
      (q p*(q p+1)*(q p+2))*y^4*(w b)^3)*
      (4*u p b y*R y-2*q p*y^4*s b y*w b-(q p*(q p+2))*y^5*(w b)^2*R y)*
      (4*v p b y*R y-2*q p*s b y*w b-(q p*(q p+2))*y^4*(w b)^2*R y) = _
    rw [← hf, ← hj, ← hg, ← ha, ← hb]
    unfold P3
    ring

end
end RefinedBMV.ZeroSpectrum
