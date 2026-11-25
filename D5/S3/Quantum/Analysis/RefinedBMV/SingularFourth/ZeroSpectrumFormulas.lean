/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumFormulas
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar Schur polynomials for the singular spectral allocation. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The five scalar signs for the singular four-copy allocation

The variables are the degree `p`, the middle spectral value `r`, and the
independent root variable `y`. The allocation uses `y = r ^ (p / 8)`.
-/

noncomputable section

namespace RefinedBMV.ThreeBlockGram.ZeroSpectrum

def q (p : ℝ) : ℝ := p + 1
def c (p : ℝ) : ℝ := q p / 2
def C (p : ℝ) : ℝ := q p * (q p + 1) / 2
def D (p : ℝ) : ℝ := q p * (q p + 2) / 4
def N (p : ℝ) : ℝ := q p * (q p + 1) * (q p + 2) / 6
def w (r : ℝ) : ℝ := 1 - r
def R (y : ℝ) : ℝ := 1 + y^4
def root (p : ℕ) (r : ℝ) : ℝ := r ^ ((p : ℝ) / 8)

def s (r y : ℝ) : ℝ := 1 - r * y^8

def u (p r y : ℝ) : ℝ :=
  1 - (p + 2) * r * y^8 + q p * r^2 * y^8

def v (p r y : ℝ) : ℝ :=
  q p - (p + 2) * r + r^2 * y^8

def fNum (p r y : ℝ) : ℝ :=
  1 - (p + 2) * (p + 3) / 2 * r * y^8 + q p * (p + 3) * r^2 * y^8
    - C p * r^3 * y^8 - N p * y^6 * (w r)^3

def jNum (p r y : ℝ) : ℝ :=
  C p - q p * (p + 3) * r + (p + 2) * (p + 3) / 2 * r^2
    - r^3 * y^8 - N p * y^2 * (w r)^3

def gNum (p r y : ℝ) : ℝ :=
  q p - (p + 3) * r + (p + 3) * r^2 * y^8 - q p * r^3 * y^8
    - N p * y^4 * (w r)^3

def alpha (p r y : ℝ) : ℝ :=
  u p r y * R y - c p * y^4 * s r y * w r - D p * y^5 * (w r)^2 * R y

def beta (p r y : ℝ) : ℝ :=
  v p r y * R y - c p * s r y * w r - D p * y^4 * (w r)^2 * R y

def z (r y : ℝ) : ℝ := s r y * (R y)^2

def Astar (p r y : ℝ) : ℝ :=
  u p r y * (R y)^2 - (s r y)^2 - D p * y^8 * (w r)^2 * (R y)^2

def Bstar (p r y : ℝ) : ℝ :=
  v p r y * (R y)^2 - (s r y)^2 - D p * y^2 * (w r)^2 * (R y)^2

def P1 (p r y : ℝ) : ℝ := fNum p r y * z r y - (alpha p r y)^2
def P2 (p r y : ℝ) : ℝ := jNum p r y * z r y - (beta p r y)^2
def P3 (p r y : ℝ) : ℝ :=
  (fNum p r y * jNum p r y - (gNum p r y)^2 / 4) * z r y
    - jNum p r y * (alpha p r y)^2 - fNum p r y * (beta p r y)^2
    + gNum p r y * alpha p r y * beta p r y

/-- Equation (12), at independent arguments for the scalar certificate. -/
structure Signs (p r y : ℝ) : Prop where
  aStar : 0 ≤ Astar p r y
  bStar : 0 ≤ Bstar p r y
  p1 : 0 ≤ P1 p r y
  p2 : 0 ≤ P2 p r y
  p3 : 0 ≤ P3 p r y

end RefinedBMV.ThreeBlockGram.ZeroSpectrum
