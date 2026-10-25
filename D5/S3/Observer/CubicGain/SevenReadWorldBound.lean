/- GID: D5/S3/Observer/CubicGain/SevenReadWorldBound
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/SevenReadWorldBound
   mirror-E: none(waiver:seven-read-complete-world-fiber)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Roots]
   utility: none
   digest: Root multiplicity bounds complete original seven-reading worlds at each positive source width. -/

import D5.S3.Observer.CubicGain.FullWorldMeanSpan
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace D5.S3.Observer.CubicGain.SevenReadWorldBound
open D5.S3.Observer.CubicGain Polynomial

/-- False selects J and true selects M at the sixth action. -/
def sevenProduct (e : Bool) (i : ℕ) : Mat :=
  ([actionJ,actionM,actionJ,actionM,actionJ,
    if e then actionM else actionJ].take i).foldl (fun Q E => E*Q) 1

/-- Original clocks and one fixed complete world in every row. -/
def sevenRead (e : Bool) (W : OriginalWorld) (i : ℕ) : ℝ :=
  W.2.2.1 + (originalPolynomial W).eval i *
    Matrix.trace (sevenProduct e i * sourceMatrix W.1 W.2.1)

/-- The entire literal fiber at one specified positive width. -/
def sevenFiber (e : Bool) (b A C z Y p v : ℝ) : Set OriginalWorld :=
  {W | FullWorldMeanSpan.FullWorld W ∧ W.2.1=b ∧
    ∀ i : Fin 7, sevenRead e W i = (![0,A,C,z,Y,p,v] : Fin 7 → ℝ) i}

def sixthIndex (e : Bool) : ℝ := if e then 3 else 2

def interpolationDenominator (e : Bool) (b : ℝ) : ℝ :=
  16*(1+b)*(1+2*b)*(1+sixthIndex e*b)

/-- Even interpolation numerators, as polynomials in the drift. -/
def evenNumerators (e : Bool) (b C Y v : ℝ) : Fin 4 → Polynomial ℝ :=
  let T := 1+b
  let U := 1+2*b
  let V := 1+sixthIndex e*b
  ![-X*Polynomial.C (T*U*V), (Polynomial.C C-X)*Polynomial.C (U*V),
    (Polynomial.C Y-X)*Polynomial.C (T*V), (Polynomial.C v-X)*Polynomial.C (T*U)]

def oddNumerators (e : Bool) (b C Y v : ℝ) : Fin 3 → Polynomial ℝ :=
  let B := evenNumerators e b C Y v
  ![5*B 0+15*B 1-5*B 2+B 3,
    -B 0+9*B 1+9*B 2-B 3, B 0-5*B 1+15*B 2+5*B 3]

/-- The native elimination polynomial retains odd sampled zeros. -/
def driftPolynomial (e : Bool) (b A C z Y p v : ℝ) : Polynomial ℝ :=
  let G := oddNumerators e b C Y v
  (Polynomial.C A-X)*G 1*G 2-2*(Polynomial.C z-X)*G 0*G 2+
    (Polynomial.C p-X)*G 0*G 1

end D5.S3.Observer.CubicGain.SevenReadWorldBound
