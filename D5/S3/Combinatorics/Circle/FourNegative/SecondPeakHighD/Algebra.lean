/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Algebra
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Algebra
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Algebra and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD

variable {R : Type*} [CommRing R]

def Z (x q : R) : R := x*q
def T (x p q : R) : R := x*p*q
def Y (x p q h : R) : R := 2*h*T x p q
def A (x p q h : R) : R := 1+x+x*Y x p q h+x*Y x p q h*Z x q
def B (x p q h : R) : R := 1+T x p q+x*T x p q+x*Y x p q h*T x p q
def L (x p q : R) : R := 1+Z x q+Z x q*T x p q+x*Z x q*T x p q
def K (x p q h : R) : R := 1+Y x p q h+Y x p q h*Z x q+Y x p q h*Z x q*T x p q
def SU (x p q h : R) : R := 2*B x p q h-1
def SV (x p q : R) : R := 2*L x p q-1-Z x q
def SW (x p q h : R) : R := 2*K x p q h-1-Y x p q h-Y x p q h*Z x q
def C (x p q h : R) : R := 2*h*L x p q-A x p q h

def oldEnds (x p q h v m M : R) : Fin 4 → R :=
  ![2*v*A x p q h-2*K x p q h+2*m*L x p q,
    2*B x p q h-2*K x p q h+2*M*L x p q,
    2*B x p q h-2*L x p q,0]
def newEnds (x p q h v m M : R) (before : Bool) : Fin 4 → R :=
  ![4*v*A x p q h-2*SW x p q h+2*m*SV x p q-
      (if before then 0 else 2*A x p q h),
    2*SU x p q h-2*SW x p q h+2*M*SV x p q,
    2*SU x p q h-2*SV x p q,0]
def oldHeads (x p q h : R) : Fin 4 → R :=
  ![A x p q h,B x p q h,K x p q h,L x p q]
def newHeads (x p q h : R) : Fin 4 → R :=
  ![A x p q h,SU x p q h,SW x p q h,SV x p q]


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
