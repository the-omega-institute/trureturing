/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairResonanceAlgebra
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairResonanceAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete resonant tail quadratic and all 124 discriminant error terms. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants

/-! Source: four-prime-resonance-discriminant, supplied PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02, full symbolic certificate.
The 124-term error is retained without truncation. Every identity is
proved in the kernel over an arbitrary commutative ring, before imposing
positivity or prime conditions. Algebraic zero parameters are not graph
exponent examples. The necessary local test is not a root criterion. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace D5.S3.Combinatorics.SpectralGraph.PairResonanceAlgebra
open PairedIdealIntersectionObstructions
variable {R : Type*} [CommRing R]

def tailA (a b s : R) : R :=
  -1*a^3*b*s +
    4*a^3*b -
    1*a^3*s +
    2*a^3 -
    2*a^2*b^2*s +
    4*a^2*b^2 +
    a^2*b*s^2 -
    7*a^2*b*s +
    10*a^2*b +
    a^2*s^2 -
    5*a^2*s +
    5*a^2 -
    3*a*b^2*s +
    4*a*b^2 +
    2*a*b*s^2 -
    9*a*b*s +
    8*a*b +
    2*a*s^2 -
    6*a*s +
    4*a -
    1*b^2*s +
    b^2 +
    b*s^2 -
    3*b*s +
    2*b +
    s^2 -
    2*s +
    1

def tailB (a b s : R) : R :=
  4*a^4*b +
    2*a^4 -
    1*a^3*b^2*s +
    4*a^3*b^2 -
    7*a^3*b*s +
    16*a^3*b -
    6*a^3*s +
    9*a^3 +
    a^2*b^2*s^2 -
    7*a^2*b^2*s +
    10*a^2*b^2 +
    4*a^2*b*s^2 -
    25*a^2*b*s +
    25*a^2*b +
    6*a^2*s^2 -
    20*a^2*s +
    14*a^2 +
    2*a*b^2*s^2 -
    9*a*b^2*s +
    8*a*b^2 -
    1*a*b*s^3 +
    12*a*b*s^2 -
    28*a*b*s +
    17*a*b -
    2*a*s^3 +
    13*a*s^2 -
    20*a*s +
    9*a +
    b^2*s^2 -
    3*b^2*s +
    2*b^2 -
    1*b*s^3 +
    6*b*s^2 -
    9*b*s +
    4*b -
    2*s^3 +
    6*s^2 -
    6*s +
    2

def tailC (a b s : R) : R :=
  2*a^4*b +
    2*a^4 -
    1*a^3*b^2*s +
    2*a^3*b^2 -
    6*a^3*b*s +
    9*a^3*b -
    7*a^3*s +
    7*a^3 +
    a^2*b^2*s^2 -
    5*a^2*b^2*s +
    5*a^2*b^2 +
    6*a^2*b*s^2 -
    20*a^2*b*s +
    14*a^2*b +
    9*a^2*s^2 -
    18*a^2*s +
    9*a^2 +
    2*a*b^2*s^2 -
    6*a*b^2*s +
    4*a*b^2 -
    2*a*b*s^3 +
    13*a*b*s^2 -
    20*a*b*s +
    9*a*b -
    5*a*s^3 +
    15*a*s^2 -
    15*a*s +
    5*a +
    b^2*s^2 -
    2*b^2*s +
    b^2 -
    2*b*s^3 +
    6*b*s^2 -
    6*b*s +
    2*b +
    s^4 -
    4*s^3 +
    6*s^2 -
    4*s +
    1

def discriminant (a b s : R) : R := (tailB a b s)^2-4*tailA a b s*tailC a b s

def localPolynomial (s z : R) : R := (2*s-1)^2*z^2+2*s^2*(2*s-1)^2*z+s^4

def errorPolynomial (h z s : R) : R :=
  h^7*z^4*s^2 -
    8*h^7*z^4*s +
    16*h^7*z^4 +
    4*h^6*z^4*s^3 -
    40*h^6*z^4*s^2 +
    100*h^6*z^4*s -
    48*h^6*z^4 -
    4*h^6*z^3*s^2 +
    24*h^6*z^3*s -
    32*h^6*z^3 +
    6*h^5*z^4*s^4 -
    80*h^5*z^4*s^3 +
    240*h^5*z^4*s^2 -
    208*h^5*z^4*s +
    52*h^5*z^4 -
    16*h^5*z^3*s^3 +
    122*h^5*z^3*s^2 -
    224*h^5*z^3*s +
    112*h^5*z^3 +
    6*h^5*z^2*s^2 -
    24*h^5*z^2*s +
    16*h^5*z^2 +
    4*h^4*z^4*s^5 -
    80*h^4*z^4*s^4 +
    280*h^4*z^4*s^3 -
    336*h^4*z^4*s^2 +
    160*h^4*z^4*s -
    24*h^4*z^4 -
    24*h^4*z^3*s^4 +
    246*h^4*z^3*s^3 -
    576*h^4*z^3*s^2 +
    510*h^4*z^3*s -
    152*h^4*z^3 +
    24*h^4*z^2*s^3 -
    126*h^4*z^2*s^2 +
    148*h^4*z^2*s -
    64*h^4*z^2 -
    4*h^4*z*s^2 +
    8*h^4*z*s +
    h^3*z^4*s^6 -
    40*h^3*z^4*s^5 +
    160*h^3*z^4*s^4 -
    240*h^3*z^4*s^3 +
    164*h^3*z^4*s^2 -
    48*h^3*z^4*s +
    4*h^3*z^4 -
    16*h^3*z^3*s^5 +
    246*h^3*z^3*s^4 -
    704*h^3*z^3*s^3 +
    858*h^3*z^3*s^2 -
    482*h^3*z^3*s +
    100*h^3*z^3 +
    36*h^3*z^2*s^4 -
    258*h^3*z^2*s^3 +
    433*h^3*z^2*s^2 -
    328*h^3*z^2*s +
    104*h^3*z^2 -
    16*h^3*z*s^3 +
    46*h^3*z*s^2 -
    24*h^3*z*s +
    h^3*s^2 -
    8*h^2*z^4*s^6 +
    36*h^2*z^4*s^5 -
    64*h^2*z^4*s^4 +
    56*h^2*z^4*s^3 -
    24*h^2*z^4*s^2 +
    4*h^2*z^4*s -
    4*h^2*z^3*s^6 +
    122*h^2*z^3*s^5 -
    416*h^2*z^3*s^4 +
    634*h^2*z^3*s^3 -
    508*h^2*z^3*s^2 +
    204*h^2*z^3*s -
    32*h^2*z^3 +
    24*h^2*z^2*s^5 -
    258*h^2*z^2*s^4 +
    570*h^2*z^2*s^3 -
    600*h^2*z^2*s^2 +
    350*h^2*z^2*s -
    88*h^2*z^2 -
    24*h^2*z*s^4 +
    98*h^2*z*s^3 -
    98*h^2*z*s^2 +
    26*h^2*z*s +
    4*h^2*s^3 -
    2*h^2*s^2 +
    24*h*z^3*s^6 -
    96*h*z^3*s^5 +
    174*h*z^3*s^4 -
    178*h*z^3*s^3 +
    104*h*z^3*s^2 -
    32*h*z^3*s +
    4*h*z^3 +
    6*h*z^2*s^6 -
    126*h*z^2*s^5 +
    353*h*z^2*s^4 -
    472*h*z^2*s^3 +
    392*h*z^2*s^2 -
    194*h*z^2*s +
    41*h*z^2 -
    16*h*z*s^5 +
    98*h*z*s^4 -
    148*h*z*s^3 +
    78*h*z*s^2 -
    12*h*z*s +
    6*h*s^4 -
    6*h*s^3 +
    h*s^2 -
    24*z^2*s^6 +
    84*z^2*s^5 -
    136*z^2*s^4 +
    150*z^2*s^3 -
    118*z^2*s^2 +
    54*z^2*s -
    10*z^2 -
    4*z*s^6 +
    46*z*s^5 -
    98*z*s^4 +
    78*z*s^3 -
    24*z*s^2 +
    2*z*s +
    4*s^5 -
    6*s^4 +
    2*s^3

def normalizedError (P H U s : R) : R :=
  P^7*H^6*U^4*s^2 -
    8*P^7*H^6*U^4*s +
    16*P^7*H^6*U^4 -
    4*P^6*H^7*U^3*s^2 +
    24*P^6*H^7*U^3*s -
    32*P^6*H^7*U^3 +
    4*P^6*H^5*U^4*s^3 -
    40*P^6*H^5*U^4*s^2 +
    100*P^6*H^5*U^4*s -
    48*P^6*H^5*U^4 +
    6*P^5*H^8*U^2*s^2 -
    24*P^5*H^8*U^2*s +
    16*P^5*H^8*U^2 -
    16*P^5*H^6*U^3*s^3 +
    122*P^5*H^6*U^3*s^2 -
    224*P^5*H^6*U^3*s +
    112*P^5*H^6*U^3 +
    6*P^5*H^4*U^4*s^4 -
    80*P^5*H^4*U^4*s^3 +
    240*P^5*H^4*U^4*s^2 -
    208*P^5*H^4*U^4*s +
    52*P^5*H^4*U^4 -
    4*P^4*H^9*U*s^2 +
    8*P^4*H^9*U*s +
    24*P^4*H^7*U^2*s^3 -
    126*P^4*H^7*U^2*s^2 +
    148*P^4*H^7*U^2*s -
    64*P^4*H^7*U^2 -
    24*P^4*H^5*U^3*s^4 +
    246*P^4*H^5*U^3*s^3 -
    576*P^4*H^5*U^3*s^2 +
    510*P^4*H^5*U^3*s -
    152*P^4*H^5*U^3 +
    4*P^4*H^3*U^4*s^5 -
    80*P^4*H^3*U^4*s^4 +
    280*P^4*H^3*U^4*s^3 -
    336*P^4*H^3*U^4*s^2 +
    160*P^4*H^3*U^4*s -
    24*P^4*H^3*U^4 +
    P^3*H^10*s^2 -
    16*P^3*H^8*U*s^3 +
    46*P^3*H^8*U*s^2 -
    24*P^3*H^8*U*s +
    36*P^3*H^6*U^2*s^4 -
    258*P^3*H^6*U^2*s^3 +
    433*P^3*H^6*U^2*s^2 -
    328*P^3*H^6*U^2*s +
    104*P^3*H^6*U^2 -
    16*P^3*H^4*U^3*s^5 +
    246*P^3*H^4*U^3*s^4 -
    704*P^3*H^4*U^3*s^3 +
    858*P^3*H^4*U^3*s^2 -
    482*P^3*H^4*U^3*s +
    100*P^3*H^4*U^3 +
    P^3*H^2*U^4*s^6 -
    40*P^3*H^2*U^4*s^5 +
    160*P^3*H^2*U^4*s^4 -
    240*P^3*H^2*U^4*s^3 +
    164*P^3*H^2*U^4*s^2 -
    48*P^3*H^2*U^4*s +
    4*P^3*H^2*U^4 +
    4*P^2*H^9*s^3 -
    2*P^2*H^9*s^2 -
    24*P^2*H^7*U*s^4 +
    98*P^2*H^7*U*s^3 -
    98*P^2*H^7*U*s^2 +
    26*P^2*H^7*U*s +
    24*P^2*H^5*U^2*s^5 -
    258*P^2*H^5*U^2*s^4 +
    570*P^2*H^5*U^2*s^3 -
    600*P^2*H^5*U^2*s^2 +
    350*P^2*H^5*U^2*s -
    88*P^2*H^5*U^2 -
    4*P^2*H^3*U^3*s^6 +
    122*P^2*H^3*U^3*s^5 -
    416*P^2*H^3*U^3*s^4 +
    634*P^2*H^3*U^3*s^3 -
    508*P^2*H^3*U^3*s^2 +
    204*P^2*H^3*U^3*s -
    32*P^2*H^3*U^3 -
    8*P^2*H*U^4*s^6 +
    36*P^2*H*U^4*s^5 -
    64*P^2*H*U^4*s^4 +
    56*P^2*H*U^4*s^3 -
    24*P^2*H*U^4*s^2 +
    4*P^2*H*U^4*s +
    6*P*H^8*s^4 -
    6*P*H^8*s^3 +
    P*H^8*s^2 -
    16*P*H^6*U*s^5 +
    98*P*H^6*U*s^4 -
    148*P*H^6*U*s^3 +
    78*P*H^6*U*s^2 -
    12*P*H^6*U*s +
    6*P*H^4*U^2*s^6 -
    126*P*H^4*U^2*s^5 +
    353*P*H^4*U^2*s^4 -
    472*P*H^4*U^2*s^3 +
    392*P*H^4*U^2*s^2 -
    194*P*H^4*U^2*s +
    41*P*H^4*U^2 +
    24*P*H^2*U^3*s^6 -
    96*P*H^2*U^3*s^5 +
    174*P*H^2*U^3*s^4 -
    178*P*H^2*U^3*s^3 +
    104*P*H^2*U^3*s^2 -
    32*P*H^2*U^3*s +
    4*P*H^2*U^3 +
    4*H^7*s^5 -
    6*H^7*s^4 +
    2*H^7*s^3 -
    4*H^5*U*s^6 +
    46*H^5*U*s^5 -
    98*H^5*U*s^4 +
    78*H^5*U*s^3 -
    24*H^5*U*s^2 +
    2*H^5*U*s -
    24*H^3*U^2*s^6 +
    84*H^3*U^2*s^5 -
    136*H^3*U^2*s^4 +
    150*H^3*U^2*s^3 -
    118*H^3*U^2*s^2 +
    54*H^3*U^2*s -
    10*H^3*U^2

theorem tail_quadratic (a b c s : R) :
    (tensorK a b c-s • 1).det = tailA a b s*c^2+tailB a b s*c+tailC a b s := by
  rw [PairedIdealIntersectionDeterminants.det_tensorK_sub_scalar]
  unfold tailA tailB tailC
  ring

theorem root_discriminant (a b c s : R)
    (hr : (tensorK a b c-s • 1).det=0) :
    discriminant a b s = (2*tailA a b s*c+tailB a b s)^2 := by
  rw [tail_quadratic] at hr
  unfold discriminant
  linear_combination -4*tailA a b s*hr

theorem discriminant_expansion (h z s : R) :
    discriminant (s-1+h) (-h+h^2*z) s =
      h^6*(s-1)^2*localPolynomial s z+h^7*errorPolynomial h z s := by
  unfold discriminant tailA tailB tailC localPolynomial errorPolynomial
  ring

theorem normalized_expansion (P H U s : R) :
    discriminant (s-1+P*H) (-P*H+P^2*U) s = P^6*
      ((s-1)^2*((2*s-1)^2*H^2*U^2+2*s^2*(2*s-1)^2*H^4*U+s^4*H^6)+
        P*normalizedError P H U s) := by
  unfold discriminant tailA tailB tailC normalizedError
  ring

end D5.S3.Combinatorics.SpectralGraph.PairResonanceAlgebra
