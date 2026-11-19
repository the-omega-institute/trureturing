/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportLargestRootSigns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportLargestRootSigns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact signs and complete upper half-line exclusion for the largest quotient root. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportClassificationAlgebra
import Mathlib.Tactic

/-! These are exact identities in the received three-prime classification.
The P(a,b,c) identity at the upper endpoint is extended coefficientwise to
h(M+1+y), y≥0, so that every real quotient root above that endpoint is excluded.
The source real domains and its a=2..3 branch are retained. Symbolic expansion
only writes the identities; all equalities and inequalities are kernel proofs. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportLargestRootSigns

open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra

/-- Source upper-endpoint shift M=bc+a+b+c. -/
def upperBase (a b c : ℝ) : ℝ := b*c+a+b+c+1

private def shiftCoefficient (k : Fin 6) (a b c : ℝ) : ℝ :=
  let s := a+b+c
  let t := a*b+a*c+b*c
  let u := a*b*c
  let r := upperBase a b c
  let A := 3*s+t
  let B := 3*s^2+2*s*t+s*u+t
  let D := s^3+s^2*t+s^2*u+2*s*t+t^2+u^2+u
  let E := s^2*t+s*t^2+s*t*u+2*s*u+t*u-3*u^2
  ![h a b c r,
    5*r^4-4*A*r^3+3*B*r^2-2*D*r+E,
    10*r^3-6*A*r^2+3*B*r-D,
    10*r^2-4*A*r+B,
    5*r-A,
    1] k

private theorem shift_expansion (a b c y : ℝ) :
    h a b c (upperBase a b c+y) =
      shiftCoefficient 0 a b c + shiftCoefficient 1 a b c*y +
      shiftCoefficient 2 a b c*y^2 + shiftCoefficient 3 a b c*y^3 +
      shiftCoefficient 4 a b c*y^4 + shiftCoefficient 5 a b c*y^5 := by
  simp [shiftCoefficient, h, quintic]
  ring

private theorem large_0 (m u v : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 0 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) := by
  have hid : shiftCoefficient 0 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) =
      m^11*u +
      2*m^11 +
      3*m^10*u^2 +
      44*m^10*u +
      76*m^10 +
      3*m^9*u^3 +
      101*m^9*u^2 +
      4*m^9*u*v +
      828*m^9*u +
      9*m^9*v +
      1277*m^9 +
      m^8*u^4 +
      78*m^8*u^3 +
      12*m^8*u^2*v +
      1466*m^8*u^2 +
      161*m^8*u*v +
      8889*m^8*u +
      302*m^8*v +
      12554*m^8 +
      19*m^7*u^4 +
      12*m^7*u^3*v +
      872*m^7*u^3 +
      352*m^7*u^2*v +
      12165*m^7*u^2 +
      6*m^7*u*v^2 +
      2659*m^7*u*v +
      61012*m^7*u +
      15*m^7*v^2 +
      4351*m^7*v +
      80470*m^7 +
      4*m^6*u^4*v +
      158*m^6*u^4 +
      257*m^6*u^3*v +
      5555*m^6*u^3 +
      18*m^6*u^2*v^2 +
      4258*m^6*u^2*v +
      64328*m^6*u^2 +
      219*m^6*u*v^2 +
      23978*m^6*u*v +
      283142*m^6*u +
      436*m^6*v^2 +
      35391*m^6*v +
      354193*m^6 +
      57*m^5*u^4*v +
      750*m^5*u^4 +
      18*m^5*u^3*v^2 +
      2240*m^5*u^3*v +
      22337*m^5*u^3 +
      450*m^5*u^2*v^2 +
      27997*m^5*u^2*v +
      227591*m^5*u^2 +
      4*m^5*u*v^3 +
      3087*m^5*u*v^2 +
      131613*m^5*u*v +
      911507*m^5*u +
      11*m^5*v^3 +
      5205*m^5*v^2 +
      179723*m^5*v +
      1095075*m^5 +
      6*m^4*u^4*v^2 +
      339*m^4*u^4*v +
      2218*m^4*u^4 +
      303*m^4*u^3*v^2 +
      10495*m^4*u^3*v +
      58928*m^4*u^3 +
      12*m^4*u^2*v^3 +
      4311*m^4*u^2*v^2 +
      110621*m^4*u^2*v +
      547176*m^4*u^2 +
      131*m^4*u*v^3 +
      22137*m^4*u*v^2 +
      460760*m^4*u*v +
      2042989*m^4*u +
      270*m^4*v^3 +
      33056*m^4*v^2 +
      593441*m^4*v +
      2381713*m^4 +
      57*m^3*u^4*v^2 +
      1075*m^3*u^4*v +
      4172*m^3*u^4 +
      12*m^3*u^3*v^3 +
      1864*m^3*u^3*v^2 +
      28811*m^3*u^3*v +
      101999*m^3*u^3 +
      248*m^3*u^2*v^3 +
      20429*m^3*u^2*v^2 +
      271110*m^3*u^2*v +
      883535*m^3*u^2 +
      m^3*u*v^4 +
      1509*m^3*u*v^3 +
      88401*m^3*u*v^2 +
      1037238*m^3*u*v +
      3129572*m^3*u +
      3*m^3*v^4 +
      2530*m^3*v^3 +
      120963*m^3*v^2 +
      1279064*m^3*v +
      3571354*m^3 +
      4*m^2*u^4*v^3 +
      204*m^2*u^4*v^2 +
      1911*m^2*u^4*v +
      4853*m^2*u^4 +
      147*m^2*u^3*v^3 +
      5460*m^2*u^3*v^2 +
      46523*m^2*u^3*v +
      111456*m^2*u^3 +
      3*m^2*u^2*v^4 +
      1712*m^2*u^2*v^3 +
      51528*m^2*u^2*v^2 +
      404388*m^2*u^2*v +
      915785*m^2*u^2 +
      29*m^2*u*v^4 +
      7741*m^2*u*v^3 +
      199807*m^2*u*v^2 +
      1455815*m^2*u*v +
      3118532*m^2*u +
      60*m^2*v^4 +
      11201*m^2*v^3 +
      256850*m^2*v^2 +
      1739823*m^2*v +
      3509410*m^2 +
      19*m*u^4*v^3 +
      325*m*u^4*v^2 +
      1797*m*u^4*v +
      3171*m*u^4 +
      3*m*u^3*v^4 +
      496*m*u^3*v^3 +
      7749*m*u^3*v^2 +
      40917*m*u^3*v +
      69414*m*u^3 +
      49*m*u^2*v^4 +
      4597*m*u^2*v^3 +
      66544*m*u^2*v^2 +
      336158*m*u^2*v +
      547789*m*u^2 +
      253*m*u*v^4 +
      17725*m*u*v^3 +
      239834*m*u*v^2 +
      1159066*m*u*v +
      1812246*m*u +
      399*m*v^4 +
      23290*m*v^3 +
      295089*m*v^2 +
      1356418*m*v +
      2023568*m +
      u^4*v^4 +
      23*u^4*v^3 +
      193*u^4*v^2 +
      693*u^4*v +
      882*u^4 +
      23*u^3*v^4 +
      520*u^3*v^3 +
      4285*u^3*v^2 +
      15059*u^3*v +
      18594*u^3 +
      193*u^2*v^4 +
      4285*u^2*v^3 +
      34629*u^2*v^2 +
      118957*u^2*v +
      142258*u^2 +
      693*u*v^4 +
      15059*u*v^3 +
      118957*u*v^2 +
      398473*u*v +
      461006*u +
      882*v^4 +
      18594*v^3 +
      142258*v^2 +
      461006*v +
      513220 := by
    simp [shiftCoefficient, upperBase, h, quintic]
    ring
  rw [hid]
  positivity

private theorem large_1 (m u v : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 1 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) := by
  have hid : shiftCoefficient 1 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) =
      m^11*u +
      3*m^11 +
      3*m^10*u^2 +
      48*m^10*u +
      117*m^10 +
      3*m^9*u^3 +
      106*m^9*u^2 +
      4*m^9*u*v +
      964*m^9*u +
      12*m^9*v +
      2021*m^9 +
      m^8*u^4 +
      80*m^8*u^3 +
      12*m^8*u^2*v +
      1602*m^8*u^2 +
      173*m^8*u*v +
      10916*m^8*u +
      411*m^8*v +
      20456*m^8 +
      19*m^7*u^4 +
      12*m^7*u^3*v +
      913*m^7*u^3 +
      367*m^7*u^2*v +
      13776*m^7*u^2 +
      6*m^7*u*v^2 +
      3010*m^7*u*v +
      78519*m^7*u +
      18*m^7*v^2 +
      6057*m^7*v +
      135173*m^7 +
      4*m^6*u^4*v +
      158*m^6*u^4 +
      263*m^6*u^3*v +
      5925*m^6*u^3 +
      18*m^6*u^2*v^2 +
      4594*m^6*u^2*v +
      75301*m^6*u^2 +
      231*m^6*u*v^2 +
      28323*m^6*u*v +
      380510*m^6*u +
      531*m^6*v^2 +
      50516*m^6*v +
      613940*m^6 +
      57*m^5*u^4*v +
      750*m^5*u^4 +
      18*m^5*u^3*v^2 +
      2334*m^5*u^3*v +
      24251*m^5*u^3 +
      465*m^5*u^2*v^2 +
      31132*m^5*u^2*v +
      275084*m^5*u^2 +
      4*m^5*u*v^3 +
      3381*m^5*u*v^2 +
      161510*m^5*u*v +
      1276764*m^5*u +
      12*m^5*v^3 +
      6450*m^5*v^2 +
      263699*m^5*v +
      1959923*m^5 +
      6*m^4*u^4*v^2 +
      339*m^4*u^4*v +
      2218*m^4*u^4 +
      309*m^4*u^3*v^2 +
      11117*m^4*u^3*v +
      65119*m^4*u^3 +
      12*m^4*u^2*v^3 +
      4575*m^4*u^2*v^2 +
      126602*m^4*u^2*v +
      682789*m^4*u^2 +
      135*m^4*u*v^3 +
      25016*m^4*u*v^2 +
      586557*m^4*u*v +
      2980392*m^4*u +
      297*m^4*v^3 +
      41821*m^4*v^2 +
      897325*m^4*v +
      4403778*m^4 +
      57*m^3*u^4*v^2 +
      1075*m^3*u^4*v +
      4172*m^3*u^4 +
      12*m^3*u^3*v^3 +
      1929*m^3*u^3*v^2 +
      31022*m^3*u^3*v +
      114789*m^3*u^3 +
      253*m^3*u^2*v^3 +
      22211*m^3*u^2*v^2 +
      319387*m^3*u^2*v +
      1139047*m^3*u^2 +
      m^3*u*v^4 +
      1588*m^3*u*v^3 +
      102943*m^3*u*v^2 +
      1369952*m^3*u*v +
      4756082*m^3*u +
      3*m^3*v^4 +
      2813*m^3*v^3 +
      156944*m^3*v^2 +
      1997938*m^3*v +
      6827880*m^3 +
      4*m^2*u^4*v^3 +
      204*m^2*u^4*v^2 +
      1911*m^2*u^4*v +
      4853*m^2*u^4 +
      149*m^2*u^3*v^3 +
      5734*m^2*u^3*v^2 +
      50954*m^2*u^3*v +
      127893*m^2*u^3 +
      3*m^2*u^2*v^4 +
      1776*m^2*u^2*v^3 +
      57461*m^2*u^2*v^2 +
      490940*m^2*u^2*v +
      1221898*m^2*u^2 +
      29*m^2*u*v^4 +
      8302*m^2*u*v^3 +
      240268*m^2*u*v^2 +
      1997249*m^2*u*v +
      4944751*m^2*u +
      60*m^2*v^4 +
      12643*m^2*v^3 +
      343600*m^2*v^2 +
      2814378*m^2*v +
      6951397*m^2 +
      19*m*u^4*v^3 +
      325*m*u^4*v^2 +
      1797*m*u^4*v +
      3171*m*u^4 +
      3*m*u^3*v^4 +
      508*m*u^3*v^3 +
      8271*m*u^3*v^2 +
      45644*m*u^3*v +
      81390*m*u^3 +
      49*m*u^2*v^4 +
      4855*m*u^2*v^3 +
      76328*m*u^2*v^2 +
      421429*m*u^2*v +
      759051*m*u^2 +
      253*m*u*v^4 +
      19452*m*u*v^3 +
      298933*m*u*v^2 +
      1655362*m*u*v +
      3009412*m*u +
      399*m*v^4 +
      26918*m*v^3 +
      409363*m*v^2 +
      2279088*m*v +
      4171760*m +
      u^4*v^4 +
      23*u^4*v^3 +
      193*u^4*v^2 +
      693*u^4*v +
      882*u^4 +
      23*u^3*v^4 +
      542*u^3*v^3 +
      4660*u^3*v^2 +
      17146*u^3*v +
      22365*u^3 +
      193*u^2*v^4 +
      4660*u^2*v^3 +
      41031*u^2*v^2 +
      154517*u^2*v +
      206058*u^2 +
      693*u*v^4 +
      17146*u*v^3 +
      154517*u*v^2 +
      594697*u*v +
      808211*u +
      882*v^4 +
      22365*v^3 +
      206058*v^2 +
      808211*v +
      1112120 := by
    simp [shiftCoefficient, upperBase, h, quintic]
    ring
  rw [hid]
  positivity

private theorem large_2 (m u v : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 2 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) := by
  have hid : shiftCoefficient 2 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) =
      m^9 +
      6*m^8*u +
      43*m^8 +
      9*m^7*u^2 +
      183*m^7*u +
      3*m^7*v +
      746*m^7 +
      4*m^6*u^3 +
      197*m^6*u^2 +
      18*m^6*u*v +
      2289*m^6*u +
      115*m^6*v +
      7015*m^6 +
      57*m^5*u^3 +
      27*m^5*u^2*v +
      1749*m^5*u^2 +
      464*m^5*u*v +
      15526*m^5*u +
      3*m^5*v^2 +
      1680*m^5*v +
      40048*m^5 +
      12*m^4*u^3*v +
      339*m^4*u^3 +
      463*m^4*u^2*v +
      8341*m^4*u^2 +
      18*m^4*u*v^2 +
      4564*m^4*u*v +
      63270*m^4*u +
      101*m^4*v^2 +
      12434*m^4*v +
      145809*m^4 +
      114*m^3*u^3*v +
      1075*m^3*u^3 +
      27*m^3*u^2*v^2 +
      2893*m^3*u^2*v +
      23315*m^3*u^2 +
      379*m^3*u*v^2 +
      22196*m^3*u*v +
      160078*m^3*u +
      m^3*v^3 +
      1187*m^3*v^2 +
      51290*m^3*v +
      341790*m^3 +
      12*m^2*u^3*v^2 +
      408*m^2*u^3*v +
      1911*m^2*u^3 +
      335*m^2*u^2*v^2 +
      8615*m^2*u^2*v +
      38369*m^2*u^2 +
      6*m^2*u*v^3 +
      2661*m^2*u*v^2 +
      57601*m^2*u*v +
      246927*m^2*u +
      29*m^2*v^3 +
      6212*m^2*v^2 +
      120207*m^2*v +
      500640*m^2 +
      57*m*u^3*v^2 +
      650*m*u^3*v +
      1797*m*u^3 +
      9*m*u^2*v^3 +
      1144*m*u^2*v^2 +
      12455*m*u^2*v +
      34440*m*u^2 +
      98*m*u*v^3 +
      7295*m*u*v^2 +
      76832*m*u*v +
      212826*m*u +
      253*m*v^3 +
      14612*m*v^2 +
      150426*m*v +
      417396*m +
      4*u^3*v^3 +
      69*u^3*v^2 +
      386*u^3*v +
      693*u^3 +
      69*u^2*v^3 +
      1224*u^2*v^2 +
      7036*u^2*v +
      12963*u^2 +
      386*u*v^3 +
      7036*u*v^2 +
      41526*u*v +
      78393*u +
      693*v^3 +
      12963*v^2 +
      78393*v +
      151093 := by
    simp [shiftCoefficient, upperBase, h, quintic]
    ring
  rw [hid]
  positivity

private theorem large_3 (m u v : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 3 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) := by
  have hid : shiftCoefficient 3 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) =
      3*m^6 +
      9*m^5*u +
      77*m^5 +
      6*m^4*u^2 +
      154*m^4*u +
      6*m^4*v +
      757*m^4 +
      57*m^3*u^2 +
      18*m^3*u*v +
      964*m^3*u +
      126*m^3*v +
      3697*m^3 +
      12*m^2*u^2*v +
      204*m^2*u^2 +
      223*m^2*u*v +
      2885*m^2*u +
      3*m^2*v^2 +
      885*m^2*v +
      9682*m^2 +
      57*m*u^2*v +
      325*m*u^2 +
      9*m*u*v^2 +
      764*m*u*v +
      4203*m*u +
      49*m*v^2 +
      2443*m*v +
      13100*m +
      6*u^2*v^2 +
      69*u^2*v +
      193*u^2 +
      69*u*v^2 +
      826*u*v +
      2399*u +
      193*v^2 +
      2399*v +
      7231 := by
    simp [shiftCoefficient, upperBase, h, quintic]
    ring
  rw [hid]
  positivity

private theorem large_4 (m u v : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 4 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) := by
  have hid : shiftCoefficient 4 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) =
      3*m^3 +
      4*m^2*u +
      37*m^2 +
      19*m*u +
      3*m*v +
      128*m +
      4*u*v +
      23*u +
      23*v +
      143 := by
    simp [shiftCoefficient, upperBase, h, quintic]
    ring
  rw [hid]
  positivity

private theorem large_5 (m u v : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 5 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) := by
  have hid : shiftCoefficient 5 (3+m) (6+m+u) ((3+m)^2-(3+m)+v) =
      1 := by
    simp [shiftCoefficient, upperBase, h, quintic]
  rw [hid]
  positivity

private theorem small_0 (m u v : ℝ) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 0 (2+m) (5+m+u) (5+m+u+v) := by
  have hp1 : 0 ≤ 1-m^1 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp2 : 0 ≤ 1-m^2 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp3 : 0 ≤ 1-m^3 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp4 : 0 ≤ 1-m^4 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp5 : 0 ≤ 1-m^5 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp6 : 0 ≤ 1-m^6 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp7 : 0 ≤ 1-m^7 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hid : shiftCoefficient 0 (2+m) (5+m+u) (5+m+u+v) =
      (1)*u^8 +
      (4)*u^7*v +
      (40 + 6*m)*u^7 +
      (6)*u^6*v^2 +
      (140 + 21*m)*u^6*v +
      (693 + 200*m + 13*m^2)*u^6 +
      (4)*u^5*v^3 +
      (180 + 27*m)*u^5*v^2 +
      (2079 + 600*m + 39*m^2)*u^5*v +
      (6792 + 2814*m + 340*m^2 + 10*m^3)*u^5 +
      (1)*u^4*v^4 +
      (100 + 15*m)*u^4*v^3 +
      (2226 + 643*m + 42*m^2)*u^4*v^2 +
      (16980 + 7035*m + 850*m^2 + 25*m^3)*u^4*v +
      (41170 + 21620*m + 3567*m^2 + 154*m^3 + 5*(1-m^4))*u^4 +
      (20 + 3*m)*u^3*v^4 +
      (987 + 286*m + 19*m^2)*u^3*v^3 +
      (14520 + 6024*m + 732*m^2 + 22*m^3)*u^3*v^2 +
      (82340 + 43240*m + 7134*m^2 + 308*m^3 + 10*(1-m^4))*u^3*v +
      (157834 + 97718*m + 18962*m^2 + 588*m^3 + 182*(1-m^4) + 14*(1-m^5))*u^3 +
      (147 + 43*m + 3*m^2)*u^2*v^4 +
      (4800 + 2001*m + 248*m^2 + 8*m^3)*u^2*v^3 +
      (52638 + 27670*m + 4587*m^2 + 203*m^3 + 6*(1-m^4))*u^2*v^2 +
      (236751 + 146577*m + 28443*m^2 + 882*m^3 + 273*(1-m^4) + 21*(1-m^5))*u^2*v +
      (371193 + 259084*m + 52712*m^2 + 1508*(1-m^3) + 1862*(1-m^4) + 230*(1-m^5) + 9*(1-m^6))*u^2 +
      (468 + 198*m + 26*m^2 + m^3)*u*v^4 +
      (11468 + 6050*m + 1020*m^2 + 49*m^3 + 1*(1-m^4))*u*v^3 +
      (100317 + 62037*m + 12019*m^2 + 366*m^3 + 117*(1-m^4) + 9*(1-m^5))*u*v^2 +
      (371193 + 259084*m + 52712*m^2 + 1508*(1-m^3) + 1862*(1-m^4) + 230*(1-m^5) + 9*(1-m^6))*u*v +
      (480352 + 371916*m + 69744*m^2 + 13222*(1-m^3) + 7222*(1-m^4) + 1132*(1-m^5) + 78*(1-m^6) + 2*(1-m^7))*u +
      (540 + 288*m + 51*m^2 + 3*m^3)*v^4 +
      (10700 + 6589*m + 1269*m^2 + 36*m^3 + 13*(1-m^4) + 1*(1-m^5))*v^3 +
      (77666 + 53913*m + 10679*m^2 + 457*(1-m^3) + 418*(1-m^4) + 51*(1-m^5) + 2*(1-m^6))*v^2 +
      (240176 + 185958*m + 34872*m^2 + 6611*(1-m^3) + 3611*(1-m^4) + 566*(1-m^5) + 39*(1-m^6) + 1*(1-m^7))*v +
      (259876 + 222224*m + 31120*m^2 + 19920*(1-m^3) + 9116*(1-m^4) + 1580*(1-m^5) + 128*(1-m^6) + 4*(1-m^7)) := by
    simp [shiftCoefficient, upperBase, h, quintic]
    ring
  rw [hid]
  positivity

private theorem small_1 (m u v : ℝ) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 1 (2+m) (5+m+u) (5+m+u+v) := by
  have hp1 : 0 ≤ 1-m^1 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp2 : 0 ≤ 1-m^2 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp3 : 0 ≤ 1-m^3 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp4 : 0 ≤ 1-m^4 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp5 : 0 ≤ 1-m^5 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp6 : 0 ≤ 1-m^6 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hid : shiftCoefficient 1 (2+m) (5+m+u) (5+m+u+v) =
      (1)*u^8 +
      (4)*u^7*v +
      (40 + 6*m)*u^7 +
      (6)*u^6*v^2 +
      (140 + 21*m)*u^6*v +
      (705 + 208*m + 15*m^2)*u^6 +
      (4)*u^5*v^3 +
      (180 + 27*m)*u^5*v^2 +
      (2115 + 624*m + 45*m^2)*u^5*v +
      (7144 + 3104*m + 438*m^2 + 20*m^3)*u^5 +
      (1)*u^4*v^4 +
      (100 + 15*m)*u^4*v^3 +
      (2262 + 667*m + 48*m^2)*u^4*v^2 +
      (17860 + 7760*m + 1095*m^2 + 50*m^3)*u^4*v +
      (45469 + 25804*m + 5327*m^2 + 472*m^3 + 15*m^4)*u^4 +
      (20 + 3*m)*u^3*v^4 +
      (999 + 294*m + 21*m^2)*u^3*v^3 +
      (15224 + 6604*m + 928*m^2 + 42*m^3)*u^3*v^2 +
      (90938 + 51608*m + 10654*m^2 + 944*m^3 + 30*m^4)*u^3*v +
      (185868 + 128784*m + 34426*m^2 + 4412*m^3 + 268*m^4 + 6*m^5)*u^3 +
      (147 + 43*m + 3*m^2)*u^2*v^4 +
      (4976 + 2146*m + 297*m^2 + 13*m^3)*u^2*v^3 +
      (57784 + 32680*m + 6695*m^2 + 584*m^3 + 18*m^4)*u^2*v^2 +
      (278802 + 193176*m + 51639*m^2 + 6618*m^3 + 402*m^4 + 9*m^5)*u^2*v +
      (475778 + 384840*m + 124120*m^2 + 20262*m^3 + 1740*m^4 + 72*m^5 + m^6)*u^2 +
      (468 + 198*m + 26*m^2 + m^3)*u*v^4 +
      (12315 + 6876*m + 1368*m^2 + 112*m^3 + 3*m^4)*u*v^3 +
      (117018 + 80550*m + 21241*m^2 + 2648*m^3 + 152*m^4 + 3*m^5)*u*v^2 +
      (475778 + 384840*m + 124120*m^2 + 20262*m^3 + 1740*m^4 + 72*m^5 + m^6)*u*v +
      (695902 + 635246*m + 235114*m^2 + 45140*m^3 + 4752*m^4 + 262*m^5 + 6*m^6)*u +
      (540 + 288*m + 51*m^2 + 3*m^3)*v^4 +
      (12042 + 8079*m + 2014*m^2 + 221*m^3 + 9*m^4)*v^3 +
      (98453 + 78688*m + 24769*m^2 + 3844*m^3 + 295*m^4 + 9*m^5)*v^2 +
      (347951 + 317623*m + 117557*m^2 + 22570*m^3 + 2376*m^4 + 131*m^5 + 3*m^6)*v +
      (444218 + 444472*m + 180736*m^2 + 38072*m^3 + 4360*m^4 + 256*m^5 + 6*m^6) := by
    simp [shiftCoefficient, upperBase, h, quintic]
    ring
  rw [hid]
  positivity

private theorem small_2 (m u v : ℝ) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 2 (2+m) (5+m+u) (5+m+u+v) := by
  have hp1 : 0 ≤ 1-m^1 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp2 : 0 ≤ 1-m^2 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp3 : 0 ≤ 1-m^3 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp4 : 0 ≤ 1-m^4 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp5 : 0 ≤ 1-m^5 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hid : shiftCoefficient 2 (2+m) (5+m+u) (5+m+u+v) =
      (4)*u^6 +
      (12)*u^5*v +
      (120 + 18*m)*u^5 +
      (12)*u^4*v^2 +
      (300 + 45*m)*u^4*v +
      (1516 + 448*m + 32*m^2)*u^4 +
      (4)*u^3*v^3 +
      (240 + 36*m)*u^3*v^2 +
      (3032 + 896*m + 64*m^2)*u^3*v +
      (10310 + 4492*m + 628*m^2 + 28*m^3)*u^3 +
      (60 + 9*m)*u^2*v^3 +
      (1810 + 534*m + 38*m^2)*u^2*v^2 +
      (15465 + 6738*m + 942*m^2 + 42*m^3)*u^2*v +
      (39773 + 22644*m + 4625*m^2 + 398*m^3 + 12*m^4)*u^2 +
      (294 + 86*m + 6*m^2)*u*v^3 +
      (6091 + 2642*m + 366*m^2 + 16*m^3)*u*v^2 +
      (39773 + 22644*m + 4625*m^2 + 398*m^3 + 12*m^4)*u*v +
      (82460 + 57278*m + 15086*m^2 + 1856*m^3 + 104*m^4 + 2*m^5)*u +
      (468 + 198*m + 26*m^2 + m^3)*v^3 +
      (7686 + 4334*m + 869*m^2 + 72*m^3 + 2*m^4)*v^2 +
      (41230 + 28639*m + 7543*m^2 + 928*m^3 + 52*m^4 + m^5)*v +
      (71771 + 58044*m + 18273*m^2 + 2792*m^3 + 207*m^4 + 6*m^5) := by
    simp [shiftCoefficient, upperBase, h, quintic]
    ring
  rw [hid]
  positivity

private theorem small_3 (m u v : ℝ) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 3 (2+m) (5+m+u) (5+m+u+v) := by
  have hp1 : 0 ≤ 1-m^1 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp2 : 0 ≤ 1-m^2 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp3 : 0 ≤ 1-m^3 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp4 : 0 ≤ 1-m^4 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hid : shiftCoefficient 3 (2+m) (5+m+u) (5+m+u+v) =
      (6)*u^4 +
      (12)*u^3*v +
      (120 + 18*m)*u^3 +
      (6)*u^2*v^2 +
      (180 + 27*m)*u^2*v +
      (921 + 272*m + 19*m^2)*u^2 +
      (60 + 9*m)*u*v^2 +
      (921 + 272*m + 19*m^2)*u*v +
      (3206 + 1394*m + 190*m^2 + 8*m^3)*u +
      (147 + 43*m + 3*m^2)*v^2 +
      (1603 + 697*m + 95*m^2 + 4*m^3)*v +
      (4285 + 2428*m + 479*m^2 + 38*m^3 + m^4) := by
    simp [shiftCoefficient, upperBase, h, quintic]
    ring
  rw [hid]
  positivity

private theorem small_4 (m u v : ℝ) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 4 (2+m) (5+m+u) (5+m+u+v) := by
  have hp1 : 0 ≤ 1-m^1 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hp2 : 0 ≤ 1-m^2 := sub_nonneg.mpr (pow_le_one₀ hm hm1)
  have hid : shiftCoefficient 4 (2+m) (5+m+u) (5+m+u+v) =
      (4)*u^2 +
      (4)*u*v +
      (40 + 6*m)*u +
      (20 + 3*m)*v +
      (109 + 32*m + 2*m^2) := by
    simp [shiftCoefficient, upperBase, h, quintic]
    ring
  rw [hid]
  positivity

private theorem small_5 (m u v : ℝ) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < shiftCoefficient 5 (2+m) (5+m+u) (5+m+u+v) := by
  have hid : shiftCoefficient 5 (2+m) (5+m+u) (5+m+u+v) =
      (1) := by
    simp [shiftCoefficient, upperBase, h, quintic]
  rw [hid]
  positivity

/-- The entire upper half-line has strictly positive quintic value on the
original largest-root domain. This excludes every upper root, without a
sample or a premise encoding the desired spectral conclusion. -/
theorem upper_halfline (a b c y : ℝ) (ha : 2 ≤ a) (hab : a+3 ≤ b)
    (hbc : b ≤ c) (hc : a^2-a ≤ c) (hy : 0 ≤ y) :
    0 < h a b c (b*c+a+b+c+1+y) := by
  have hcoeff : ∀ k : Fin 6, 0 < shiftCoefficient k a b c := by
    intro k
    by_cases ha3 : 3 ≤ a
    · have hm : 0 ≤ a-3 := by linarith
      have hu : 0 ≤ b-a-3 := by linarith
      have hv : 0 ≤ c-(a^2-a) := by linarith
      have hs : ∀ k, shiftCoefficient k a b c =
          shiftCoefficient k (3+(a-3)) (6+(a-3)+(b-a-3))
            ((3+(a-3))^2-(3+(a-3))+(c-(a^2-a))) := by
        intro k
        congr 1 <;> ring
      rw [hs k]
      fin_cases k
      · exact large_0 _ _ _ hm hu hv
      · exact large_1 _ _ _ hm hu hv
      · exact large_2 _ _ _ hm hu hv
      · exact large_3 _ _ _ hm hu hv
      · exact large_4 _ _ _ hm hu hv
      · exact large_5 _ _ _ hm hu hv
    · have hm : 0 ≤ a-2 := by linarith
      have hm1 : a-2 ≤ 1 := by linarith
      have hu : 0 ≤ b-a-3 := by linarith
      have hv : 0 ≤ c-b := by linarith
      have hs : ∀ k, shiftCoefficient k a b c =
          shiftCoefficient k (2+(a-2)) (5+(a-2)+(b-a-3))
            (5+(a-2)+(b-a-3)+(c-b)) := by
        intro k
        congr 1 <;> ring
      rw [hs k]
      fin_cases k
      · exact small_0 _ _ _ hm hm1 hu hv
      · exact small_1 _ _ _ hm hm1 hu hv
      · exact small_2 _ _ _ hm hm1 hu hv
      · exact small_3 _ _ _ hm hm1 hu hv
      · exact small_4 _ _ _ hm hm1 hu hv
      · exact small_5 _ _ _ hm hm1 hu hv
  change 0 < h a b c (upperBase a b c+y)
  rw [shift_expansion]
  have h0 := hcoeff 0
  have h1 := hcoeff 1
  have h2 := hcoeff 2
  have h3 := hcoeff 3
  have h4 := hcoeff 4
  have h5 := hcoeff 5
  positivity

/-- The original lower-endpoint T polynomial. -/
def lowerFactor (a b c : ℝ) : ℝ :=
  (2*b^2-a*b+b-a)*c^2-((a-1)*b^2+a^2)*c-a*b*(a+b)

private theorem lowerFactor_positive_shift (m u v : ℝ)
    (hm : 0 ≤ m) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 < lowerFactor (2+m) (5+m+u) (5+m+u+v) := by
  have hid : lowerFactor (2+m) (5+m+u) (5+m+u+v) =
      2*m^3*u +
      m^3*v +
      4*m^3 +
      6*m^2*u^2 +
      6*m^2*u*v +
      48*m^2*u +
      m^2*v^2 +
      24*m^2*v +
      78*m^2 +
      6*m*u^3 +
      9*m*u^2*v +
      82*m*u^2 +
      3*m*u*v^2 +
      82*m*u*v +
      354*m*u +
      13*m*v^2 +
      177*m*v +
      462*m +
      2*u^4 +
      4*u^3*v +
      38*u^3 +
      2*u^2*v^2 +
      57*u^2*v +
      266*u^2 +
      19*u*v^2 +
      266*u*v +
      802*u +
      43*v^2 +
      401*v +
      860 := by dsimp [lowerFactor]; ring
  rw [hid]
  positivity

/-- Strict lower sign on the full real domain, not just integer parameters. -/
theorem lower_negative (a b c : ℝ) (ha : 2 ≤ a) (hab : a+3 ≤ b)
    (hbc : b ≤ c) : h a b c (b*c+a+b+c) < 0 := by
  have hfac : 0 < lowerFactor a b c := by
    have hm : 0 ≤ a-2 := by linarith
    have hu : 0 ≤ b-a-3 := by linarith
    have hv : 0 ≤ c-b := by linarith
    have hs : lowerFactor a b c =
        lowerFactor (2+(a-2)) (5+(a-2)+(b-a-3))
          (5+(a-2)+(b-a-3)+(c-b)) := by congr 1 <;> ring
    rw [hs]
    exact lowerFactor_positive_shift _ _ _ hm hu hv
  have hid : h a b c (b*c+a+b+c) = -a^2*b*c*lowerFactor a b c := by
    simp [h, quintic, lowerFactor]
    ring
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  rw [hid]
  have : 0 < a^2*b*c*lowerFactor a b c := by positivity
  nlinarith

#print axioms upper_halfline
#print axioms lower_negative

end D5.S3.Combinatorics.SpectralGraph.SixSupportLargestRootSigns
