/- GID: D5/S3/Observer/CubicGain/SourceFixedMinor
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/SourceFixedMinor
   mirror-E: none(waiver:source-fixed-minor-continuation)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Derivative]
   utility: none
   digest: Literal clock-five-six-seven minor polynomials and their fixed-column relation. -/

import D5.S3.Observer.CubicGain.ExactW3Center
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.ComputeDegree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
noncomputable section

namespace D5.S3.Observer.CubicGain.SourceFixedMinor

open Polynomial
open D5.S3.Observer.CubicGain.RegularResponseCircuit
open D5.S3.Observer.CubicGain.ExactW3Center

/-- The integer circuit of VI (2.3), over an arbitrary coefficient ring. -/
def sourceJ {R : Type*} [CommRing R] (t b : R) : R := t+b*(1-t^2)
def sourceN {R : Type*} [CommRing R] (t b : R) : R := sourceJ t b+t*b
def sourceD {R : Type*} [CommRing R] (t b : R) : R :=
  5*((b^2+8*b+4)*sourceJ t b*sourceN t b-
    2*(1+b)*(1+2*b)*(sourceJ t b+sourceN t b))
def sourceC {R : Type*} [CommRing R] (t b : R) : Fin 4 → R :=
  ![-24*sourceD t b+3*((8*b-1)*(2+5*b))*sourceJ t b*sourceN t b,
    3*((8*b-1)*(2+5*b))*sourceN t b,
    3*(49*b+34)*sourceJ t b*sourceN t b-
      54*(1+2*b)*(sourceJ t b+sourceN t b),
    3*((8*b-1)*(2+5*b))*sourceJ t b]
/-- Numerators at clocks five, six and seven, in this order. -/
def sourceNumerator {R : Type*} [CommRing R] (t b : R) : Fin 3 → R :=
  ![-sourceC t b 0+(1+2*b+sourceN t b)*
      (-4*sourceC t b 0+15*sourceC t b 1-20*sourceC t b 2+10*sourceC t b 3),
    -sourceC t b 0+(2*(1+2*b)+sourceN t b)*
      (-10*sourceC t b 0+36*sourceC t b 1-45*sourceC t b 2+20*sourceC t b 3),
    -sourceC t b 0+(3*(1+2*b)+2*sourceN t b)*
      (-20*sourceC t b 0+70*sourceC t b 1-84*sourceC t b 2+35*sourceC t b 3)]

/-- The literal formal partials used in VI (3.1). -/
def sourceBt (i : Fin 3) (t b : ℝ) : ℝ :=
  sourceD t b * ((sourceNumerator (X : Polynomial ℝ) (C b) i).derivative.eval t) -
    sourceNumerator t b i * ((sourceD (X : Polynomial ℝ) (C b)).derivative.eval t)
def sourceBb (i : Fin 3) (t b : ℝ) : ℝ :=
  sourceD t b * ((sourceNumerator (C t) (X : Polynomial ℝ) i).derivative.eval b) -
    sourceNumerator t b i * ((sourceD (C t) (X : Polynomial ℝ)).derivative.eval b)

/-- Coefficients in r of the normalized pair (N0,N1), with fixed degree fifteen. -/
def sourceE0 {R : Type*} [CommRing R] (b : R) : Polynomial R :=
    (((((((C ((-102720 : R) * b^2) * (X : Polynomial R)^15 + C ((-821760 : R) * b^1) * (X : Polynomial R)^15) + (C ((-410880 : R) * b^0) * (X : Polynomial R)^15 + C ((462240 : R) * b^3) * (X : Polynomial R)^14)) + ((C ((4468320 : R) * b^2) * (X : Polynomial R)^14 + C ((8012160 : R) * b^1) * (X : Polynomial R)^14) + (C ((3081600 : R) * b^0) * (X : Polynomial R)^14 + C ((-7143760 : R) * b^4) * (X : Polynomial R)^13))) + (((C ((-11582400 : R) * b^3) * (X : Polynomial R)^13 + C ((-30276960 : R) * b^2) * (X : Polynomial R)^13) + (C ((-32838400 : R) * b^1) * (X : Polynomial R)^13 + C ((-10066560 : R) * b^0) * (X : Polynomial R)^13)) + ((C ((22459578 : R) * b^5) * (X : Polynomial R)^12 + C ((56745342 : R) * b^4) * (X : Polynomial R)^12) + (C ((62161092 : R) * b^3) * (X : Polynomial R)^12 + C ((95034456 : R) * b^2) * (X : Polynomial R)^12)))) + ((((C ((75090096 : R) * b^1) * (X : Polynomial R)^12 + C ((18695040 : R) * b^0) * (X : Polynomial R)^12) + (C ((-9217971 : R) * b^6) * (X : Polynomial R)^11 + C ((-141242232 : R) * b^5) * (X : Polynomial R)^11)) + ((C ((-193416828 : R) * b^4) * (X : Polynomial R)^11 + C ((-155883048 : R) * b^3) * (X : Polynomial R)^11) + (C ((-171106272 : R) * b^2) * (X : Polynomial R)^11 + C ((-106073376 : R) * b^1) * (X : Polynomial R)^11))) + (((C ((-21571200 : R) * b^0) * (X : Polynomial R)^11 + C ((-43923051 : R) * b^7) * (X : Polynomial R)^10) + (C ((55368967 : R) * b^6) * (X : Polynomial R)^10 + C ((397068070 : R) * b^5) * (X : Polynomial R)^10)) + ((C ((365740526 : R) * b^4) * (X : Polynomial R)^10 + C ((216529540 : R) * b^3) * (X : Polynomial R)^10) + (C ((189534136 : R) * b^2) * (X : Polynomial R)^10 + (C ((96050000 : R) * b^1) * (X : Polynomial R)^10 + C ((15818880 : R) * b^0) * (X : Polynomial R)^10)))))) + (((((C ((47580070 : R) * b^8) * (X : Polynomial R)^9 + C ((237039086 : R) * b^7) * (X : Polynomial R)^9) + (C ((-146554321 : R) * b^6) * (X : Polynomial R)^9 + C ((-651464362 : R) * b^5) * (X : Polynomial R)^9)) + ((C ((-411805396 : R) * b^4) * (X : Polynomial R)^9 + C ((-167471368 : R) * b^3) * (X : Polynomial R)^9) + (C ((-129332480 : R) * b^2) * (X : Polynomial R)^9 + C ((-55577280 : R) * b^1) * (X : Polynomial R)^9))) + (((C ((-7190400 : R) * b^0) * (X : Polynomial R)^9 + C ((15571863 : R) * b^9) * (X : Polynomial R)^8) + (C ((-282359934 : R) * b^8) * (X : Polynomial R)^8 + C ((-569712687 : R) * b^7) * (X : Polynomial R)^8)) + ((C ((233326389 : R) * b^6) * (X : Polynomial R)^8 + C ((682350220 : R) * b^5) * (X : Polynomial R)^8) + (C ((269525838 : R) * b^4) * (X : Polynomial R)^8 + (C ((55675140 : R) * b^3) * (X : Polynomial R)^8 + C ((50405320 : R) * b^2) * (X : Polynomial R)^8))))) + ((((C ((19663440 : R) * b^1) * (X : Polynomial R)^8 + C ((1848960 : R) * b^0) * (X : Polynomial R)^8) + (C ((-37353091 : R) * b^10) * (X : Polynomial R)^7 + C ((-19992407 : R) * b^9) * (X : Polynomial R)^7)) + ((C ((699003766 : R) * b^8) * (X : Polynomial R)^7 + C ((778382188 : R) * b^7) * (X : Polynomial R)^7) + (C ((-259457859 : R) * b^6) * (X : Polynomial R)^7 + C ((-469417860 : R) * b^5) * (X : Polynomial R)^7))) + (((C ((-82711964 : R) * b^4) * (X : Polynomial R)^7 + C ((13760648 : R) * b^3) * (X : Polynomial R)^7) + (C ((-8174176 : R) * b^2) * (X : Polynomial R)^7 + C ((-3801376 : R) * b^1) * (X : Polynomial R)^7)) + ((C ((-205440 : R) * b^0) * (X : Polynomial R)^7 + C ((8687448 : R) * b^11) * (X : Polynomial R)^6) + (C ((185858499 : R) * b^10) * (X : Polynomial R)^6 + (C ((-40242750 : R) * b^9) * (X : Polynomial R)^6 + C ((-933174884 : R) * b^8) * (X : Polynomial R)^6))))))) + ((((((C ((-633912971 : R) * b^7) * (X : Polynomial R)^6 + C ((216188371 : R) * b^6) * (X : Polynomial R)^6) + (C ((211160574 : R) * b^5) * (X : Polynomial R)^6 + C ((-7312454 : R) * b^4) * (X : Polynomial R)^6)) + ((C ((-19363172 : R) * b^3) * (X : Polynomial R)^6 + C ((-783928 : R) * b^2) * (X : Polynomial R)^6) + (C ((296496 : R) * b^1) * (X : Polynomial R)^6 + C ((3317251 : R) * b^12) * (X : Polynomial R)^5))) + (((C ((-87048314 : R) * b^11) * (X : Polynomial R)^5 + C ((-368371929 : R) * b^10) * (X : Polynomial R)^5) + (C ((104816472 : R) * b^9) * (X : Polynomial R)^5 + C ((722665054 : R) * b^8) * (X : Polynomial R)^5)) + ((C ((291737766 : R) * b^7) * (X : Polynomial R)^5 + C ((-131748529 : R) * b^6) * (X : Polynomial R)^5) + (C ((-60417178 : R) * b^5) * (X : Polynomial R)^5 + C ((13788732 : R) * b^4) * (X : Polynomial R)^5)))) + ((((C ((6435240 : R) * b^3) * (X : Polynomial R)^5 + C ((334304 : R) * b^2) * (X : Polynomial R)^5) + (C ((-636165 : R) * b^13) * (X : Polynomial R)^4 + C ((-6876073 : R) * b^12) * (X : Polynomial R)^4)) + ((C ((204832493 : R) * b^11) * (X : Polynomial R)^4 + C ((375617729 : R) * b^10) * (X : Polynomial R)^4) + (C ((-93346391 : R) * b^9) * (X : Polynomial R)^4 + C ((-325126952 : R) * b^8) * (X : Polynomial R)^4))) + (((C ((-60501195 : R) * b^7) * (X : Polynomial R)^4 + C ((52506641 : R) * b^6) * (X : Polynomial R)^4) + (C ((10384310 : R) * b^5) * (X : Polynomial R)^4 + C ((-3708596 : R) * b^4) * (X : Polynomial R)^4)) + ((C ((-723912 : R) * b^3) * (X : Polynomial R)^4 + C ((2649746 : R) * b^14) * (X : Polynomial R)^3) + (C ((17699710 : R) * b^13) * (X : Polynomial R)^3 + (C ((3262907 : R) * b^12) * (X : Polynomial R)^3 + C ((-199823808 : R) * b^11) * (X : Polynomial R)^3)))))) + (((((C ((-203793686 : R) * b^10) * (X : Polynomial R)^3 + C ((45069967 : R) * b^9) * (X : Polynomial R)^3) + (C ((81542558 : R) * b^8) * (X : Polynomial R)^3 + C ((-478476 : R) * b^7) * (X : Polynomial R)^3)) + ((C ((-11295928 : R) * b^6) * (X : Polynomial R)^3 + C ((-881120 : R) * b^5) * (X : Polynomial R)^3) + (C ((298560 : R) * b^4) * (X : Polynomial R)^3 + C ((-2637039 : R) * b^15) * (X : Polynomial R)^2))) + (((C ((-10326504 : R) * b^14) * (X : Polynomial R)^2 + C ((-36904122 : R) * b^13) * (X : Polynomial R)^2) + (C ((-4673923 : R) * b^12) * (X : Polynomial R)^2 + C ((85627677 : R) * b^11) * (X : Polynomial R)^2)) + ((C ((52032126 : R) * b^10) * (X : Polynomial R)^2 + C ((-14379758 : R) * b^9) * (X : Polynomial R)^2) + (C ((-11117238 : R) * b^8) * (X : Polynomial R)^2 + (C ((1330788 : R) * b^7) * (X : Polynomial R)^2 + C ((884240 : R) * b^6) * (X : Polynomial R)^2))))) + ((((C ((398475 : R) * b^16) * (X : Polynomial R)^1 + C ((4321197 : R) * b^15) * (X : Polynomial R)^1) + (C ((13472587 : R) * b^14) * (X : Polynomial R)^1 + C ((25681227 : R) * b^13) * (X : Polynomial R)^1)) + ((C ((5012428 : R) * b^12) * (X : Polynomial R)^1 + C ((-14193728 : R) * b^11) * (X : Polynomial R)^1) + (C ((-4554672 : R) * b^10) * (X : Polynomial R)^1 + C ((2416648 : R) * b^9) * (X : Polynomial R)^1))) + (((C ((868800 : R) * b^8) * (X : Polynomial R)^1 + C ((155926 : R) * b^17) * (X : Polynomial R)^0) + (C ((-601697 : R) * b^16) * (X : Polynomial R)^0 + C ((-1542906 : R) * b^15) * (X : Polynomial R)^0)) + ((C ((-4285783 : R) * b^14) * (X : Polynomial R)^0 + C ((-4638172 : R) * b^13) * (X : Polynomial R)^0) + (C ((-687942 : R) * b^12) * (X : Polynomial R)^0 + (C ((930652 : R) * b^11) * (X : Polynomial R)^0 + C ((283120 : R) * b^10) * (X : Polynomial R)^0))))))))

/-- Coefficients in r of the normalized pair (N0,N2), with fixed degree fifteen. -/
def sourceE1 {R : Type*} [CommRing R] (b : R) : Polynomial R :=
    (((((((C ((-657408 : R) * b^2) * (X : Polynomial R)^15 + C ((-5259264 : R) * b^1) * (X : Polynomial R)^15) + (C ((-2629632 : R) * b^0) * (X : Polynomial R)^15 + C ((2958336 : R) * b^3) * (X : Polynomial R)^14)) + ((C ((28597248 : R) * b^2) * (X : Polynomial R)^14 + C ((51277824 : R) * b^1) * (X : Polynomial R)^14) + (C ((19722240 : R) * b^0) * (X : Polynomial R)^14 + C ((-18426880 : R) * b^4) * (X : Polynomial R)^13))) + (((C ((-48410304 : R) * b^3) * (X : Polynomial R)^13 + C ((-190071552 : R) * b^2) * (X : Polynomial R)^13) + (C ((-211083520 : R) * b^1) * (X : Polynomial R)^13 + C ((-64425984 : R) * b^0) * (X : Polynomial R)^13)) + ((C ((48118592 : R) * b^5) * (X : Polynomial R)^12 + C ((95654432 : R) * b^4) * (X : Polynomial R)^12) + (C ((217707360 : R) * b^3) * (X : Polynomial R)^12 + C ((587379968 : R) * b^2) * (X : Polynomial R)^12)))) + ((((C ((486541952 : R) * b^1) * (X : Polynomial R)^12 + C ((119648256 : R) * b^0) * (X : Polynomial R)^12) + (C ((-9870816 : R) * b^6) * (X : Polynomial R)^11 + C ((-239739808 : R) * b^5) * (X : Polynomial R)^11)) + ((C ((-161018400 : R) * b^4) * (X : Polynomial R)^11 + C ((-453449856 : R) * b^3) * (X : Polynomial R)^11) + (C ((-1049087872 : R) * b^2) * (X : Polynomial R)^11 + C ((-695388672 : R) * b^1) * (X : Polynomial R)^11))) + (((C ((-138055680 : R) * b^0) * (X : Polynomial R)^11 + C ((-105757736 : R) * b^7) * (X : Polynomial R)^10) + (C ((107992057 : R) * b^6) * (X : Polynomial R)^10 + C ((488410918 : R) * b^5) * (X : Polynomial R)^10)) + ((C ((-50951628 : R) * b^4) * (X : Polynomial R)^10 + C ((466298488 : R) * b^3) * (X : Polynomial R)^10) + (C ((1167494272 : R) * b^2) * (X : Polynomial R)^10 + (C ((639956864 : R) * b^1) * (X : Polynomial R)^10 + C ((101240832 : R) * b^0) * (X : Polynomial R)^10)))))) + (((((C ((84575416 : R) * b^8) * (X : Polynomial R)^9 + C ((457897569 : R) * b^7) * (X : Polynomial R)^9) + (C ((-423187248 : R) * b^6) * (X : Polynomial R)^9 + C ((-487598432 : R) * b^5) * (X : Polynomial R)^9)) + ((C ((624941312 : R) * b^4) * (X : Polynomial R)^9 + C ((-134055888 : R) * b^3) * (X : Polynomial R)^9) + (C ((-819641088 : R) * b^2) * (X : Polynomial R)^9 + C ((-378636544 : R) * b^1) * (X : Polynomial R)^9))) + (((C ((-46018560 : R) * b^0) * (X : Polynomial R)^9 + C ((61771440 : R) * b^9) * (X : Polynomial R)^8) + (C ((-533982882 : R) * b^8) * (X : Polynomial R)^8 + C ((-795199041 : R) * b^7) * (X : Polynomial R)^8)) + ((C ((920669835 : R) * b^6) * (X : Polynomial R)^8 + C ((178620594 : R) * b^5) * (X : Polynomial R)^8) + (C ((-1107508428 : R) * b^4) * (X : Polynomial R)^8 + (C ((-218343960 : R) * b^3) * (X : Polynomial R)^8 + C ((347807232 : R) * b^2) * (X : Polynomial R)^8))))) + ((((C ((138234240 : R) * b^1) * (X : Polynomial R)^8 + C ((11833344 : R) * b^0) * (X : Polynomial R)^8) + (C ((-58757336 : R) * b^10) * (X : Polynomial R)^7 + C ((-65822345 : R) * b^9) * (X : Polynomial R)^7)) + ((C ((1331732933 : R) * b^8) * (X : Polynomial R)^7 + C ((600163934 : R) * b^7) * (X : Polynomial R)^7) + (C ((-1293635116 : R) * b^6) * (X : Polynomial R)^7 + C ((98836144 : R) * b^5) * (X : Polynomial R)^7))) + (((C ((1027468608 : R) * b^4) * (X : Polynomial R)^7 + C ((278562976 : R) * b^3) * (X : Polynomial R)^7) + (C ((-77093248 : R) * b^2) * (X : Polynomial R)^7 + C ((-27999232 : R) * b^1) * (X : Polynomial R)^7)) + ((C ((-1314816 : R) * b^0) * (X : Polynomial R)^7 + C ((-17329720 : R) * b^11) * (X : Polynomial R)^6) + (C ((315478799 : R) * b^10) * (X : Polynomial R)^6 + (C ((-240251601 : R) * b^9) * (X : Polynomial R)^6 + C ((-1721263368 : R) * b^8) * (X : Polynomial R)^6))))))) + ((((((C ((53490740 : R) * b^7) * (X : Polynomial R)^6 + C ((1228365327 : R) * b^6) * (X : Polynomial R)^6) + (C ((-128565094 : R) * b^5) * (X : Polynomial R)^6 + C ((-557545492 : R) * b^4) * (X : Polynomial R)^6)) + ((C ((-143256888 : R) * b^3) * (X : Polynomial R)^6 + C ((4496512 : R) * b^2) * (X : Polynomial R)^6) + (C ((2356352 : R) * b^1) * (X : Polynomial R)^6 + C ((-3666480 : R) * b^12) * (X : Polynomial R)^5))) + (((C ((-109942566 : R) * b^11) * (X : Polynomial R)^5 + C ((-599971215 : R) * b^10) * (X : Polynomial R)^5) + (C ((610641617 : R) * b^9) * (X : Polynomial R)^5 + C ((1248579290 : R) * b^8) * (X : Polynomial R)^5)) + ((C ((-480319011 : R) * b^7) * (X : Polynomial R)^5 + C ((-773491684 : R) * b^6) * (X : Polynomial R)^5) + (C ((45889056 : R) * b^5) * (X : Polynomial R)^5 + C ((172938864 : R) * b^4) * (X : Polynomial R)^5)))) + ((((C ((35288688 : R) * b^3) * (X : Polynomial R)^5 + C ((775936 : R) * b^2) * (X : Polynomial R)^5) + (C ((21928328 : R) * b^13) * (X : Polynomial R)^4 + C ((10721323 : R) * b^12) * (X : Polynomial R)^4)) + ((C ((379412584 : R) * b^11) * (X : Polynomial R)^4 + C ((521597159 : R) * b^10) * (X : Polynomial R)^4) + (C ((-622274083 : R) * b^9) * (X : Polynomial R)^4 + C ((-522632408 : R) * b^8) * (X : Polynomial R)^4))) + (((C ((381230413 : R) * b^7) * (X : Polynomial R)^4 + C ((299652533 : R) * b^6) * (X : Polynomial R)^4) + (C ((-2965074 : R) * b^5) * (X : Polynomial R)^4 + C ((-27033908 : R) * b^4) * (X : Polynomial R)^4)) + ((C ((-3298952 : R) * b^3) * (X : Polynomial R)^4 + C ((6253720 : R) * b^14) * (X : Polynomial R)^3) + (C ((-6121075 : R) * b^13) * (X : Polynomial R)^3 + (C ((-30525463 : R) * b^12) * (X : Polynomial R)^3 + C ((-397217716 : R) * b^11) * (X : Polynomial R)^3)))))) + (((((C ((-183175273 : R) * b^10) * (X : Polynomial R)^3 + C ((360103188 : R) * b^9) * (X : Polynomial R)^3) + (C ((137704477 : R) * b^8) * (X : Polynomial R)^3 + C ((-126531840 : R) * b^7) * (X : Polynomial R)^3)) + ((C ((-60883208 : R) * b^6) * (X : Polynomial R)^3 + C ((-1006896 : R) * b^5) * (X : Polynomial R)^3) + (C ((1481520 : R) * b^4) * (X : Polynomial R)^3 + C ((-12208160 : R) * b^15) * (X : Polynomial R)^2))) + (((C ((-17599208 : R) * b^14) * (X : Polynomial R)^2 + C ((-45540924 : R) * b^13) * (X : Polynomial R)^2) + (C ((25570965 : R) * b^12) * (X : Polynomial R)^2 + C ((164605488 : R) * b^11) * (X : Polynomial R)^2)) + ((C ((-11384076 : R) * b^10) * (X : Polynomial R)^2 + C ((-124786956 : R) * b^9) * (X : Polynomial R)^2) + (C ((-29884834 : R) * b^8) * (X : Polynomial R)^2 + (C ((14801004 : R) * b^7) * (X : Polynomial R)^2 + C ((4388320 : R) * b^6) * (X : Polynomial R)^2))))) + ((((C ((1528984 : R) * b^16) * (X : Polynomial R)^1 + C ((15864033 : R) * b^15) * (X : Polynomial R)^1) + (C ((23224069 : R) * b^14) * (X : Polynomial R)^1 + C ((35493199 : R) * b^13) * (X : Polynomial R)^1)) + ((C ((-15108345 : R) * b^12) * (X : Polynomial R)^1 + C ((-32123964 : R) * b^11) * (X : Polynomial R)^1) + (C ((12588474 : R) * b^10) * (X : Polynomial R)^1 + C ((19459008 : R) * b^9) * (X : Polynomial R)^1))) + (((C ((4310120 : R) * b^8) * (X : Polynomial R)^1 + C ((960520 : R) * b^17) * (X : Polynomial R)^0) + (C ((-2391609 : R) * b^16) * (X : Polynomial R)^0 + C ((-2601574 : R) * b^15) * (X : Polynomial R)^0)) + ((C ((-2463507 : R) * b^14) * (X : Polynomial R)^0 + C ((1450942 : R) * b^13) * (X : Polynomial R)^0) + (C ((9415154 : R) * b^12) * (X : Polynomial R)^0 + (C ((6961040 : R) * b^11) * (X : Polynomial R)^0 + C ((1403320 : R) * b^10) * (X : Polynomial R)^0))))))))

private def vD {R : Type*} [CommRing R] (t b : R) : R :=
    (((((5 : R)*t^4*b^4 + (40 : R)*t^4*b^3) + ((20 : R)*t^4*b^2 + ((-5 : R)*t^3*b^4 + (-50 : R)*t^3*b^3))) + (((-100 : R)*t^3*b^2 + (-40 : R)*t^3*b^1) + ((-10 : R)*t^2*b^4 + ((-35 : R)*t^2*b^3 + (65 : R)*t^2*b^2)))) + ((((80 : R)*t^2*b^1 + (20 : R)*t^2*b^0) + ((5 : R)*t^1*b^4 + ((30 : R)*t^1*b^3 + (30 : R)*t^1*b^2))) + (((-30 : R)*t^1*b^1 + (-20 : R)*t^1*b^0) + ((5 : R)*t^0*b^4 + ((-40 : R)*t^0*b^2 + (-20 : R)*t^0*b^1)))))

private def vN0 {R : Type*} [CommRing R] (t b : R) : R :=
    (((((-768 : R)*t^6*b^4 + ((96 : R)*t^6*b^3 + (1536 : R)*t^5*b^4)) + (((2112 : R)*t^5*b^3 + (-288 : R)*t^5*b^2) + ((2232 : R)*t^4*b^4 + (-2376 : R)*t^4*b^3))) + (((-1440 : R)*t^4*b^2 + ((288 : R)*t^4*b^1 + (-3648 : R)*t^3*b^4)) + (((-5511 : R)*t^3*b^3 + (-270 : R)*t^3*b^2) + ((-384 : R)*t^3*b^1 + (-96 : R)*t^3*b^0)))) + ((((-1368 : R)*t^2*b^4 + ((4869 : R)*t^2*b^3 + (4224 : R)*t^2*b^2)) + (((1500 : R)*t^2*b^1 + (480 : R)*t^2*b^0) + ((1872 : R)*t^1*b^4 + (1437 : R)*t^1*b^3))) + (((-1917 : R)*t^1*b^2 + ((-1125 : R)*t^1*b^1 + (-390 : R)*t^1*b^0)) + (((-216 : R)*t^0*b^4 + (-2238 : R)*t^0*b^3) + ((-1395 : R)*t^0*b^2 + (-390 : R)*t^0*b^1)))))

private def vN1 {R : Type*} [CommRing R] (t b : R) : R :=
    (((((-2655 : R)*t^6*b^4 + ((-270 : R)*t^6*b^3 + (5310 : R)*t^5*b^4)) + (((8505 : R)*t^5*b^3 + (810 : R)*t^5*b^2) + ((13050 : R)*t^4*b^4 + (-5595 : R)*t^4*b^3))) + (((-8295 : R)*t^4*b^2 + ((-810 : R)*t^4*b^1 + (-17880 : R)*t^3*b^4)) + (((-33168 : R)*t^3*b^3 + (-5574 : R)*t^3*b^2) + ((1695 : R)*t^3*b^1 + (270 : R)*t^3*b^0)))) + ((((-9750 : R)*t^2*b^4 + ((25266 : R)*t^2*b^3 + (26640 : R)*t^2*b^2)) + (((6891 : R)*t^2*b^1 + (750 : R)*t^2*b^0) + ((10650 : R)*t^1*b^4 + (9750 : R)*t^1*b^3))) + (((-11472 : R)*t^1*b^2 + ((-7320 : R)*t^1*b^1 + (-1032 : R)*t^1*b^0)) + (((-1125 : R)*t^0*b^4 + (-13293 : R)*t^0*b^3) + ((-7458 : R)*t^0*b^2 + (-1032 : R)*t^0*b^1)))))

private def vN2 {R : Type*} [CommRing R] (t b : R) : R :=
    (((((-12384 : R)*t^6*b^4 + ((-2304 : R)*t^6*b^3 + (24768 : R)*t^5*b^4)) + (((41760 : R)*t^5*b^3 + (6912 : R)*t^5*b^2) + ((48720 : R)*t^4*b^4 + (-32895 : R)*t^4*b^3))) + (((-44742 : R)*t^4*b^2 + ((-6912 : R)*t^4*b^1 + (-71088 : R)*t^3*b^4)) + (((-125037 : R)*t^3*b^3 + (-11076 : R)*t^3*b^2) + ((13740 : R)*t^3*b^1 + (2304 : R)*t^3*b^0)))) + ((((-35472 : R)*t^2*b^4 + ((100284 : R)*t^2*b^3 + (101658 : R)*t^2*b^2)) + (((23157 : R)*t^2*b^1 + (1626 : R)*t^2*b^0) + ((39120 : R)*t^1*b^4 + (33873 : R)*t^1*b^3))) + (((-46548 : R)*t^1*b^2 + ((-29001 : R)*t^1*b^1 + (-3954 : R)*t^1*b^0)) + (((-3264 : R)*t^0*b^4 + (-49569 : R)*t^0*b^3) + ((-28335 : R)*t^0*b^2 + (-3954 : R)*t^0*b^1)))))

private def vDt {R : Type*} [CommRing R] (t b : R) : R :=
    (((((20 : R)*t^3*b^4 + (160 : R)*t^3*b^3) + ((80 : R)*t^3*b^2 + (-15 : R)*t^2*b^4)) + (((-150 : R)*t^2*b^3 + (-300 : R)*t^2*b^2) + ((-120 : R)*t^2*b^1 + (-20 : R)*t^1*b^4))) + ((((-70 : R)*t^1*b^3 + (130 : R)*t^1*b^2) + ((160 : R)*t^1*b^1 + (40 : R)*t^1*b^0)) + (((5 : R)*t^0*b^4 + (30 : R)*t^0*b^3) + ((30 : R)*t^0*b^2 + ((-30 : R)*t^0*b^1 + (-20 : R)*t^0*b^0)))))

private def vDb {R : Type*} [CommRing R] (t b : R) : R :=
    (((((20 : R)*t^4*b^3 + (120 : R)*t^4*b^2) + ((40 : R)*t^4*b^1 + (-20 : R)*t^3*b^3)) + (((-150 : R)*t^3*b^2 + (-200 : R)*t^3*b^1) + ((-40 : R)*t^3*b^0 + ((-40 : R)*t^2*b^3 + (-105 : R)*t^2*b^2)))) + ((((130 : R)*t^2*b^1 + (80 : R)*t^2*b^0) + ((20 : R)*t^1*b^3 + (90 : R)*t^1*b^2)) + (((60 : R)*t^1*b^1 + (-30 : R)*t^1*b^0) + ((20 : R)*t^0*b^3 + ((-80 : R)*t^0*b^1 + (-20 : R)*t^0*b^0)))))

private def vNt0 {R : Type*} [CommRing R] (t b : R) : R :=
    (((((-4608 : R)*t^5*b^4 + ((576 : R)*t^5*b^3 + (7680 : R)*t^4*b^4)) + ((10560 : R)*t^4*b^3 + ((-1440 : R)*t^4*b^2 + (8928 : R)*t^3*b^4))) + (((-9504 : R)*t^3*b^3 + ((-5760 : R)*t^3*b^2 + (1152 : R)*t^3*b^1)) + ((-10944 : R)*t^2*b^4 + ((-16533 : R)*t^2*b^3 + (-810 : R)*t^2*b^2)))) + ((((-1152 : R)*t^2*b^1 + ((-288 : R)*t^2*b^0 + (-2736 : R)*t^1*b^4)) + ((9738 : R)*t^1*b^3 + ((8448 : R)*t^1*b^2 + (3000 : R)*t^1*b^1))) + (((960 : R)*t^1*b^0 + ((1872 : R)*t^0*b^4 + (1437 : R)*t^0*b^3)) + ((-1917 : R)*t^0*b^2 + ((-1125 : R)*t^0*b^1 + (-390 : R)*t^0*b^0)))))

private def vNb0 {R : Type*} [CommRing R] (t b : R) : R :=
    (((((-3072 : R)*t^6*b^3 + ((288 : R)*t^6*b^2 + (6144 : R)*t^5*b^3)) + ((6336 : R)*t^5*b^2 + ((-576 : R)*t^5*b^1 + (8928 : R)*t^4*b^3))) + (((-7128 : R)*t^4*b^2 + ((-2880 : R)*t^4*b^1 + (288 : R)*t^4*b^0)) + ((-14592 : R)*t^3*b^3 + ((-16533 : R)*t^3*b^2 + (-540 : R)*t^3*b^1)))) + ((((-384 : R)*t^3*b^0 + ((-5472 : R)*t^2*b^3 + (14607 : R)*t^2*b^2)) + ((8448 : R)*t^2*b^1 + ((1500 : R)*t^2*b^0 + (7488 : R)*t^1*b^3))) + (((4311 : R)*t^1*b^2 + ((-3834 : R)*t^1*b^1 + (-1125 : R)*t^1*b^0)) + (((-864 : R)*t^0*b^3 + (-6714 : R)*t^0*b^2) + ((-2790 : R)*t^0*b^1 + (-390 : R)*t^0*b^0)))))

private def vNt1 {R : Type*} [CommRing R] (t b : R) : R :=
    (((((-15930 : R)*t^5*b^4 + ((-1620 : R)*t^5*b^3 + (26550 : R)*t^4*b^4)) + ((42525 : R)*t^4*b^3 + ((4050 : R)*t^4*b^2 + (52200 : R)*t^3*b^4))) + (((-22380 : R)*t^3*b^3 + ((-33180 : R)*t^3*b^2 + (-3240 : R)*t^3*b^1)) + ((-53640 : R)*t^2*b^4 + ((-99504 : R)*t^2*b^3 + (-16722 : R)*t^2*b^2)))) + ((((5085 : R)*t^2*b^1 + ((810 : R)*t^2*b^0 + (-19500 : R)*t^1*b^4)) + ((50532 : R)*t^1*b^3 + ((53280 : R)*t^1*b^2 + (13782 : R)*t^1*b^1))) + (((1500 : R)*t^1*b^0 + ((10650 : R)*t^0*b^4 + (9750 : R)*t^0*b^3)) + ((-11472 : R)*t^0*b^2 + ((-7320 : R)*t^0*b^1 + (-1032 : R)*t^0*b^0)))))

private def vNb1 {R : Type*} [CommRing R] (t b : R) : R :=
    (((((-10620 : R)*t^6*b^3 + ((-810 : R)*t^6*b^2 + (21240 : R)*t^5*b^3)) + ((25515 : R)*t^5*b^2 + ((1620 : R)*t^5*b^1 + (52200 : R)*t^4*b^3))) + (((-16785 : R)*t^4*b^2 + ((-16590 : R)*t^4*b^1 + (-810 : R)*t^4*b^0)) + ((-71520 : R)*t^3*b^3 + ((-99504 : R)*t^3*b^2 + (-11148 : R)*t^3*b^1)))) + ((((1695 : R)*t^3*b^0 + ((-39000 : R)*t^2*b^3 + (75798 : R)*t^2*b^2)) + ((53280 : R)*t^2*b^1 + ((6891 : R)*t^2*b^0 + (42600 : R)*t^1*b^3))) + (((29250 : R)*t^1*b^2 + ((-22944 : R)*t^1*b^1 + (-7320 : R)*t^1*b^0)) + (((-4500 : R)*t^0*b^3 + (-39879 : R)*t^0*b^2) + ((-14916 : R)*t^0*b^1 + (-1032 : R)*t^0*b^0)))))

private def vNt2 {R : Type*} [CommRing R] (t b : R) : R :=
    (((((-74304 : R)*t^5*b^4 + ((-13824 : R)*t^5*b^3 + (123840 : R)*t^4*b^4)) + ((208800 : R)*t^4*b^3 + ((34560 : R)*t^4*b^2 + (194880 : R)*t^3*b^4))) + (((-131580 : R)*t^3*b^3 + ((-178968 : R)*t^3*b^2 + (-27648 : R)*t^3*b^1)) + ((-213264 : R)*t^2*b^4 + ((-375111 : R)*t^2*b^3 + (-33228 : R)*t^2*b^2)))) + ((((41220 : R)*t^2*b^1 + ((6912 : R)*t^2*b^0 + (-70944 : R)*t^1*b^4)) + ((200568 : R)*t^1*b^3 + ((203316 : R)*t^1*b^2 + (46314 : R)*t^1*b^1))) + (((3252 : R)*t^1*b^0 + ((39120 : R)*t^0*b^4 + (33873 : R)*t^0*b^3)) + ((-46548 : R)*t^0*b^2 + ((-29001 : R)*t^0*b^1 + (-3954 : R)*t^0*b^0)))))

private def vNb2 {R : Type*} [CommRing R] (t b : R) : R :=
    (((((-49536 : R)*t^6*b^3 + ((-6912 : R)*t^6*b^2 + (99072 : R)*t^5*b^3)) + ((125280 : R)*t^5*b^2 + ((13824 : R)*t^5*b^1 + (194880 : R)*t^4*b^3))) + (((-98685 : R)*t^4*b^2 + ((-89484 : R)*t^4*b^1 + (-6912 : R)*t^4*b^0)) + ((-284352 : R)*t^3*b^3 + ((-375111 : R)*t^3*b^2 + (-22152 : R)*t^3*b^1)))) + ((((13740 : R)*t^3*b^0 + ((-141888 : R)*t^2*b^3 + (300852 : R)*t^2*b^2)) + ((203316 : R)*t^2*b^1 + ((23157 : R)*t^2*b^0 + (156480 : R)*t^1*b^3))) + (((101619 : R)*t^1*b^2 + ((-93096 : R)*t^1*b^1 + (-29001 : R)*t^1*b^0)) + (((-13056 : R)*t^0*b^3 + (-148707 : R)*t^0*b^2) + ((-56670 : R)*t^0*b^1 + (-3954 : R)*t^0*b^0)))))

private theorem expanded_D {R : Type*} [CommRing R] (t b : R) :
    sourceD t b = vD t b := by
  unfold sourceD sourceN sourceJ vD
  ring
private theorem expanded_N0 {R : Type*} [CommRing R] (t b : R) :
    sourceNumerator t b 0 = vN0 t b := by
  simp only [sourceNumerator,sourceC,sourceD,sourceN,sourceJ,vN0,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  ring
private theorem expanded_N1 {R : Type*} [CommRing R] (t b : R) :
    sourceNumerator t b 1 = vN1 t b := by
  simp only [sourceNumerator,sourceC,sourceD,sourceN,sourceJ,vN1,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  ring
private theorem expanded_N2 {R : Type*} [CommRing R] (t b : R) :
    sourceNumerator t b 2 = vN2 t b := by
  simp only [sourceNumerator,sourceC,sourceD,sourceN,sourceJ,vN2,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  ring
private theorem partial_Dt (t b : ℝ) :
    (sourceD (X : Polynomial ℝ) (C b)).derivative.eval t = vDt t b := by
  rw [expanded_D]
  simp only [vD,vDt,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,derivative_C,derivative_X,derivative_natCast,derivative_ofNat,
    derivative_neg,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,
    eval_natCast,eval_neg,eval_zero,eval_one,eval_ofNat]
  ring
private theorem partial_Db (t b : ℝ) :
    (sourceD (C t) (X : Polynomial ℝ)).derivative.eval b = vDb t b := by
  rw [expanded_D]
  simp only [vD,vDb,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,derivative_C,derivative_X,derivative_natCast,derivative_ofNat,
    derivative_neg,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,
    eval_natCast,eval_neg,eval_zero,eval_one,eval_ofNat]
  ring
private theorem partial_Nt0 (t b : ℝ) :
    (sourceNumerator (X : Polynomial ℝ) (C b) 0).derivative.eval t = vNt0 t b := by
  rw [expanded_N0]
  simp only [vN0,vNt0,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,derivative_C,derivative_X,derivative_natCast,derivative_ofNat,
    derivative_neg,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,
    eval_natCast,eval_neg,eval_zero,eval_one,eval_ofNat]
  ring
private theorem partial_Nt1 (t b : ℝ) :
    (sourceNumerator (X : Polynomial ℝ) (C b) 1).derivative.eval t = vNt1 t b := by
  rw [expanded_N1]
  simp only [vN1,vNt1,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,derivative_C,derivative_X,derivative_natCast,derivative_ofNat,
    derivative_neg,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,
    eval_natCast,eval_neg,eval_zero,eval_one,eval_ofNat]
  ring
private theorem partial_Nt2 (t b : ℝ) :
    (sourceNumerator (X : Polynomial ℝ) (C b) 2).derivative.eval t = vNt2 t b := by
  rw [expanded_N2]
  simp only [vN2,vNt2,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,derivative_C,derivative_X,derivative_natCast,derivative_ofNat,
    derivative_neg,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,
    eval_natCast,eval_neg,eval_zero,eval_one,eval_ofNat]
  ring
private theorem partial_Nb0 (t b : ℝ) :
    (sourceNumerator (C t) (X : Polynomial ℝ) 0).derivative.eval b = vNb0 t b := by
  rw [expanded_N0]
  simp only [vN0,vNb0,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,derivative_C,derivative_X,derivative_natCast,derivative_ofNat,
    derivative_neg,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,
    eval_natCast,eval_neg,eval_zero,eval_one,eval_ofNat]
  ring
private theorem partial_Nb1 (t b : ℝ) :
    (sourceNumerator (C t) (X : Polynomial ℝ) 1).derivative.eval b = vNb1 t b := by
  rw [expanded_N1]
  simp only [vN1,vNb1,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,derivative_C,derivative_X,derivative_natCast,derivative_ofNat,
    derivative_neg,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,
    eval_natCast,eval_neg,eval_zero,eval_one,eval_ofNat]
  ring
private theorem partial_Nb2 (t b : ℝ) :
    (sourceNumerator (C t) (X : Polynomial ℝ) 2).derivative.eval b = vNb2 t b := by
  rw [expanded_N2]
  simp only [vN2,vNb2,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,derivative_C,derivative_X,derivative_natCast,derivative_ofNat,
    derivative_neg,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,
    eval_natCast,eval_neg,eval_zero,eval_one,eval_ofNat]
  ring
private def sourceQuotient (k : Fin 3) (t b : ℝ) : ℝ :=
  sourceD t b*((sourceNumerator (X : Polynomial ℝ) (C b) 0).derivative.eval t *
    (sourceNumerator (C t) (X : Polynomial ℝ) k).derivative.eval b -
    (sourceNumerator (C t) (X : Polynomial ℝ) 0).derivative.eval b *
    (sourceNumerator (X : Polynomial ℝ) (C b) k).derivative.eval t) -
  sourceNumerator t b 0*((sourceD (X : Polynomial ℝ) (C b)).derivative.eval t *
    (sourceNumerator (C t) (X : Polynomial ℝ) k).derivative.eval b -
    (sourceD (C t) (X : Polynomial ℝ)).derivative.eval b *
    (sourceNumerator (X : Polynomial ℝ) (C b) k).derivative.eval t) -
  sourceNumerator t b k*((sourceNumerator (X : Polynomial ℝ) (C b) 0).derivative.eval t *
    (sourceD (C t) (X : Polynomial ℝ)).derivative.eval b -
    (sourceNumerator (C t) (X : Polynomial ℝ) 0).derivative.eval b *
    (sourceD (X : Polynomial ℝ) (C b)).derivative.eval t)
private theorem source_factor (k : Fin 3) (t b : ℝ) :
    sourceBt 0 t b*sourceBb k t b-sourceBb 0 t b*sourceBt k t b =
      sourceD t b*sourceQuotient k t b := by
  unfold sourceBt sourceBb sourceQuotient
  ring
private def p00 (t b : ℝ) : ℝ :=
    (((((((-2773440 : ℝ)*t^11*b^6 + (10169280 : ℝ)*t^10*b^6) + ((15253920 : ℝ)*t^10*b^5 + (-32771520 : ℝ)*t^9*b^7)) + (((8997840 : ℝ)*t^9*b^6 + (-44995680 : ℝ)*t^9*b^5) + ((-34668000 : ℝ)*t^9*b^4 + ((81328320 : ℝ)*t^8*b^7 + (89131194 : ℝ)*t^8*b^6)))) + ((((-53102682 : ℝ)*t^8*b^5 + (77906628 : ℝ)*t^8*b^4) + ((41601600 : ℝ)*t^8*b^3 + (-3047040 : ℝ)*t^7*b^7)) + (((-301489884 : ℝ)*t^7*b^6 + (-5679846 : ℝ)*t^7*b^5) + ((129167244 : ℝ)*t^7*b^4 + ((-65055312 : ℝ)*t^7*b^3 + (-27734400 : ℝ)*t^7*b^2))))) + (((((-125930880 : ℝ)*t^6*b^7 + (100451232 : ℝ)*t^6*b^6) + ((391282182 : ℝ)*t^6*b^5 + (-234386118 : ℝ)*t^6*b^4)) + (((-165191472 : ℝ)*t^6*b^3 + (25143768 : ℝ)*t^6*b^2) + ((9707040 : ℝ)*t^6*b^1 + ((78384960 : ℝ)*t^5*b^7 + (324484938 : ℝ)*t^5*b^6)))) + ((((-293737266 : ℝ)*t^5*b^5 + (-160125003 : ℝ)*t^5*b^4) + ((340376148 : ℝ)*t^5*b^3 + (116630172 : ℝ)*t^5*b^2)) + (((-2785392 : ℝ)*t^5*b^1 + (-1386720 : ℝ)*t^5*b^0) + ((24906240 : ℝ)*t^4*b^7 + ((-262478592 : ℝ)*t^4*b^6 + (-231772149 : ℝ)*t^4*b^5)))))) + ((((((332198595 : ℝ)*t^4*b^4 + (-73596447 : ℝ)*t^4*b^3) + ((-209767482 : ℝ)*t^4*b^2 + (-42828534 : ℝ)*t^4*b^1)) + (((-383292 : ℝ)*t^4*b^0 + (-38113920 : ℝ)*t^3*b^7) + ((-26742042 : ℝ)*t^3*b^6 + ((273828276 : ℝ)*t^3*b^5 + (-37665522 : ℝ)*t^3*b^4)))) + ((((-170404812 : ℝ)*t^3*b^3 + (83148759 : ℝ)*t^3*b^2) + ((58963698 : ℝ)*t^3*b^1 + (6327432 : ℝ)*t^3*b^0)) + (((17634240 : ℝ)*t^2*b^7 + (88853850 : ℝ)*t^2*b^6) + ((-1778409 : ℝ)*t^2*b^5 + ((-83405052 : ℝ)*t^2*b^4 + (101039409 : ℝ)*t^2*b^3))))) + (((((37741059 : ℝ)*t^2*b^2 + (-21836007 : ℝ)*t^2*b^1) + ((-5866074 : ℝ)*t^2*b^0 + (-4536000 : ℝ)*t^1*b^7)) + (((-24923358 : ℝ)*t^1*b^6 + (-52527690 : ℝ)*t^1*b^5) + ((13142484 : ℝ)*t^1*b^4 + ((-7616160 : ℝ)*t^1*b^3 + (-30533184 : ℝ)*t^1*b^2)))) + ((((-2863908 : ℝ)*t^1*b^1 + (1288080 : ℝ)*t^1*b^0) + ((777600 : ℝ)*t^0*b^7 + (-1191888 : ℝ)*t^0*b^6)) + (((8660817 : ℝ)*t^0*b^5 + (6152859 : ℝ)*t^0*b^4) + ((-4512645 : ℝ)*t^0*b^3 + ((2485926 : ℝ)*t^0*b^2 + (1244160 : ℝ)*t^0*b^1)))))))
private theorem pair00 (t b : ℝ) : vNt0 t b*vNb1 t b-vNb0 t b*vNt1 t b = p00 t b := by
  unfold vNt0 vNb1 vNb0 vNt1 p00
  ring
private def z00 (t b : ℝ) : ℝ :=
    ((((((((-13867200 : ℝ)*t^15*b^10 + (-110937600 : ℝ)*t^15*b^9) + ((-55468800 : ℝ)*t^15*b^8 + (64713600 : ℝ)*t^14*b^10)) + (((621712800 : ℝ)*t^14*b^9 + (1090886400 : ℝ)*t^14*b^8) + ((416016000 : ℝ)*t^14*b^7 + ((-163857600 : ℝ)*t^13*b^11 + (-1288983600 : ℝ)*t^13*b^10)))) + ((((-1008158400 : ℝ)*t^13*b^9 + (-3753108000 : ℝ)*t^13*b^8) + ((-4440672000 : ℝ)*t^13*b^7 + (-1358985600 : ℝ)*t^13*b^6)) + (((570499200 : ℝ)*t^12*b^11 + (5176815570 : ℝ)*t^12*b^10) + ((7386871950 : ℝ)*t^12*b^9 + ((2926163340 : ℝ)*t^12*b^8 + (10023524280 : ℝ)*t^12*b^7))))) + (((((9967991760 : ℝ)*t^12*b^6 + (2523830400 : ℝ)*t^12*b^5) + ((-94161600 : ℝ)*t^11*b^11 + (-5047398990 : ℝ)*t^11*b^10)) + (((-26086582080 : ℝ)*t^11*b^9 + (-14753506140 : ℝ)*t^11*b^8) + ((930562920 : ℝ)*t^11*b^7 + ((-14238295920 : ℝ)*t^11*b^6 + (-13665339360 : ℝ)*t^11*b^5)))) + ((((-2912112000 : ℝ)*t^11*b^4 + (-1591560000 : ℝ)*t^10*b^11) + ((-7500290760 : ℝ)*t^10*b^10 + ((20699296650 : ℝ)*t^10*b^9 + (59099827410 : ℝ)*t^10*b^8))) + (((3463417890 : ℝ)*t^10*b^7 + (-19500676020 : ℝ)*t^10*b^6) + ((10290552120 : ℝ)*t^10*b^5 + ((11846430000 : ℝ)*t^10*b^4 + (2135548800 : ℝ)*t^10*b^3)))))) + ((((((1294833600 : ℝ)*t^9*b^11 + (16604150940 : ℝ)*t^9*b^10) + ((35037567090 : ℝ)*t^9*b^9 + (-51241251195 : ℝ)*t^9*b^8)) + (((-71326996290 : ℝ)*t^9*b^7 + (37065178440 : ℝ)*t^9*b^6) + ((43675825320 : ℝ)*t^9*b^5 + ((-1407812400 : ℝ)*t^9*b^4 + (-6439521600 : ℝ)*t^9*b^3)))) + ((((-970704000 : ℝ)*t^9*b^2 + (1383321600 : ℝ)*t^8*b^11) + ((-3607952220 : ℝ)*t^8*b^10 + ((-62051211495 : ℝ)*t^8*b^9 + (-61132149720 : ℝ)*t^8*b^8))) + (((84823942815 : ℝ)*t^8*b^7 + (42348742200 : ℝ)*t^8*b^6) + ((-75934069290 : ℝ)*t^8*b^5 + ((-49946458500 : ℝ)*t^8*b^4 + (-3717466200 : ℝ)*t^8*b^3))))) + (((((2076548400 : ℝ)*t^8*b^2 + (249609600 : ℝ)*t^8*b^1) + ((-1743840000 : ℝ)*t^7*b^11 + (-12362628690 : ℝ)*t^7*b^10)) + (((9290273715 : ℝ)*t^7*b^9 + (114777929385 : ℝ)*t^7*b^8) + ((40504237380 : ℝ)*t^7*b^7 + ((-97671811320 : ℝ)*t^7*b^6 + (-555696180 : ℝ)*t^7*b^5)))) + ((((74936491380 : ℝ)*t^7*b^4 + (33525925560 : ℝ)*t^7*b^3) + ((3103567920 : ℝ)*t^7*b^2 + ((-345454560 : ℝ)*t^7*b^1 + (-27734400 : ℝ)*t^7*b^0))) + (((-208051200 : ℝ)*t^6*b^11 + (9418342230 : ℝ)*t^6*b^10) + ((38411734005 : ℝ)*t^6*b^9 + ((-23195085750 : ℝ)*t^6*b^8 + (-114603261525 : ℝ)*t^6*b^7))))))) + (((((((15943838310 : ℝ)*t^6*b^6 + (78161593410 : ℝ)*t^6*b^5) + ((-17304549390 : ℝ)*t^6*b^4 + (-42556570290 : ℝ)*t^6*b^3)) + (((-13239943020 : ℝ)*t^6*b^2 + (-1043021880 : ℝ)*t^6*b^1) + ((20068560 : ℝ)*t^6*b^0 + ((786744000 : ℝ)*t^5*b^11 + (1026588510 : ℝ)*t^5*b^10)))) + ((((-24717349350 : ℝ)*t^5*b^9 + (-54874790190 : ℝ)*t^5*b^8) + ((34628061510 : ℝ)*t^5*b^7 + ((58807205955 : ℝ)*t^5*b^6 + (-46518462630 : ℝ)*t^5*b^5))) + (((-42016899825 : ℝ)*t^5*b^4 + (12063902670 : ℝ)*t^5*b^3) + ((13857046920 : ℝ)*t^5*b^2 + ((2815915320 : ℝ)*t^5*b^1 + (134214480 : ℝ)*t^5*b^0))))) + (((((-215812800 : ℝ)*t^4*b^11 + (-3718696320 : ℝ)*t^4*b^10) + ((-2703935970 : ℝ)*t^4*b^9 + (33700030245 : ℝ)*t^4*b^8)) + (((37231480125 : ℝ)*t^4*b^7 + (-29632711770 : ℝ)*t^4*b^6) + ((-10034407080 : ℝ)*t^4*b^5 + ((33306523650 : ℝ)*t^4*b^4 + (14075100765 : ℝ)*t^4*b^3)))) + ((((-3757766670 : ℝ)*t^4*b^2 + (-2318960340 : ℝ)*t^4*b^1) + ((-243870120 : ℝ)*t^4*b^0 + ((-60926400 : ℝ)*t^3*b^11 + (1214659260 : ℝ)*t^3*b^10))) + (((7120733580 : ℝ)*t^3*b^9 + (2658268935 : ℝ)*t^3*b^8) + ((-23325121080 : ℝ)*t^3*b^7 + ((-8583228990 : ℝ)*t^3*b^6 + (15134003235 : ℝ)*t^3*b^5)))))) + ((((((-3175515900 : ℝ)*t^3*b^4 + (-11055673260 : ℝ)*t^3*b^3) + ((-2513911950 : ℝ)*t^3*b^2 + (531921960 : ℝ)*t^3*b^1)) + (((143083080 : ℝ)*t^3*b^0 + (57715200 : ℝ)*t^2*b^11) + ((168275340 : ℝ)*t^2*b^10 + ((-1855028925 : ℝ)*t^2*b^9 + (-6825524985 : ℝ)*t^2*b^8)))) + ((((-1269029385 : ℝ)*t^2*b^7 + (6849943965 : ℝ)*t^2*b^6) + ((-2712501810 : ℝ)*t^2*b^5 + ((-4709512980 : ℝ)*t^2*b^4 + (1329154560 : ℝ)*t^2*b^3))) + (((1555837740 : ℝ)*t^2*b^2 + (160840440 : ℝ)*t^2*b^1) + ((-25761600 : ℝ)*t^2*b^0 + ((-18792000 : ℝ)*t^1*b^11 + (-107248230 : ℝ)*t^1*b^10))))) + (((((-50323005 : ℝ)*t^1*b^9 + (1384870905 : ℝ)*t^1*b^8) + ((3003545655 : ℝ)*t^1*b^7 + (197837820 : ℝ)*t^1*b^6)) + (((-384905700 : ℝ)*t^1*b^5 + (1504315710 : ℝ)*t^1*b^4) + ((778219920 : ℝ)*t^1*b^3 + ((-81288360 : ℝ)*t^1*b^2 + (-50644800 : ℝ)*t^1*b^1)))) + ((((3888000 : ℝ)*t^0*b^11 + (-5959440 : ℝ)*t^0*b^10) + ((12200085 : ℝ)*t^0*b^9 + ((62887815 : ℝ)*t^0*b^8 + (-345158145 : ℝ)*t^0*b^7))) + (((-406901070 : ℝ)*t^0*b^6 + (63669420 : ℝ)*t^0*b^5) + ((-9184140 : ℝ)*t^0*b^4 + ((-99484920 : ℝ)*t^0*b^3 + (-24883200 : ℝ)*t^0*b^2))))))))
private theorem product00 (t b : ℝ) : vD t b*p00 t b = z00 t b := by
  unfold vD p00 z00
  ring
private def p01 (t b : ℝ) : ℝ :=
    (((((((106200 : ℝ)*t^9*b^7 + (228600 : ℝ)*t^9*b^6) + ((-147600 : ℝ)*t^9*b^5 + (-265500 : ℝ)*t^8*b^7)) + (((-944550 : ℝ)*t^8*b^6 + (-553500 : ℝ)*t^8*b^5) + ((669600 : ℝ)*t^8*b^4 + (-212400 : ℝ)*t^7*b^7))) + ((((2486325 : ℝ)*t^7*b^6 + (4542900 : ℝ)*t^7*b^5) + ((336900 : ℝ)*t^7*b^4 + (-1202400 : ℝ)*t^7*b^3)) + (((806100 : ℝ)*t^6*b^7 + (-1567125 : ℝ)*t^6*b^6) + ((-11041605 : ℝ)*t^6*b^5 + (-10694100 : ℝ)*t^6*b^4)))) + (((((-80460 : ℝ)*t^6*b^3 + (1065600 : ℝ)*t^6*b^2) + ((547800 : ℝ)*t^5*b^7 + (-2385525 : ℝ)*t^5*b^6)) + (((6749370 : ℝ)*t^5*b^5 + (21739815 : ℝ)*t^5*b^4) + ((12959640 : ℝ)*t^5*b^3 + (325980 : ℝ)*t^5*b^2))) + ((((-464400 : ℝ)*t^5*b^1 + (-1195200 : ℝ)*t^4*b^7) + ((2491965 : ℝ)*t^4*b^6 + (6854400 : ℝ)*t^4*b^5)) + (((-9541575 : ℝ)*t^4*b^4 + (-20913405 : ℝ)*t^4*b^3) + ((-8209890 : ℝ)*t^4*b^2 + (-362280 : ℝ)*t^4*b^1))))) + ((((((79200 : ℝ)*t^4*b^0 + (-844800 : ℝ)*t^3*b^7) + ((-743850 : ℝ)*t^3*b^6 + (-9807300 : ℝ)*t^3*b^5)) + (((-10624245 : ℝ)*t^3*b^4 + (6213900 : ℝ)*t^3*b^3) + ((9917940 : ℝ)*t^3*b^2 + (2526660 : ℝ)*t^3*b^1))) + ((((104760 : ℝ)*t^3*b^0 + (909300 : ℝ)*t^2*b^7) + ((1157865 : ℝ)*t^2*b^6 + (3655440 : ℝ)*t^2*b^5)) + (((10764915 : ℝ)*t^2*b^4 + (7246170 : ℝ)*t^2*b^3) + ((-1790910 : ℝ)*t^2*b^2 + (-2027730 : ℝ)*t^2*b^1)))) + (((((-286860 : ℝ)*t^2*b^0 + (480000 : ℝ)*t^1*b^7) + ((372690 : ℝ)*t^1*b^6 + (632970 : ℝ)*t^1*b^5)) + (((-1674630 : ℝ)*t^1*b^4 + (-4161600 : ℝ)*t^1*b^3) + ((-1876080 : ℝ)*t^1*b^2 + (154680 : ℝ)*t^1*b^1))) + ((((104160 : ℝ)*t^1*b^0 + (-235500 : ℝ)*t^0*b^7) + ((-529395 : ℝ)*t^0*b^6 + (-324510 : ℝ)*t^0*b^5)) + (((-374610 : ℝ)*t^0*b^4 + (105810 : ℝ)*t^0*b^3) + ((399060 : ℝ)*t^0*b^2 + (100320 : ℝ)*t^0*b^1))))))
private theorem pair01 (t b : ℝ) : vDt t b*vNb1 t b-vDb t b*vNt1 t b = p01 t b := by
  unfold vDt vNb1 vDb vNt1 p01
  ring
private def z01 (t b : ℝ) : ℝ :=
    ((((((((-81561600 : ℝ)*t^15*b^11 + (-165369600 : ℝ)*t^15*b^10) + ((135302400 : ℝ)*t^15*b^9 + (-14169600 : ℝ)*t^15*b^8)) + (((367027200 : ℝ)*t^14*b^11 + (1275350400 : ℝ)*t^14*b^10) + ((559915200 : ℝ)*t^14*b^9 + ((-944956800 : ℝ)*t^14*b^8 + (106790400 : ℝ)*t^14*b^7)))) + ((((-7646400 : ℝ)*t^13*b^11 + (-3683548800 : ℝ)*t^13*b^10) + ((-7044386400 : ℝ)*t^13*b^9 + ((361022400 : ℝ)*t^13*b^8 + (2807769600 : ℝ)*t^13*b^7))) + (((-350784000 : ℝ)*t^13*b^6 + (-1925344800 : ℝ)*t^12*b^11) + ((1754735400 : ℝ)*t^12*b^10 + ((21260807640 : ℝ)*t^12*b^9 + (21353368320 : ℝ)*t^12*b^8))))) + (((((-4532634720 : ℝ)*t^12*b^7 + (-4551500160 : ℝ)*t^12*b^6) + ((655603200 : ℝ)*t^12*b^5 + (1166644800 : ℝ)*t^11*b^11)) + (((12347442900 : ℝ)*t^11*b^10 + (-12316428990 : ℝ)*t^11*b^9) + ((-67655502360 : ℝ)*t^11*b^8 + ((-40087582200 : ℝ)*t^11*b^7 + (9231382080 : ℝ)*t^11*b^6)))) + ((((4215317760 : ℝ)*t^11*b^5 + (-762048000 : ℝ)*t^11*b^4) + ((4895395200 : ℝ)*t^10*b^11 + ((-17268501420 : ℝ)*t^10*b^10 + (-57268051425 : ℝ)*t^10*b^9))) + (((25550932410 : ℝ)*t^10*b^8 + (119431503180 : ℝ)*t^10*b^7) + ((46870975800 : ℝ)*t^10*b^6 + ((-9207603360 : ℝ)*t^10*b^5 + (-1977148800 : ℝ)*t^10*b^4)))))) + ((((((563673600 : ℝ)*t^10*b^3 + (-3134376000 : ℝ)*t^9*b^11) + ((-10430280360 : ℝ)*t^9*b^10 + (94720196610 : ℝ)*t^9*b^9)) + (((176756149755 : ℝ)*t^9*b^8 + (-1032566580 : ℝ)*t^9*b^7) + ((-113302702260 : ℝ)*t^9*b^6 + ((-30687625440 : ℝ)*t^9*b^5 + (5116233600 : ℝ)*t^9*b^4)))) + ((((65664000 : ℝ)*t^9*b^3 + (-258854400 : ℝ)*t^9*b^2) + ((-8105025600 : ℝ)*t^8*b^11 + ((21572733060 : ℝ)*t^8*b^10 + (6355986435 : ℝ)*t^8*b^9))) + (((-241714196460 : ℝ)*t^8*b^8 + (-329916178350 : ℝ)*t^8*b^7) + ((-73782340200 : ℝ)*t^8*b^6 + ((41291884800 : ℝ)*t^8*b^5 + (5379544800 : ℝ)*t^8*b^4))))) + (((((-1780106400 : ℝ)*t^8*b^3 + (409968000 : ℝ)*t^8*b^2) + ((67392000 : ℝ)*t^8*b^1 + (4308048000 : ℝ)*t^7*b^11)) + (((5395455900 : ℝ)*t^7*b^10 + (-99224267535 : ℝ)*t^7*b^9) + ((-31041855855 : ℝ)*t^7*b^8 + ((327664408860 : ℝ)*t^7*b^7 + (374574029400 : ℝ)*t^7*b^6)))) + ((((128384743770 : ℝ)*t^7*b^5 + (22014460440 : ℝ)*t^7*b^4) + ((7359383880 : ℝ)*t^7*b^3 + ((609606720 : ℝ)*t^7*b^2 + (-188375040 : ℝ)*t^7*b^1))) + (((-7603200 : ℝ)*t^7*b^0 + (8515929600 : ℝ)*t^6*b^11) + ((-4609209240 : ℝ)*t^6*b^10 + ((56654896680 : ℝ)*t^6*b^9 + (244586411280 : ℝ)*t^6*b^8))))))) + (((((((113599636875 : ℝ)*t^6*b^7 + (-240219784260 : ℝ)*t^6*b^6) + ((-259976133585 : ℝ)*t^6*b^5 + (-106777031310 : ℝ)*t^6*b^4)) + (((-30847618980 : ℝ)*t^6*b^3 + (-5905859400 : ℝ)*t^6*b^2) + ((-239381280 : ℝ)*t^6*b^1 + ((27959040 : ℝ)*t^6*b^0 + (-3807547200 : ℝ)*t^5*b^11)))) + ((((-11713197780 : ℝ)*t^5*b^10 + (6372316350 : ℝ)*t^5*b^9) + ((-132584055480 : ℝ)*t^5*b^8 + ((-325381199940 : ℝ)*t^5*b^7 + (-169686944145 : ℝ)*t^5*b^6))) + (((81032819670 : ℝ)*t^5*b^5 + (106772528655 : ℝ)*t^5*b^4) + ((48844654560 : ℝ)*t^5*b^3 + ((13554404460 : ℝ)*t^5*b^2 + (1756940400 : ℝ)*t^5*b^1))))) + (((((46935360 : ℝ)*t^5*b^0 + (-4843900800 : ℝ)*t^4*b^11) + ((-2253364020 : ℝ)*t^4*b^10 + (-22340987505 : ℝ)*t^4*b^9)) + (((-35602723755 : ℝ)*t^4*b^8 + (117276692490 : ℝ)*t^4*b^7) + ((238679175870 : ℝ)*t^4*b^6 + ((127254486420 : ℝ)*t^4*b^5 + (1611175500 : ℝ)*t^4*b^4)))) + ((((-23439631320 : ℝ)*t^4*b^3 + (-11871961740 : ℝ)*t^4*b^2) + ((-2592587520 : ℝ)*t^4*b^1 + ((-188548560 : ℝ)*t^4*b^0 + (2087150400 : ℝ)*t^3*b^11))) + (((10581874920 : ℝ)*t^3*b^10 + (18866454660 : ℝ)*t^3*b^9) + ((58828303395 : ℝ)*t^3*b^8 + ((59769842220 : ℝ)*t^3*b^7 + (-40947386310 : ℝ)*t^3*b^6)))))) + ((((((-92615256405 : ℝ)*t^3*b^5 + (-49329590580 : ℝ)*t^3*b^4) + ((-8805079980 : ℝ)*t^3*b^3 + (2092664970 : ℝ)*t^3*b^2)) + (((1293531480 : ℝ)*t^3*b^1 + (161872200 : ℝ)*t^3*b^0) + ((1024315200 : ℝ)*t^2*b^11 + ((-1320113700 : ℝ)*t^2*b^10 + (-6977481615 : ℝ)*t^2*b^9)))) + ((((-19612708425 : ℝ)*t^2*b^8 + (-47471383800 : ℝ)*t^2*b^7) + ((-41766137955 : ℝ)*t^2*b^6 + ((-1117109070 : ℝ)*t^2*b^5 + (15773938110 : ℝ)*t^2*b^4))) + (((8829031770 : ℝ)*t^2*b^3 + (1890994680 : ℝ)*t^2*b^2) + ((-17476200 : ℝ)*t^2*b^1 + ((-40622400 : ℝ)*t^2*b^0 + (-544536000 : ℝ)*t^1*b^11))))) + (((((-2484181980 : ℝ)*t^1*b^10 + (-2557171575 : ℝ)*t^1*b^9) + ((-1649772405 : ℝ)*t^1*b^8 + ((4587647085 : ℝ)*t^1*b^7 + (13996899090 : ℝ)*t^1*b^6))) + (((11730199500 : ℝ)*t^1*b^5 + (3277706670 : ℝ)*t^1*b^4) + ((-399739320 : ℝ)*t^1*b^3 + ((-474121800 : ℝ)*t^1*b^2 + (-79747200 : ℝ)*t^1*b^1)))) + ((((50868000 : ℝ)*t^0*b^11 + (641398320 : ℝ)*t^0*b^10) + ((1583402670 : ℝ)*t^0*b^9 + ((1637520165 : ℝ)*t^0*b^8 + (1474677720 : ℝ)*t^0*b^7))) + (((326140110 : ℝ)*t^0*b^6 + (-916272450 : ℝ)*t^0*b^5) + ((-822470760 : ℝ)*t^0*b^4 + ((-295579800 : ℝ)*t^0*b^3 + (-39124800 : ℝ)*t^0*b^2))))))))
private theorem product01 (t b : ℝ) : vN0 t b*p01 t b = z01 t b := by
  unfold vN0 p01 z01
  ring
private def p02 (t b : ℝ) : ℝ :=
    (((((((-30720 : ℝ)*t^9*b^7 + (-55680 : ℝ)*t^9*b^6) + ((84480 : ℝ)*t^9*b^5 + (76800 : ℝ)*t^8*b^7)) + (((246240 : ℝ)*t^8*b^6 + (8640 : ℝ)*t^8*b^5) + ((-378240 : ℝ)*t^8*b^4 + (61440 : ℝ)*t^7*b^7))) + ((((-499680 : ℝ)*t^7*b^6 + (-960960 : ℝ)*t^7*b^5) + ((485760 : ℝ)*t^7*b^4 + (668160 : ℝ)*t^7*b^3)) + (((-232800 : ℝ)*t^6*b^7 + (120120 : ℝ)*t^6*b^6) + ((2146080 : ℝ)*t^6*b^5 + (1888440 : ℝ)*t^6*b^4)))) + (((((-985680 : ℝ)*t^6*b^3 + (-579840 : ℝ)*t^6*b^2) + ((-93120 : ℝ)*t^5*b^7 + (608325 : ℝ)*t^5*b^6)) + (((-969660 : ℝ)*t^5*b^5 + (-4324800 : ℝ)*t^5*b^4) + ((-1937040 : ℝ)*t^5*b^3 + (791280 : ℝ)*t^5*b^2))) + ((((245760 : ℝ)*t^5*b^1 + (293760 : ℝ)*t^4*b^7) + ((-366195 : ℝ)*t^4*b^6 + (-1452615 : ℝ)*t^4*b^5)) + (((1725450 : ℝ)*t^4*b^4 + (4197660 : ℝ)*t^4*b^3) + ((1026480 : ℝ)*t^4*b^2 + (-277680 : ℝ)*t^4*b^1))))) + ((((((-40320 : ℝ)*t^4*b^0 + (124800 : ℝ)*t^3*b^7) + ((-27570 : ℝ)*t^3*b^6 + (1616010 : ℝ)*t^3*b^5)) + (((2098515 : ℝ)*t^3*b^4 + (-1372440 : ℝ)*t^3*b^3) + ((-1955160 : ℝ)*t^3*b^2 + (-253200 : ℝ)*t^3*b^1))) + ((((33360 : ℝ)*t^3*b^0 + (-184320 : ℝ)*t^2*b^7) + ((-164985 : ℝ)*t^2*b^6 + (-463095 : ℝ)*t^2*b^5)) + (((-1866915 : ℝ)*t^2*b^4 + (-1347345 : ℝ)*t^2*b^3) + ((498690 : ℝ)*t^2*b^2 + (373500 : ℝ)*t^2*b^1)))) + (((((20760 : ℝ)*t^2*b^0 + (-72000 : ℝ)*t^1*b^7) + ((-48975 : ℝ)*t^1*b^6 + (-157110 : ℝ)*t^1*b^5)) + (((194625 : ℝ)*t^1*b^4 + (753480 : ℝ)*t^1*b^3) + ((316560 : ℝ)*t^1*b^2 + (-62880 : ℝ)*t^1*b^1))) + ((((-14400 : ℝ)*t^1*b^0 + (41760 : ℝ)*t^0*b^7) + ((88230 : ℝ)*t^0*b^6 + (53190 : ℝ)*t^0*b^5)) + (((86250 : ℝ)*t^0*b^4 + (-6480 : ℝ)*t^0*b^3) + ((-77940 : ℝ)*t^0*b^2 + (-13800 : ℝ)*t^0*b^1))))))
private theorem pair02 (t b : ℝ) : vNt0 t b*vDb t b-vNb0 t b*vDt t b = p02 t b := by
  unfold vNt0 vDb vNb0 vDt p02
  ring
private def z02 (t b : ℝ) : ℝ :=
    ((((((((81561600 : ℝ)*t^15*b^11 + (156124800 : ℝ)*t^15*b^10) + ((-209260800 : ℝ)*t^15*b^9 + (-22809600 : ℝ)*t^15*b^8)) + (((-367027200 : ℝ)*t^14*b^11 + (-1231437600 : ℝ)*t^14*b^10) + ((-139276800 : ℝ)*t^14*b^9 + ((1675296000 : ℝ)*t^14*b^8 + (170553600 : ℝ)*t^14*b^7)))) + ((((-156211200 : ℝ)*t^13*b^11 + (2716034400 : ℝ)*t^13*b^10) + ((6557436000 : ℝ)*t^13*b^9 + ((-2751667200 : ℝ)*t^13*b^8 + (-5770713600 : ℝ)*t^13*b^7))) + (((-555206400 : ℝ)*t^13*b^6 + (2495844000 : ℝ)*t^12*b^11) + ((2411399160 : ℝ)*t^12*b^10 + ((-16427476080 : ℝ)*t^12*b^9 + (-21224454120 : ℝ)*t^12*b^8))))) + (((((10279608480 : ℝ)*t^12*b^7 + (11140437600 : ℝ)*t^12*b^6) + ((1026950400 : ℝ)*t^12*b^5 + (-1260806400 : ℝ)*t^11*b^11)) + (((-16980033195 : ℝ)*t^11*b^10 + (-7414252650 : ℝ)*t^11*b^9) + ((61605753480 : ℝ)*t^11*b^8 + ((48032882280 : ℝ)*t^11*b^7 + (-15769895760 : ℝ)*t^11*b^6)))) + ((((-13107355200 : ℝ)*t^11*b^5 + (-1179360000 : ℝ)*t^11*b^4) + ((-6486955200 : ℝ)*t^10*b^11 + ((11744747955 : ℝ)*t^10*b^10 + (75475744560 : ℝ)*t^10*b^9))) + (((15680831850 : ℝ)*t^10*b^8 + (-132426408960 : ℝ)*t^10*b^7) + ((-76115481120 : ℝ)*t^10*b^6 + ((10969119360 : ℝ)*t^10*b^5 + (9501328800 : ℝ)*t^10*b^4)))))) + ((((((860025600 : ℝ)*t^10*b^3 + (4429209600 : ℝ)*t^9*b^11) + ((24893328150 : ℝ)*t^9*b^10 + (-70349388390 : ℝ)*t^9*b^9)) + (((-221402456505 : ℝ)*t^9*b^8 + (-40978533420 : ℝ)*t^9*b^7) + ((168899123520 : ℝ)*t^9*b^6 + ((81899662320 : ℝ)*t^9*b^5 + (-704084400 : ℝ)*t^9*b^4)))) + ((((-4004208000 : ℝ)*t^9*b^3 + (-388281600 : ℝ)*t^9*b^2) + ((9488347200 : ℝ)*t^8*b^11 + ((-25881419115 : ℝ)*t^8*b^10 + (-55701000900 : ℝ)*t^8*b^9))) + (((206219117655 : ℝ)*t^8*b^8 + (404240433660 : ℝ)*t^8*b^7) + ((85425322500 : ℝ)*t^8*b^6 + ((-129354616800 : ℝ)*t^8*b^5 + (-57831384600 : ℝ)*t^8*b^4))))) + (((((-4205599200 : ℝ)*t^8*b^3 + (781725600 : ℝ)*t^8*b^2) + ((99014400 : ℝ)*t^8*b^1 + (-6051888000 : ℝ)*t^7*b^11)) + (((-16077195495 : ℝ)*t^7*b^10 + (109414199565 : ℝ)*t^7*b^9) + ((114364615770 : ℝ)*t^7*b^8 + ((-322187369940 : ℝ)*t^7*b^7 + (-460570237065 : ℝ)*t^7*b^6)))) + ((((-107816636250 : ℝ)*t^7*b^5 + (56644069320 : ℝ)*t^7*b^4) + ((25547312520 : ℝ)*t^7*b^3 + ((2861799120 : ℝ)*t^7*b^2 + (13982400 : ℝ)*t^7*b^1))) + (((-10886400 : ℝ)*t^7*b^0 + (-8723980800 : ℝ)*t^6*b^11) + ((13636616310 : ℝ)*t^6*b^10 + ((-26606795130 : ℝ)*t^6*b^9 + (-265970573280 : ℝ)*t^6*b^8))))))) + (((((((-186210028620 : ℝ)*t^6*b^7 + (284689706265 : ℝ)*t^6*b^6) + ((328409250300 : ℝ)*t^6*b^5 + (79970256090 : ℝ)*t^6*b^4)) + (((-11379890880 : ℝ)*t^6*b^3 + (-6462740880 : ℝ)*t^6*b^2) + ((-768363840 : ℝ)*t^6*b^1 + ((-21232800 : ℝ)*t^6*b^0 + (4594291200 : ℝ)*t^5*b^11)))) + ((((12590509995 : ℝ)*t^5*b^10 + (-27172491570 : ℝ)*t^5*b^9) + ((94286002095 : ℝ)*t^5*b^8 + ((355292520210 : ℝ)*t^5*b^7 + (195974222670 : ℝ)*t^5*b^6))) + (((-140679481770 : ℝ)*t^5*b^5 + (-142860744675 : ℝ)*t^5*b^4) + ((-34061978880 : ℝ)*t^5*b^3 + ((-317850480 : ℝ)*t^5*b^2 + (769389120 : ℝ)*t^5*b^1))))) + (((((72235440 : ℝ)*t^5*b^0 + (4628088000 : ℝ)*t^4*b^11) + ((-1436704875 : ℝ)*t^4*b^10 + (19946474820 : ℝ)*t^4*b^9)) + (((60085291815 : ℝ)*t^4*b^8 + (-96948010170 : ℝ)*t^4*b^7) + ((-264111300045 : ℝ)*t^4*b^6 + ((-122658180660 : ℝ)*t^4*b^5 + (34417901925 : ℝ)*t^4*b^4)))) + ((((35151933240 : ℝ)*t^4*b^3 + (7646901120 : ℝ)*t^4*b^2) + ((440514000 : ℝ)*t^4*b^1 + ((-22745520 : ℝ)*t^4*b^0 + (-2148076800 : ℝ)*t^3*b^11))) + (((-9486454230 : ℝ)*t^3*b^10 + (-12542208030 : ℝ)*t^3*b^9) + ((-56316865275 : ℝ)*t^3*b^8 + ((-74102891940 : ℝ)*t^3*b^7 + (41534873190 : ℝ)*t^3*b^6)))))) + ((((((105721111125 : ℝ)*t^3*b^5 + (42484659570 : ℝ)*t^3*b^4) + ((-2229061860 : ℝ)*t^3*b^3 + (-4098260160 : ℝ)*t^3*b^2)) + (((-721959120 : ℝ)*t^3*b^1 + (-32224320 : ℝ)*t^3*b^0) + ((-966600000 : ℝ)*t^2*b^11 + ((1607055795 : ℝ)*t^2*b^10 + (5587145370 : ℝ)*t^2*b^9)))) + ((((14447868930 : ℝ)*t^2*b^8 + (46412680950 : ℝ)*t^2*b^7) + ((44762836455 : ℝ)*t^2*b^6 + ((-3936838410 : ℝ)*t^2*b^5 + (-19836361980 : ℝ)*t^2*b^4))) + (((-6999601500 : ℝ)*t^2*b^3 + (-395042400 : ℝ)*t^2*b^2) + ((138525840 : ℝ)*t^2*b^1 + ((14860800 : ℝ)*t^2*b^0 + (525744000 : ℝ)*t^1*b^11))))) + (((((2359002375 : ℝ)*t^1*b^10 + (2312394705 : ℝ)*t^1*b^9) + ((2428376895 : ℝ)*t^1*b^8 + ((-2739756645 : ℝ)*t^1*b^7 + (-14024620530 : ℝ)*t^1*b^6))) + (((-11476387440 : ℝ)*t^1*b^5 + (-1568430720 : ℝ)*t^1*b^4) + ((1069210080 : ℝ)*t^1*b^3 + ((353737440 : ℝ)*t^1*b^2 + (29102400 : ℝ)*t^1*b^1)))) + ((((-46980000 : ℝ)*t^0*b^11 + (-654374430 : ℝ)*t^0*b^10) + ((-1544126220 : ℝ)*t^0*b^9 + ((-1505201580 : ℝ)*t^0*b^8 + (-1626975630 : ℝ)*t^0*b^7))) + (((-524323440 : ℝ)*t^0*b^6 + (1010899260 : ℝ)*t^0*b^5) + ((771407280 : ℝ)*t^0*b^4 + ((183354480 : ℝ)*t^0*b^3 + (14241600 : ℝ)*t^0*b^2))))))))
private theorem product02 (t b : ℝ) : vN1 t b*p02 t b = z02 t b := by
  unfold vN1 p02 z02
  ring
private theorem quotient_e0 (t b : ℝ) :
    45 * (sourceE0 b).eval (t*b) = b^7*sourceQuotient 1 t b := by
  unfold sourceQuotient
  simp only [partial_Nt0,partial_Nb1,partial_Nb0,partial_Nt1,partial_Dt,partial_Db]
  simp only [expanded_D,expanded_N0,expanded_N1]
  rw [pair00,pair01,pair02,product00,product01,product02]
  simp only [sourceE0,z00,z01,z02,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_zero,eval_one,eval_ofNat]
  ring
/-- Exact normalization of the literal ordered source pair, with no division. -/
theorem source_e0_normalization (t b : ℝ) :
    45 * sourceD t b * (sourceE0 b).eval (t*b) =
      b^7*(sourceBt 0 t b*sourceBb 1 t b-sourceBb 0 t b*sourceBt 1 t b) := by
  rw [source_factor]
  calc
    _ = sourceD t b * (45 * (sourceE0 b).eval (t*b)) := by ring
    _ = sourceD t b * (b^7*sourceQuotient 1 t b) := by rw [quotient_e0]
    _ = _ := by ring
private def p10 (t b : ℝ) : ℝ :=
    (((((((-17750016 : ℝ)*t^11*b^6 + (65083392 : ℝ)*t^10*b^6) + ((97625088 : ℝ)*t^10*b^5 + (-78206976 : ℝ)*t^9*b^7)) + (((50347008 : ℝ)*t^9*b^6 + (-295409088 : ℝ)*t^9*b^5) + ((-221875200 : ℝ)*t^9*b^4 + ((191232000 : ℝ)*t^8*b^7 + (7424064 : ℝ)*t^8*b^6)))) + ((((-288226080 : ℝ)*t^8*b^5 + (532038816 : ℝ)*t^8*b^4) + ((266250240 : ℝ)*t^8*b^3 + (14118912 : ℝ)*t^7*b^7)) + (((-597034080 : ℝ)*t^7*b^6 + (841405248 : ℝ)*t^7*b^5) + ((673617312 : ℝ)*t^7*b^4 + ((-475732224 : ℝ)*t^7*b^3 + (-177500160 : ℝ)*t^7*b^2))))) + (((((-308206080 : ℝ)*t^6*b^7 + (381745728 : ℝ)*t^6*b^6) + ((473699853 : ℝ)*t^6*b^5 + (-1998719658 : ℝ)*t^6*b^4)) + (((-821569608 : ℝ)*t^6*b^3 + (212803776 : ℝ)*t^6*b^2) + ((62125056 : ℝ)*t^6*b^1 + ((115329024 : ℝ)*t^5*b^7 + (569474208 : ℝ)*t^5*b^6)))) + ((((-1283535774 : ℝ)*t^5*b^5 + (325078974 : ℝ)*t^5*b^4) + ((2053042560 : ℝ)*t^5*b^3 + (550060632 : ℝ)*t^5*b^2)) + (((-40021056 : ℝ)*t^5*b^1 + (-8875008 : ℝ)*t^5*b^0) + ((88685568 : ℝ)*t^4*b^7 + ((-504225936 : ℝ)*t^4*b^6 + (98489322 : ℝ)*t^4*b^5)))))) + ((((((1551833145 : ℝ)*t^4*b^4 + (-712816974 : ℝ)*t^4*b^3) + ((-1066873860 : ℝ)*t^4*b^2 + (-190833336 : ℝ)*t^4*b^1)) + (((1236384 : ℝ)*t^4*b^0 + (-25251840 : ℝ)*t^3*b^7) + ((-20647728 : ℝ)*t^3*b^6 + ((571966452 : ℝ)*t^3*b^5 + (-819818361 : ℝ)*t^3*b^4)))) + ((((-851591916 : ℝ)*t^3*b^3 + (399513114 : ℝ)*t^3*b^2) + ((265376880 : ℝ)*t^3*b^1 + (26604072 : ℝ)*t^3*b^0)) + (((10174464 : ℝ)*t^2*b^7 + (110342016 : ℝ)*t^2*b^6) + ((-140772924 : ℝ)*t^2*b^5 + ((-140154318 : ℝ)*t^2*b^4 + (602208360 : ℝ)*t^2*b^3))))) + (((((207434817 : ℝ)*t^2*b^2 + (-84007467 : ℝ)*t^2*b^1) + ((-23448258 : ℝ)*t^2*b^0 + (-25574400 : ℝ)*t^1*b^7)) + (((-30499056 : ℝ)*t^1*b^6 + (-54722286 : ℝ)*t^1*b^5) + ((133310979 : ℝ)*t^1*b^4 + ((-40956912 : ℝ)*t^1*b^3 + (-141643017 : ℝ)*t^1*b^2)))) + ((((-17981856 : ℝ)*t^1*b^1 + (4334580 : ℝ)*t^1*b^0) + ((9358848 : ℝ)*t^0*b^7 + (-5223024 : ℝ)*t^0*b^6)) + (((1600803 : ℝ)*t^0*b^5 + (-16895025 : ℝ)*t^0*b^4) + ((-39445713 : ℝ)*t^0*b^3 + ((3715632 : ℝ)*t^0*b^2 + (4207500 : ℝ)*t^0*b^1)))))))
private theorem pair10 (t b : ℝ) : vNt0 t b*vNb2 t b-vNb0 t b*vNt2 t b = p10 t b := by
  unfold vNt0 vNb2 vNb0 vNt2 p10
  ring
private def z10 (t b : ℝ) : ℝ :=
    ((((((((-88750080 : ℝ)*t^15*b^10 + (-710000640 : ℝ)*t^15*b^9) + ((-355000320 : ℝ)*t^15*b^8 + (414167040 : ℝ)*t^14*b^10)) + (((3978961920 : ℝ)*t^14*b^9 + (6981672960 : ℝ)*t^14*b^8) + ((2662502400 : ℝ)*t^14*b^7 + ((-391034880 : ℝ)*t^13*b^11 + (-3024460800 : ℝ)*t^13*b^10)))) + ((((-4148349120 : ℝ)*t^13*b^9 + (-24462144000 : ℝ)*t^13*b^8) + ((-28569035520 : ℝ)*t^13*b^7 + (-8697507840 : ℝ)*t^13*b^6)) + (((1347194880 : ℝ)*t^12*b^11 + (10605430080 : ℝ)*t^12*b^10) + ((5674194720 : ℝ)*t^12*b^9 + ((5534082720 : ℝ)*t^12*b^8 + (67553873280 : ℝ)*t^12*b^7))))) + (((((64761344640 : ℝ)*t^12*b^6 + (16152514560 : ℝ)*t^12*b^5) + ((-103495680 : ℝ)*t^11*b^11 + (-9548693280 : ℝ)*t^11*b^10)) + (((-38896112160 : ℝ)*t^11*b^9 + (43608360960 : ℝ)*t^11*b^8) + ((34345503360 : ℝ)*t^11*b^7 + ((-102709889280 : ℝ)*t^11*b^6 + (-90131927040 : ℝ)*t^11*b^5)))) + ((((-18637516800 : ℝ)*t^11*b^4 + (-3914979840 : ℝ)*t^10*b^11) + ((-16676707680 : ℝ)*t^10*b^10 + ((48934772865 : ℝ)*t^10*b^9 + (42119896950 : ℝ)*t^10*b^8))) + (((-222415465140 : ℝ)*t^10*b^7 + (-146516253480 : ℝ)*t^10*b^6) + ((88564209120 : ℝ)*t^10*b^5 + ((79898682240 : ℝ)*t^10*b^4 + (13667512320 : ℝ)*t^10*b^3)))))) + ((((((2541611520 : ℝ)*t^9*b^11 + (32464101600 : ℝ)*t^9*b^10) + ((47602346985 : ℝ)*t^9*b^9 + (-164787278130 : ℝ)*t^9*b^8)) + (((42801076800 : ℝ)*t^9*b^7 + (477124673760 : ℝ)*t^9*b^6) + ((262253873520 : ℝ)*t^9*b^5 + ((-36919876320 : ℝ)*t^9*b^4 + (-44919740160 : ℝ)*t^9*b^3)))) + ((((-6212505600 : ℝ)*t^9*b^2 + (3975598080 : ℝ)*t^8*b^11) + ((-3142256400 : ℝ)*t^8*b^10 + ((-111994146810 : ℝ)*t^8*b^9 + (14983965360 : ℝ)*t^8*b^8))) + (((346283859105 : ℝ)*t^8*b^7 + (-170907714450 : ℝ)*t^8*b^6) + ((-593315166420 : ℝ)*t^8*b^5 + ((-267939448920 : ℝ)*t^8*b^4 + (-1853092800 : ℝ)*t^8*b^3))))) + (((((15289153920 : ℝ)*t^8*b^2 + (1597501440 : ℝ)*t^8*b^1) + ((-3193413120 : ℝ)*t^7*b^11 + (-23080343040 : ℝ)*t^7*b^10)) + (((25996285215 : ℝ)*t^7*b^9 + (192356281620 : ℝ)*t^7*b^8) + ((-236033211870 : ℝ)*t^7*b^7 + ((-464181355530 : ℝ)*t^7*b^6 + (216805444920 : ℝ)*t^7*b^5)))) + ((((460946317320 : ℝ)*t^7*b^4 + (166304161440 : ℝ)*t^7*b^3) + ((9144601920 : ℝ)*t^7*b^2 + ((-2802378240 : ℝ)*t^7*b^1 + (-177500160 : ℝ)*t^7*b^0))) + (((-1674109440 : ℝ)*t^6*b^11 + (12478754160 : ℝ)*t^6*b^10) + ((55861780455 : ℝ)*t^6*b^9 + ((-112550159385 : ℝ)*t^6*b^8 + (-164451050415 : ℝ)*t^6*b^7))))))) + (((((((429038090910 : ℝ)*t^6*b^6 + (402562301175 : ℝ)*t^6*b^5) + ((-152203838670 : ℝ)*t^6*b^4 + (-224290814220 : ℝ)*t^6*b^3)) + (((-61577559000 : ℝ)*t^6*b^2 + (-3715247520 : ℝ)*t^6*b^1) + ((202227840 : ℝ)*t^6*b^0 + ((1093847040 : ℝ)*t^5*b^11 + (1841195520 : ℝ)*t^5*b^10)))) + ((((-37478712150 : ℝ)*t^5*b^9 + (-51550625430 : ℝ)*t^5*b^8) + ((199439836335 : ℝ)*t^5*b^7 + ((49069053315 : ℝ)*t^5*b^6 + (-388970536815 : ℝ)*t^5*b^5))) + (((-222639101910 : ℝ)*t^5*b^4 + (63511354800 : ℝ)*t^5*b^3) + ((64996483680 : ℝ)*t^5*b^2 + ((12330869040 : ℝ)*t^5*b^1 + (507353760 : ℝ)*t^5*b^0))))) + (((((390090240 : ℝ)*t^4*b^11 + (-3061995840 : ℝ)*t^4*b^10) + ((977232195 : ℝ)*t^4*b^9 + (59684838120 : ℝ)*t^4*b^8)) + (((-9833846265 : ℝ)*t^4*b^7 + (-185868224955 : ℝ)*t^4*b^6) + ((21453247755 : ℝ)*t^4*b^5 + ((197915520870 : ℝ)*t^4*b^4 + (74107167615 : ℝ)*t^4*b^3)))) + ((((-15196456710 : ℝ)*t^4*b^2 + (-9859780620 : ℝ)*t^4*b^1) + ((-1001046600 : ℝ)*t^4*b^0 + ((133562880 : ℝ)*t^3*b^11 + (1511972640 : ℝ)*t^3*b^10))) + (((6051151845 : ℝ)*t^3*b^9 + (-7980915600 : ℝ)*t^3*b^8) + ((-45328044060 : ℝ)*t^3*b^7 + ((50372663310 : ℝ)*t^3*b^6 + (99135384930 : ℝ)*t^3*b^5)))))) + ((((((-18728471115 : ℝ)*t^3*b^4 + (-54136706760 : ℝ)*t^3*b^3) + ((-12861581670 : ℝ)*t^3*b^2 + (1838644920 : ℝ)*t^3*b^1)) + (((555656760 : ℝ)*t^3*b^0 + (-170588160 : ℝ)*t^2*b^11) + ((-643346640 : ℝ)*t^2*b^10 + ((-2291535360 : ℝ)*t^2*b^9 + (-5918661450 : ℝ)*t^2*b^8)))) + ((((10873624590 : ℝ)*t^2*b^7 + (14041732680 : ℝ)*t^2*b^6) + ((-34233755580 : ℝ)*t^2*b^5 + ((-30062690640 : ℝ)*t^2*b^4 + (3652436610 : ℝ)*t^2*b^3))) + (((6531345720 : ℝ)*t^2*b^2 + (782714880 : ℝ)*t^2*b^1) + ((-86691600 : ℝ)*t^2*b^0 + ((-81077760 : ℝ)*t^1*b^11 + (102155040 : ℝ)*t^1*b^10))))) + (((((881443305 : ℝ)*t^1*b^9 + (1924097940 : ℝ)*t^1*b^8) + ((1907546535 : ℝ)*t^1*b^7 + (-6561416115 : ℝ)*t^1*b^6)) + (((-1693882620 : ℝ)*t^1*b^5 + (8265497670 : ℝ)*t^1*b^4) + ((4355804880 : ℝ)*t^1*b^3 + ((-14283720 : ℝ)*t^1*b^2 + (-170841600 : ℝ)*t^1*b^1)))) + ((((46794240 : ℝ)*t^0*b^11 + (-26115120 : ℝ)*t^0*b^10) + ((-366349905 : ℝ)*t^0*b^9 + ((-62731125 : ℝ)*t^0*b^8 + (-156800205 : ℝ)*t^0*b^7))) + (((662363100 : ℝ)*t^0*b^6 + (1936766520 : ℝ)*t^0*b^5) + ((640288980 : ℝ)*t^0*b^4 + ((-242612640 : ℝ)*t^0*b^3 + (-84150000 : ℝ)*t^0*b^2))))))))
private theorem product10 (t b : ℝ) : vD t b*p10 t b = z10 t b := by
  unfold vD p10 z10
  ring
private def p11 (t b : ℝ) : ℝ :=
    (((((((495360 : ℝ)*t^9*b^7 + (1128960 : ℝ)*t^9*b^6) + ((-437760 : ℝ)*t^9*b^5 + (-1238400 : ℝ)*t^8*b^7)) + (((-4567680 : ℝ)*t^8*b^6 + (-3490560 : ℝ)*t^8*b^5) + ((2016000 : ℝ)*t^8*b^4 + (-990720 : ℝ)*t^7*b^7))) + ((((9715980 : ℝ)*t^7*b^6 + (19895280 : ℝ)*t^7*b^5) + ((4210320 : ℝ)*t^7*b^4 + (-3686400 : ℝ)*t^7*b^3)) + (((3763200 : ℝ)*t^6*b^7 + (-3698205 : ℝ)*t^6*b^6) + ((-40610430 : ℝ)*t^6*b^5 + (-43656900 : ℝ)*t^6*b^4)))) + (((((-3417720 : ℝ)*t^6*b^3 + (3340800 : ℝ)*t^6*b^2) + ((1983360 : ℝ)*t^5*b^7 + (-11310735 : ℝ)*t^5*b^6)) + (((19540170 : ℝ)*t^5*b^5 + (78831690 : ℝ)*t^5*b^4) + ((50818680 : ℝ)*t^5*b^3 + (2962440 : ℝ)*t^5*b^2))) + ((((-1497600 : ℝ)*t^5*b^1 + (-5186880 : ℝ)*t^4*b^7) + ((8116575 : ℝ)*t^4*b^6 + (28695285 : ℝ)*t^4*b^5)) + (((-28852725 : ℝ)*t^4*b^4 + (-75448680 : ℝ)*t^4*b^3) + ((-31452600 : ℝ)*t^4*b^2 + (-1833960 : ℝ)*t^4*b^1))))) + ((((((264960 : ℝ)*t^4*b^0 + (-2880000 : ℝ)*t^3*b^7) + ((-103740 : ℝ)*t^3*b^6 + (-33448320 : ℝ)*t^3*b^5)) + (((-41733315 : ℝ)*t^3*b^4 + (18953220 : ℝ)*t^3*b^3) + ((35626350 : ℝ)*t^3*b^2 + (9538920 : ℝ)*t^3*b^1))) + ((((440520 : ℝ)*t^3*b^0 + (3605760 : ℝ)*t^2*b^7) + ((3788985 : ℝ)*t^2*b^6 + (10301175 : ℝ)*t^2*b^5)) + (((37513755 : ℝ)*t^2*b^4 + (27915375 : ℝ)*t^2*b^3) + ((-5296140 : ℝ)*t^2*b^2 + (-7244790 : ℝ)*t^2*b^1)))) + (((((-1071060 : ℝ)*t^2*b^0 + (1680000 : ℝ)*t^1*b^7) + ((880935 : ℝ)*t^1*b^6 + (2916450 : ℝ)*t^1*b^5)) + (((-4347765 : ℝ)*t^1*b^4 + (-14536920 : ℝ)*t^1*b^3) + ((-7168110 : ℝ)*t^1*b^2 + (386160 : ℝ)*t^1*b^1))) + ((((368280 : ℝ)*t^1*b^0 + (-847680 : ℝ)*t^0*b^7) + ((-1812675 : ℝ)*t^0*b^6 + (-1075680 : ℝ)*t^0*b^5)) + (((-1717140 : ℝ)*t^0*b^4 + (-63690 : ℝ)*t^0*b^3) + ((1304580 : ℝ)*t^0*b^2 + (355680 : ℝ)*t^0*b^1))))))
private theorem pair11 (t b : ℝ) : vDt t b*vNb2 t b-vDb t b*vNt2 t b = p11 t b := by
  unfold vDt vNb2 vDb vNt2 p11
  ring
private def z11 (t b : ℝ) : ℝ :=
    ((((((((-380436480 : ℝ)*t^15*b^11 + (-819486720 : ℝ)*t^15*b^10) + ((444579840 : ℝ)*t^15*b^9 + (-42024960 : ℝ)*t^15*b^8)) + (((1711964160 : ℝ)*t^14*b^11 + (6169374720 : ℝ)*t^14*b^10) + ((3811553280 : ℝ)*t^14*b^9 + ((-3133071360 : ℝ)*t^14*b^8 + (319610880 : ℝ)*t^14*b^7)))) + ((((-35665920 : ℝ)*t^13*b^11 + (-15845575680 : ℝ)*t^13*b^10) + ((-33371429760 : ℝ)*t^13*b^9 + ((-4726494720 : ℝ)*t^13*b^8 + (9453934080 : ℝ)*t^13*b^7))) + (((-1060577280 : ℝ)*t^13*b^6 + (-8983065600 : ℝ)*t^12*b^11) + ((1931834880 : ℝ)*t^12*b^10 + ((82285086240 : ℝ)*t^12*b^9 + (96249119040 : ℝ)*t^12*b^8))))) + (((((-5508190080 : ℝ)*t^12*b^7 + (-15740686080 : ℝ)*t^12*b^6) + ((2005032960 : ℝ)*t^12*b^5 + (5885798400 : ℝ)*t^11*b^11)) + (((59539710240 : ℝ)*t^11*b^10 + (-18188400960 : ℝ)*t^11*b^9) + ((-245606873760 : ℝ)*t^11*b^8 + ((-169513591680 : ℝ)*t^11*b^7 + (22635550080 : ℝ)*t^11*b^6)))) + ((((15346437120 : ℝ)*t^11*b^5 + (-2361139200 : ℝ)*t^11*b^4) + ((21665018880 : ℝ)*t^10*b^11 + ((-64051634520 : ℝ)*t^10*b^10 + (-251677097820 : ℝ)*t^10*b^9))) + (((24482368440 : ℝ)*t^10*b^8 + (415850659920 : ℝ)*t^10*b^7) + ((184581542880 : ℝ)*t^10*b^6 + ((-28891923840 : ℝ)*t^10*b^5 + (-8211651840 : ℝ)*t^10*b^4)))))) + ((((((1772789760 : ℝ)*t^10*b^3 + (-16126479360 : ℝ)*t^9*b^11) + ((-65688431400 : ℝ)*t^9*b^10 + (325592263215 : ℝ)*t^9*b^9)) + (((710574378840 : ℝ)*t^9*b^8 + (95219221680 : ℝ)*t^9*b^7) + ((-376172988480 : ℝ)*t^9*b^6 + ((-109716502320 : ℝ)*t^9*b^5 + (20404149120 : ℝ)*t^9*b^4)))) + ((((1415554560 : ℝ)*t^9*b^3 + (-828334080 : ℝ)*t^9*b^2) + ((-32740508160 : ℝ)*t^8*b^11 + ((95870767680 : ℝ)*t^8*b^10 + (103686875460 : ℝ)*t^8*b^9))) + (((-816063952950 : ℝ)*t^8*b^8 + (-1257579691110 : ℝ)*t^8*b^7) + ((-355476656700 : ℝ)*t^8*b^6 + ((114371505720 : ℝ)*t^8*b^5 + (10106948880 : ℝ)*t^8*b^4))))) + (((((-9770071680 : ℝ)*t^8*b^3 + (857675520 : ℝ)*t^8*b^2) + ((220078080 : ℝ)*t^8*b^1 + (21287255040 : ℝ)*t^7*b^11)) + (((42240254040 : ℝ)*t^7*b^10 + (-384278130405 : ℝ)*t^7*b^9) + ((-238866940620 : ℝ)*t^7*b^8 + ((1095438186270 : ℝ)*t^7*b^7 + (1382634167310 : ℝ)*t^7*b^6)))) + ((((513277295400 : ℝ)*t^7*b^5 + (101376734040 : ℝ)*t^7*b^4) + ((33778565280 : ℝ)*t^7*b^3 + ((3946135680 : ℝ)*t^7*b^2 + (-517662720 : ℝ)*t^7*b^1))) + (((-25436160 : ℝ)*t^7*b^0 + (31781445120 : ℝ)*t^6*b^11) + ((-39953344680 : ℝ)*t^6*b^10 + ((145351964970 : ℝ)*t^6*b^9 + (897794239545 : ℝ)*t^6*b^8))))))) + (((((((530229635595 : ℝ)*t^6*b^7 + (-786683591640 : ℝ)*t^6*b^6) + ((-937293085260 : ℝ)*t^6*b^5 + (-401341919040 : ℝ)*t^6*b^4)) + (((-119819466720 : ℝ)*t^6*b^3 + (-24051801600 : ℝ)*t^6*b^2) + ((-1292158080 : ℝ)*t^6*b^1 + ((84890880 : ℝ)*t^6*b^0 + (-16904494080 : ℝ)*t^5*b^11)))) + ((((-48429325440 : ℝ)*t^5*b^10 + (64064768130 : ℝ)*t^5*b^9) + ((-396615191760 : ℝ)*t^5*b^8 + ((-1169651915235 : ℝ)*t^5*b^7 + (-683320732515 : ℝ)*t^5*b^6))) + (((244727491275 : ℝ)*t^5*b^5 + (375771022920 : ℝ)*t^5*b^4) + ((178228361520 : ℝ)*t^5*b^3 + ((50836145040 : ℝ)*t^5*b^2 + (6869477520 : ℝ)*t^5*b^1))))) + (((((210936960 : ℝ)*t^5*b^0 + (-17224335360 : ℝ)*t^4*b^11) + ((3391476120 : ℝ)*t^4*b^10 + (-67604442570 : ℝ)*t^4*b^9)) + (((-169793415540 : ℝ)*t^4*b^8 + (354605477220 : ℝ)*t^4*b^7) + ((846658519425 : ℝ)*t^4*b^6 + ((483958304145 : ℝ)*t^4*b^5 + (23958924930 : ℝ)*t^4*b^4)))) + ((((-79376604210 : ℝ)*t^4*b^3 + (-42515049420 : ℝ)*t^4*b^2) + ((-9581678280 : ℝ)*t^4*b^1 + ((-721266480 : ℝ)*t^4*b^0 + (8166159360 : ℝ)*t^3*b^11))) + (((37001308680 : ℝ)*t^3*b^10 + (50829431445 : ℝ)*t^3*b^9) + ((198244364670 : ℝ)*t^3*b^8 + ((240682273200 : ℝ)*t^3*b^7 + (-111529284390 : ℝ)*t^3*b^6)))))) + ((((((-322525647360 : ℝ)*t^3*b^5 + (-181749102345 : ℝ)*t^3*b^4) + ((-35663112720 : ℝ)*t^3*b^3 + (6366742290 : ℝ)*t^3*b^2)) + (((4562239320 : ℝ)*t^3*b^1 + (594487800 : ℝ)*t^3*b^0) + ((3525742080 : ℝ)*t^2*b^11 + ((-6472455840 : ℝ)*t^2*b^10 + (-23164884090 : ℝ)*t^2*b^9)))) + ((((-57192408630 : ℝ)*t^2*b^8 + (-162474484995 : ℝ)*t^2*b^7) + ((-159109526250 : ℝ)*t^2*b^6 + ((-15606896580 : ℝ)*t^2*b^5 + (52304159970 : ℝ)*t^2*b^4))) + (((31520172240 : ℝ)*t^2*b^3 + (7134455340 : ℝ)*t^2*b^2) + ((23522400 : ℝ)*t^2*b^1 + ((-143629200 : ℝ)*t^2*b^0 + (-1949736960 : ℝ)*t^1*b^11))))) + (((((-8561565720 : ℝ)*t^1*b^10 + (-7938570105 : ℝ)*t^1*b^9) + ((-7803702450 : ℝ)*t^1*b^8 + ((10303435665 : ℝ)*t^1*b^7 + (46569147255 : ℝ)*t^1*b^6))) + (((42947357220 : ℝ)*t^1*b^5 + (13476705840 : ℝ)*t^1*b^4) + ((-691992900 : ℝ)*t^1*b^3 + ((-1573279200 : ℝ)*t^1*b^2 + (-282344400 : ℝ)*t^1*b^1)))) + ((((183098880 : ℝ)*t^0*b^11 + (2288645640 : ℝ)*t^0*b^10) + ((5471627130 : ℝ)*t^0*b^9 + ((5637550905 : ℝ)*t^0*b^8 + (6064233210 : ℝ)*t^0*b^7))) + (((2675674440 : ℝ)*t^0*b^6 + (-2237944770 : ℝ)*t^0*b^5) + ((-2591061840 : ℝ)*t^0*b^4 + ((-1004959800 : ℝ)*t^0*b^3 + (-138715200 : ℝ)*t^0*b^2))))))))
private theorem product11 (t b : ℝ) : vN0 t b*p11 t b = z11 t b := by
  unfold vN0 p11 z11
  ring
private def p12 (t b : ℝ) : ℝ :=
    (((((((-30720 : ℝ)*t^9*b^7 + (-55680 : ℝ)*t^9*b^6) + ((84480 : ℝ)*t^9*b^5 + (76800 : ℝ)*t^8*b^7)) + (((246240 : ℝ)*t^8*b^6 + (8640 : ℝ)*t^8*b^5) + ((-378240 : ℝ)*t^8*b^4 + (61440 : ℝ)*t^7*b^7))) + ((((-499680 : ℝ)*t^7*b^6 + (-960960 : ℝ)*t^7*b^5) + ((485760 : ℝ)*t^7*b^4 + (668160 : ℝ)*t^7*b^3)) + (((-232800 : ℝ)*t^6*b^7 + (120120 : ℝ)*t^6*b^6) + ((2146080 : ℝ)*t^6*b^5 + (1888440 : ℝ)*t^6*b^4)))) + (((((-985680 : ℝ)*t^6*b^3 + (-579840 : ℝ)*t^6*b^2) + ((-93120 : ℝ)*t^5*b^7 + (608325 : ℝ)*t^5*b^6)) + (((-969660 : ℝ)*t^5*b^5 + (-4324800 : ℝ)*t^5*b^4) + ((-1937040 : ℝ)*t^5*b^3 + (791280 : ℝ)*t^5*b^2))) + ((((245760 : ℝ)*t^5*b^1 + (293760 : ℝ)*t^4*b^7) + ((-366195 : ℝ)*t^4*b^6 + (-1452615 : ℝ)*t^4*b^5)) + (((1725450 : ℝ)*t^4*b^4 + (4197660 : ℝ)*t^4*b^3) + ((1026480 : ℝ)*t^4*b^2 + (-277680 : ℝ)*t^4*b^1))))) + ((((((-40320 : ℝ)*t^4*b^0 + (124800 : ℝ)*t^3*b^7) + ((-27570 : ℝ)*t^3*b^6 + (1616010 : ℝ)*t^3*b^5)) + (((2098515 : ℝ)*t^3*b^4 + (-1372440 : ℝ)*t^3*b^3) + ((-1955160 : ℝ)*t^3*b^2 + (-253200 : ℝ)*t^3*b^1))) + ((((33360 : ℝ)*t^3*b^0 + (-184320 : ℝ)*t^2*b^7) + ((-164985 : ℝ)*t^2*b^6 + (-463095 : ℝ)*t^2*b^5)) + (((-1866915 : ℝ)*t^2*b^4 + (-1347345 : ℝ)*t^2*b^3) + ((498690 : ℝ)*t^2*b^2 + (373500 : ℝ)*t^2*b^1)))) + (((((20760 : ℝ)*t^2*b^0 + (-72000 : ℝ)*t^1*b^7) + ((-48975 : ℝ)*t^1*b^6 + (-157110 : ℝ)*t^1*b^5)) + (((194625 : ℝ)*t^1*b^4 + (753480 : ℝ)*t^1*b^3) + ((316560 : ℝ)*t^1*b^2 + (-62880 : ℝ)*t^1*b^1))) + ((((-14400 : ℝ)*t^1*b^0 + (41760 : ℝ)*t^0*b^7) + ((88230 : ℝ)*t^0*b^6 + (53190 : ℝ)*t^0*b^5)) + (((86250 : ℝ)*t^0*b^4 + (-6480 : ℝ)*t^0*b^3) + ((-77940 : ℝ)*t^0*b^2 + (-13800 : ℝ)*t^0*b^1))))))
private theorem pair12 (t b : ℝ) : vNt0 t b*vDb t b-vNb0 t b*vDt t b = p12 t b := by
  unfold vNt0 vDb vNb0 vDt p12
  ring
private def z12 (t b : ℝ) : ℝ :=
    ((((((((380436480 : ℝ)*t^15*b^11 + (760320000 : ℝ)*t^15*b^10) + ((-917913600 : ℝ)*t^15*b^9 + (-194641920 : ℝ)*t^15*b^8)) + (((-1711964160 : ℝ)*t^14*b^11 + (-5888332800 : ℝ)*t^14*b^10) + ((-1119467520 : ℝ)*t^14*b^9 + ((7807242240 : ℝ)*t^14*b^8 + (1455390720 : ℝ)*t^14*b^7)))) + ((((-355368960 : ℝ)*t^13*b^11 + (13650324480 : ℝ)*t^13*b^10) + ((31401544320 : ℝ)*t^13*b^9 + ((-11182429440 : ℝ)*t^13*b^8 + (-28524211200 : ℝ)*t^13*b^7))) + (((-4737761280 : ℝ)*t^13*b^6 + (10330260480 : ℝ)*t^12*b^11) + ((6508258560 : ℝ)*t^12*b^10 + ((-80915340960 : ℝ)*t^12*b^9 + (-100511867520 : ℝ)*t^12*b^8))))) + (((((46629964800 : ℝ)*t^12*b^7 + (58607642880 : ℝ)*t^12*b^6) + ((8763310080 : ℝ)*t^12*b^5 + (-5989294080 : ℝ)*t^11*b^11)) + (((-68644216800 : ℝ)*t^11*b^10 + (-9919419840 : ℝ)*t^11*b^9) + ((296461062720 : ℝ)*t^11*b^8 + ((224264338560 : ℝ)*t^11*b^7 + (-78136485120 : ℝ)*t^11*b^6)))) + ((((-74185873920 : ℝ)*t^11*b^5 + (-10063872000 : ℝ)*t^11*b^4) + ((-25579998720 : ℝ)*t^10*b^11 + ((52134024960 : ℝ)*t^10*b^10 + (295752228120 : ℝ)*t^10*b^9))) + (((-4340962800 : ℝ)*t^10*b^8 + (-635973301800 : ℝ)*t^10*b^7) + ((-352081228320 : ℝ)*t^10*b^6 + ((64918890720 : ℝ)*t^10*b^5 + (59312275200 : ℝ)*t^10*b^4)))))) + ((((((7338885120 : ℝ)*t^10*b^3 + (18668090880 : ℝ)*t^9*b^11) + ((94346639280 : ℝ)*t^9*b^10 + (-298595306835 : ℝ)*t^9*b^9)) + (((-856318230810 : ℝ)*t^9*b^8 + (-30476215440 : ℝ)*t^9*b^7) + ((825175303200 : ℝ)*t^9*b^6 + ((378002890800 : ℝ)*t^9*b^5 + (-20440176480 : ℝ)*t^9*b^4)))) + ((((-29296650240 : ℝ)*t^9*b^3 + (-3313336320 : ℝ)*t^9*b^2) + ((36716106240 : ℝ)*t^8*b^11 + ((-101792738880 : ℝ)*t^8*b^10 + (-191651792580 : ℝ)*t^8*b^9))) + (((866831875155 : ℝ)*t^8*b^8 + (1562433407640 : ℝ)*t^8*b^7) + ((176531015520 : ℝ)*t^8*b^6 + ((-657848792880 : ℝ)*t^8*b^5 + (-268220919600 : ℝ)*t^8*b^4))))) + (((((-7734346560 : ℝ)*t^8*b^3 + (8210937600 : ℝ)*t^8*b^2) + ((844922880 : ℝ)*t^8*b^1 + (-24480668160 : ℝ)*t^7*b^11)) + (((-62676516960 : ℝ)*t^7*b^10 + (413236421145 : ℝ)*t^7*b^9) + ((371295240255 : ℝ)*t^7*b^8 + ((-1358478775170 : ℝ)*t^7*b^7 + (-1788601942620 : ℝ)*t^7*b^6)))) + ((((-300919476960 : ℝ)*t^7*b^5 + (313333495920 : ℝ)*t^7*b^4) + ((119990262240 : ℝ)*t^7*b^3 + ((8667662400 : ℝ)*t^7*b^2 + (-1024750080 : ℝ)*t^7*b^1))) + (((-92897280 : ℝ)*t^7*b^0 + (-33455554560 : ℝ)*t^6*b^11) + ((53211936240 : ℝ)*t^6*b^10 + ((-103686730470 : ℝ)*t^6*b^9 + (-999533076885 : ℝ)*t^6*b^8))))))) + (((((((-617223834450 : ℝ)*t^6*b^7 + (1213314599250 : ℝ)*t^6*b^6) + ((1284578946720 : ℝ)*t^6*b^5 + (254923509600 : ℝ)*t^6*b^4)) + (((-79381800360 : ℝ)*t^6*b^3 + (-31079197440 : ℝ)*t^6*b^2) + ((-2625432480 : ℝ)*t^6*b^1 + ((11301120 : ℝ)*t^6*b^0 + (17998341120 : ℝ)*t^5*b^11)))) + ((((50435512560 : ℝ)*t^5*b^10 + (-96596064810 : ℝ)*t^5*b^9) + ((372063271005 : ℝ)*t^5*b^8 + ((1341612878805 : ℝ)*t^5*b^7 + (676203717780 : ℝ)*t^5*b^6))) + (((-612083672595 : ℝ)*t^5*b^5 + (-563602999050 : ℝ)*t^5*b^4) + ((-116782014240 : ℝ)*t^5*b^3 + ((6378089760 : ℝ)*t^5*b^2 + (3873400560 : ℝ)*t^5*b^1))))) + (((((261499680 : ℝ)*t^5*b^0 + (17614425600 : ℝ)*t^4*b^11) + ((-7440246720 : ℝ)*t^4*b^10 + (68099215230 : ℝ)*t^4*b^9)) + (((212404687380 : ℝ)*t^4*b^8 + (-387911195640 : ℝ)*t^4*b^7) + ((-1004524410645 : ℝ)*t^4*b^6 + ((-438986598030 : ℝ)*t^4*b^5 + (156801227355 : ℝ)*t^4*b^4)))) + ((((139999407840 : ℝ)*t^4*b^3 + (27452021040 : ℝ)*t^4*b^2) + ((938423520 : ℝ)*t^4*b^1 + ((-131327280 : ℝ)*t^4*b^0 + (-8032596480 : ℝ)*t^3*b^11))) + (((-35770753440 : ℝ)*t^3*b^10 + (-44502831225 : ℝ)*t^3*b^9) + ((-204851634435 : ℝ)*t^3*b^8 + ((-268135520040 : ℝ)*t^3*b^7 + (170144834985 : ℝ)*t^3*b^6)))))) + ((((((405456388830 : ℝ)*t^3*b^5 + (156823929765 : ℝ)*t^3*b^4) + ((-12779661240 : ℝ)*t^3*b^3 + (-16488579600 : ℝ)*t^3*b^2)) + (((-2678284080 : ℝ)*t^3*b^1 + (-105499440 : ℝ)*t^3*b^0) + ((-3696330240 : ℝ)*t^2*b^11 + ((6378476400 : ℝ)*t^2*b^10 + (21665313090 : ℝ)*t^2*b^9)))) + ((((53323088760 : ℝ)*t^2*b^8 + (172197416160 : ℝ)*t^2*b^7) + ((165744011970 : ℝ)*t^2*b^6 + ((-18114575580 : ℝ)*t^2*b^5 + (-76751437590 : ℝ)*t^2*b^4))) + (((-26522918100 : ℝ)*t^2*b^3 + (-1269154800 : ℝ)*t^2*b^2) + ((561718080 : ℝ)*t^2*b^1 + ((56937600 : ℝ)*t^2*b^0 + (1868659200 : ℝ)*t^1*b^11))))) + (((((8594916480 : ℝ)*t^1*b^10 + (8106131925 : ℝ)*t^1*b^9) + ((8682717285 : ℝ)*t^1*b^8 + ((-9993083085 : ℝ)*t^1*b^7 + (-52450687845 : ℝ)*t^1*b^6))) + (((-43195661460 : ℝ)*t^1*b^5 + (-5777689500 : ℝ)*t^1*b^4) + ((4172142420 : ℝ)*t^1*b^3 + ((1365040080 : ℝ)*t^1*b^2 + (111502800 : ℝ)*t^1*b^1)))) + ((((-136304640 : ℝ)*t^0*b^11 + (-2357984160 : ℝ)*t^0*b^10) + ((-5730354630 : ℝ)*t^0*b^9 + ((-5583211200 : ℝ)*t^0*b^8 + (-6110175600 : ℝ)*t^0*b^7))) + (((-2078603730 : ℝ)*t^0*b^6 + (3751029360 : ℝ)*t^0*b^5) + ((2918104020 : ℝ)*t^0*b^4 + ((699197760 : ℝ)*t^0*b^3 + (54565200 : ℝ)*t^0*b^2))))))))
private theorem product12 (t b : ℝ) : vN2 t b*p12 t b = z12 t b := by
  unfold vN2 p12 z12
  ring
private theorem quotient_e1 (t b : ℝ) :
    45 * (sourceE1 b).eval (t*b) = b^7*sourceQuotient 2 t b := by
  unfold sourceQuotient
  simp only [partial_Nt0,partial_Nb2,partial_Nb0,partial_Nt2,partial_Dt,partial_Db]
  simp only [expanded_D,expanded_N0,expanded_N2]
  rw [pair10,pair11,pair12,product10,product11,product12]
  simp only [sourceE1,z10,z11,z12,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_zero,eval_one,eval_ofNat]
  ring
/-- Exact normalization of the literal ordered source pair, with no division. -/
theorem source_e1_normalization (t b : ℝ) :
    45 * sourceD t b * (sourceE1 b).eval (t*b) =
      b^7*(sourceBt 0 t b*sourceBb 2 t b-sourceBb 0 t b*sourceBt 2 t b) := by
  rw [source_factor]
  calc
    _ = sourceD t b * (45 * (sourceE1 b).eval (t*b)) := by ring
    _ = sourceD t b * (b^7*sourceQuotient 2 t b) := by rw [quotient_e1]
    _ = _ := by ring

/-- All twenty-eight literal shifted rows, without deleting specialized zero rows. -/
def literalRow (b : ℝ) (i : Fin 28) : Polynomial ℝ :=
  if i.val < 14 then X^(13-i.val)*sourceE0 b else X^(27-i.val)*sourceE1 b

/-- Columns are ordered r^28,...,1, exactly as in VI Definition 4.1. -/
def literalMatrix (b : ℝ) : Matrix (Fin 28) (Fin 29) ℝ :=
  fun i j => (literalRow b i).coeff (28-j.val)

private theorem literal_row_degree (b : ℝ) (i : Fin 28) :
    (literalRow b i).natDegree ≤ 28 := by
  have he0 : (sourceE0 b).natDegree ≤ 15 := by unfold sourceE0; compute_degree
  have he1 : (sourceE1 b).natDegree ≤ 15 := by unfold sourceE1; compute_degree
  unfold literalRow
  split_ifs with hi
  · have h := natDegree_mul_le (p := (X^(13-i.val) : Polynomial ℝ)) (q := sourceE0 b)
    simp only [natDegree_X_pow] at h
    omega
  · have h := natDegree_mul_le (p := (X^(27-i.val) : Polynomial ℝ)) (q := sourceE1 b)
    simp only [natDegree_X_pow] at h
    omega

private theorem literal_row_root (b z : ℝ)
    (h0 : (sourceE0 b).eval z = 0) (h1 : (sourceE1 b).eval z = 0)
    (i : Fin 28) : (literalRow b i).eval z = 0 := by
  unfold literalRow
  split_ifs <;> simp only [eval_mul,eval_pow,eval_X,h0,h1,mul_zero]

private theorem literal_row_sum (b z : ℝ)
    (h0 : (sourceE0 b).eval z = 0) (h1 : (sourceE1 b).eval z = 0)
    (i : Fin 28) :
    (∑ j : Fin 28, (literalRow b i).coeff (28-j.val)*z^(28-j.val)) +
      (literalRow b i).coeff 0 = 0 := by
  have hs : (∑ j : Fin 29, (literalRow b i).coeff (28-j.val)*z^(28-j.val)) =
      (literalRow b i).eval z := by
    calc
      _ = ∑ j : Fin 29, (literalRow b i).coeff j.val*z^j.val := by
        simpa using (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin 29))
          (fun j : Fin 29 => (literalRow b i).coeff j.val*z^j.val))
      _ = ∑ j ∈ Finset.range 29, (literalRow b i).coeff j*z^j :=
        Fin.sum_univ_eq_sum_range (fun j => (literalRow b i).coeff j*z^j) 29
      _ = _ := (eval_eq_sum_range' (by have h := literal_row_degree b i; omega) z).symm
  rw [literal_row_root b z h0 h1 i] at hs
  rw [Fin.sum_univ_castSucc] at hs
  simpa only [Fin.val_castSucc,Fin.val_last,Nat.sub_self,pow_zero,mul_one] using hs

/-- The literal fixed minors obey the guarded source relation at every finite
common zero. The fixed degree and all original rows and columns are retained. -/
theorem literal_fixed_minor_relation (b z : ℝ)
    (h0 : (sourceE0 b).eval z = 0) (h1 : (sourceE1 b).eval z = 0) :
    z * (fixedMinorR (literalMatrix b)).det +
      (fixedMinorC (literalMatrix b)).det = 0 := by
  apply fixed_minor_linear_relation
  intro i
  have hs := literal_row_sum b z h0 h1 i
  have ht (j : Fin 28) :
      fixedMinorRootCoeffs z j • fixedMinorR (literalMatrix b) i j =
        -((literalRow b i).coeff (28-j.val)*z^(28-j.val)) := by
    by_cases hj : j.val < 27
    · simp only [fixedMinorRootCoeffs,fixedMinorR,hj,dite_true,literalMatrix,smul_eq_mul]
      ring
    · have hv : j.val = 27 := by omega
      simp [fixedMinorRootCoeffs,fixedMinorR,literalMatrix,hv]
      <;> ring
  simp only [ht,Finset.sum_neg_distrib]
  have hc : fixedMinorC (literalMatrix b) i 27 = (literalRow b i).coeff 0 := by
    simp [fixedMinorC,literalMatrix]
  rw [hc]
  linarith

/-- The literal source common-root criterion implies the same fixed-minor
relation in the independent source coordinates, including leading degree drops. -/
theorem source_fixed_minor_relation (t b : ℝ)
    (hd : sourceD t b ≠ 0)
    (hm0 : sourceBt 0 t b*sourceBb 1 t b-sourceBb 0 t b*sourceBt 1 t b = 0)
    (hm1 : sourceBt 0 t b*sourceBb 2 t b-sourceBb 0 t b*sourceBt 2 t b = 0) :
    (t*b) * (fixedMinorR (literalMatrix b)).det +
      (fixedMinorC (literalMatrix b)).det = 0 := by
  have h0 := source_e0_normalization t b
  have h1 := source_e1_normalization t b
  rw [hm0,mul_zero] at h0
  rw [hm1,mul_zero] at h1
  apply literal_fixed_minor_relation
  · exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (by norm_num) hd)
  · exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero (by norm_num) hd)

#print axioms source_e0_normalization
#print axioms source_e1_normalization
#print axioms source_fixed_minor_relation

end D5.S3.Observer.CubicGain.SourceFixedMinor
