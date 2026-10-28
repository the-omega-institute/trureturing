/- GID: D5/S3/Observer/CubicGain/SourceFixedMinor
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/SourceFixedMinor
   mirror-E: none(waiver:source-fixed-minor-continuation)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Derivative]
   utility: none
   digest: Literal clock-five-six-seven minor polynomials and their fixed-degree leading guard. -/

import D5.S3.Observer.CubicGain.ExactW3Center
import Mathlib.Algebra.Polynomial.Derivative

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
def sourceE0 (b : ℝ) : Polynomial ℝ :=
    C ((-102720) * b^2) * X^15 +
    C ((-821760) * b^1) * X^15 +
    C ((-410880) * b^0) * X^15 +
    C ((462240) * b^3) * X^14 +
    C ((4468320) * b^2) * X^14 +
    C ((8012160) * b^1) * X^14 +
    C ((3081600) * b^0) * X^14 +
    C ((-7143760) * b^4) * X^13 +
    C ((-11582400) * b^3) * X^13 +
    C ((-30276960) * b^2) * X^13 +
    C ((-32838400) * b^1) * X^13 +
    C ((-10066560) * b^0) * X^13 +
    C ((22459578) * b^5) * X^12 +
    C ((56745342) * b^4) * X^12 +
    C ((62161092) * b^3) * X^12 +
    C ((95034456) * b^2) * X^12 +
    C ((75090096) * b^1) * X^12 +
    C ((18695040) * b^0) * X^12 +
    C ((-9217971) * b^6) * X^11 +
    C ((-141242232) * b^5) * X^11 +
    C ((-193416828) * b^4) * X^11 +
    C ((-155883048) * b^3) * X^11 +
    C ((-171106272) * b^2) * X^11 +
    C ((-106073376) * b^1) * X^11 +
    C ((-21571200) * b^0) * X^11 +
    C ((-43923051) * b^7) * X^10 +
    C ((55368967) * b^6) * X^10 +
    C ((397068070) * b^5) * X^10 +
    C ((365740526) * b^4) * X^10 +
    C ((216529540) * b^3) * X^10 +
    C ((189534136) * b^2) * X^10 +
    C ((96050000) * b^1) * X^10 +
    C ((15818880) * b^0) * X^10 +
    C ((47580070) * b^8) * X^9 +
    C ((237039086) * b^7) * X^9 +
    C ((-146554321) * b^6) * X^9 +
    C ((-651464362) * b^5) * X^9 +
    C ((-411805396) * b^4) * X^9 +
    C ((-167471368) * b^3) * X^9 +
    C ((-129332480) * b^2) * X^9 +
    C ((-55577280) * b^1) * X^9 +
    C ((-7190400) * b^0) * X^9 +
    C ((15571863) * b^9) * X^8 +
    C ((-282359934) * b^8) * X^8 +
    C ((-569712687) * b^7) * X^8 +
    C ((233326389) * b^6) * X^8 +
    C ((682350220) * b^5) * X^8 +
    C ((269525838) * b^4) * X^8 +
    C ((55675140) * b^3) * X^8 +
    C ((50405320) * b^2) * X^8 +
    C ((19663440) * b^1) * X^8 +
    C ((1848960) * b^0) * X^8 +
    C ((-37353091) * b^10) * X^7 +
    C ((-19992407) * b^9) * X^7 +
    C ((699003766) * b^8) * X^7 +
    C ((778382188) * b^7) * X^7 +
    C ((-259457859) * b^6) * X^7 +
    C ((-469417860) * b^5) * X^7 +
    C ((-82711964) * b^4) * X^7 +
    C ((13760648) * b^3) * X^7 +
    C ((-8174176) * b^2) * X^7 +
    C ((-3801376) * b^1) * X^7 +
    C ((-205440) * b^0) * X^7 +
    C ((8687448) * b^11) * X^6 +
    C ((185858499) * b^10) * X^6 +
    C ((-40242750) * b^9) * X^6 +
    C ((-933174884) * b^8) * X^6 +
    C ((-633912971) * b^7) * X^6 +
    C ((216188371) * b^6) * X^6 +
    C ((211160574) * b^5) * X^6 +
    C ((-7312454) * b^4) * X^6 +
    C ((-19363172) * b^3) * X^6 +
    C ((-783928) * b^2) * X^6 +
    C ((296496) * b^1) * X^6 +
    C ((3317251) * b^12) * X^5 +
    C ((-87048314) * b^11) * X^5 +
    C ((-368371929) * b^10) * X^5 +
    C ((104816472) * b^9) * X^5 +
    C ((722665054) * b^8) * X^5 +
    C ((291737766) * b^7) * X^5 +
    C ((-131748529) * b^6) * X^5 +
    C ((-60417178) * b^5) * X^5 +
    C ((13788732) * b^4) * X^5 +
    C ((6435240) * b^3) * X^5 +
    C ((334304) * b^2) * X^5 +
    C ((-636165) * b^13) * X^4 +
    C ((-6876073) * b^12) * X^4 +
    C ((204832493) * b^11) * X^4 +
    C ((375617729) * b^10) * X^4 +
    C ((-93346391) * b^9) * X^4 +
    C ((-325126952) * b^8) * X^4 +
    C ((-60501195) * b^7) * X^4 +
    C ((52506641) * b^6) * X^4 +
    C ((10384310) * b^5) * X^4 +
    C ((-3708596) * b^4) * X^4 +
    C ((-723912) * b^3) * X^4 +
    C ((2649746) * b^14) * X^3 +
    C ((17699710) * b^13) * X^3 +
    C ((3262907) * b^12) * X^3 +
    C ((-199823808) * b^11) * X^3 +
    C ((-203793686) * b^10) * X^3 +
    C ((45069967) * b^9) * X^3 +
    C ((81542558) * b^8) * X^3 +
    C ((-478476) * b^7) * X^3 +
    C ((-11295928) * b^6) * X^3 +
    C ((-881120) * b^5) * X^3 +
    C ((298560) * b^4) * X^3 +
    C ((-2637039) * b^15) * X^2 +
    C ((-10326504) * b^14) * X^2 +
    C ((-36904122) * b^13) * X^2 +
    C ((-4673923) * b^12) * X^2 +
    C ((85627677) * b^11) * X^2 +
    C ((52032126) * b^10) * X^2 +
    C ((-14379758) * b^9) * X^2 +
    C ((-11117238) * b^8) * X^2 +
    C ((1330788) * b^7) * X^2 +
    C ((884240) * b^6) * X^2 +
    C ((398475) * b^16) * X^1 +
    C ((4321197) * b^15) * X^1 +
    C ((13472587) * b^14) * X^1 +
    C ((25681227) * b^13) * X^1 +
    C ((5012428) * b^12) * X^1 +
    C ((-14193728) * b^11) * X^1 +
    C ((-4554672) * b^10) * X^1 +
    C ((2416648) * b^9) * X^1 +
    C ((868800) * b^8) * X^1 +
    C ((155926) * b^17) * X^0 +
    C ((-601697) * b^16) * X^0 +
    C ((-1542906) * b^15) * X^0 +
    C ((-4285783) * b^14) * X^0 +
    C ((-4638172) * b^13) * X^0 +
    C ((-687942) * b^12) * X^0 +
    C ((930652) * b^11) * X^0 +
    C ((283120) * b^10) * X^0

/-- Coefficients in r of the normalized pair (N0,N2), with fixed degree fifteen. -/
def sourceE1 (b : ℝ) : Polynomial ℝ :=
    C ((-657408) * b^2) * X^15 +
    C ((-5259264) * b^1) * X^15 +
    C ((-2629632) * b^0) * X^15 +
    C ((2958336) * b^3) * X^14 +
    C ((28597248) * b^2) * X^14 +
    C ((51277824) * b^1) * X^14 +
    C ((19722240) * b^0) * X^14 +
    C ((-18426880) * b^4) * X^13 +
    C ((-48410304) * b^3) * X^13 +
    C ((-190071552) * b^2) * X^13 +
    C ((-211083520) * b^1) * X^13 +
    C ((-64425984) * b^0) * X^13 +
    C ((48118592) * b^5) * X^12 +
    C ((95654432) * b^4) * X^12 +
    C ((217707360) * b^3) * X^12 +
    C ((587379968) * b^2) * X^12 +
    C ((486541952) * b^1) * X^12 +
    C ((119648256) * b^0) * X^12 +
    C ((-9870816) * b^6) * X^11 +
    C ((-239739808) * b^5) * X^11 +
    C ((-161018400) * b^4) * X^11 +
    C ((-453449856) * b^3) * X^11 +
    C ((-1049087872) * b^2) * X^11 +
    C ((-695388672) * b^1) * X^11 +
    C ((-138055680) * b^0) * X^11 +
    C ((-105757736) * b^7) * X^10 +
    C ((107992057) * b^6) * X^10 +
    C ((488410918) * b^5) * X^10 +
    C ((-50951628) * b^4) * X^10 +
    C ((466298488) * b^3) * X^10 +
    C ((1167494272) * b^2) * X^10 +
    C ((639956864) * b^1) * X^10 +
    C ((101240832) * b^0) * X^10 +
    C ((84575416) * b^8) * X^9 +
    C ((457897569) * b^7) * X^9 +
    C ((-423187248) * b^6) * X^9 +
    C ((-487598432) * b^5) * X^9 +
    C ((624941312) * b^4) * X^9 +
    C ((-134055888) * b^3) * X^9 +
    C ((-819641088) * b^2) * X^9 +
    C ((-378636544) * b^1) * X^9 +
    C ((-46018560) * b^0) * X^9 +
    C ((61771440) * b^9) * X^8 +
    C ((-533982882) * b^8) * X^8 +
    C ((-795199041) * b^7) * X^8 +
    C ((920669835) * b^6) * X^8 +
    C ((178620594) * b^5) * X^8 +
    C ((-1107508428) * b^4) * X^8 +
    C ((-218343960) * b^3) * X^8 +
    C ((347807232) * b^2) * X^8 +
    C ((138234240) * b^1) * X^8 +
    C ((11833344) * b^0) * X^8 +
    C ((-58757336) * b^10) * X^7 +
    C ((-65822345) * b^9) * X^7 +
    C ((1331732933) * b^8) * X^7 +
    C ((600163934) * b^7) * X^7 +
    C ((-1293635116) * b^6) * X^7 +
    C ((98836144) * b^5) * X^7 +
    C ((1027468608) * b^4) * X^7 +
    C ((278562976) * b^3) * X^7 +
    C ((-77093248) * b^2) * X^7 +
    C ((-27999232) * b^1) * X^7 +
    C ((-1314816) * b^0) * X^7 +
    C ((-17329720) * b^11) * X^6 +
    C ((315478799) * b^10) * X^6 +
    C ((-240251601) * b^9) * X^6 +
    C ((-1721263368) * b^8) * X^6 +
    C ((53490740) * b^7) * X^6 +
    C ((1228365327) * b^6) * X^6 +
    C ((-128565094) * b^5) * X^6 +
    C ((-557545492) * b^4) * X^6 +
    C ((-143256888) * b^3) * X^6 +
    C ((4496512) * b^2) * X^6 +
    C ((2356352) * b^1) * X^6 +
    C ((-3666480) * b^12) * X^5 +
    C ((-109942566) * b^11) * X^5 +
    C ((-599971215) * b^10) * X^5 +
    C ((610641617) * b^9) * X^5 +
    C ((1248579290) * b^8) * X^5 +
    C ((-480319011) * b^7) * X^5 +
    C ((-773491684) * b^6) * X^5 +
    C ((45889056) * b^5) * X^5 +
    C ((172938864) * b^4) * X^5 +
    C ((35288688) * b^3) * X^5 +
    C ((775936) * b^2) * X^5 +
    C ((21928328) * b^13) * X^4 +
    C ((10721323) * b^12) * X^4 +
    C ((379412584) * b^11) * X^4 +
    C ((521597159) * b^10) * X^4 +
    C ((-622274083) * b^9) * X^4 +
    C ((-522632408) * b^8) * X^4 +
    C ((381230413) * b^7) * X^4 +
    C ((299652533) * b^6) * X^4 +
    C ((-2965074) * b^5) * X^4 +
    C ((-27033908) * b^4) * X^4 +
    C ((-3298952) * b^3) * X^4 +
    C ((6253720) * b^14) * X^3 +
    C ((-6121075) * b^13) * X^3 +
    C ((-30525463) * b^12) * X^3 +
    C ((-397217716) * b^11) * X^3 +
    C ((-183175273) * b^10) * X^3 +
    C ((360103188) * b^9) * X^3 +
    C ((137704477) * b^8) * X^3 +
    C ((-126531840) * b^7) * X^3 +
    C ((-60883208) * b^6) * X^3 +
    C ((-1006896) * b^5) * X^3 +
    C ((1481520) * b^4) * X^3 +
    C ((-12208160) * b^15) * X^2 +
    C ((-17599208) * b^14) * X^2 +
    C ((-45540924) * b^13) * X^2 +
    C ((25570965) * b^12) * X^2 +
    C ((164605488) * b^11) * X^2 +
    C ((-11384076) * b^10) * X^2 +
    C ((-124786956) * b^9) * X^2 +
    C ((-29884834) * b^8) * X^2 +
    C ((14801004) * b^7) * X^2 +
    C ((4388320) * b^6) * X^2 +
    C ((1528984) * b^16) * X^1 +
    C ((15864033) * b^15) * X^1 +
    C ((23224069) * b^14) * X^1 +
    C ((35493199) * b^13) * X^1 +
    C ((-15108345) * b^12) * X^1 +
    C ((-32123964) * b^11) * X^1 +
    C ((12588474) * b^10) * X^1 +
    C ((19459008) * b^9) * X^1 +
    C ((4310120) * b^8) * X^1 +
    C ((960520) * b^17) * X^0 +
    C ((-2391609) * b^16) * X^0 +
    C ((-2601574) * b^15) * X^0 +
    C ((-2463507) * b^14) * X^0 +
    C ((1450942) * b^13) * X^0 +
    C ((9415154) * b^12) * X^0 +
    C ((6961040) * b^11) * X^0 +
    C ((1403320) * b^10) * X^0

/-- The denominator and all four samples coincide with the existing actual circuit. -/
theorem source_circuit_correspondence (t b : ℝ) :
    sourceD t b = circuitD (t,b) ∧ sourceC t b = circuitC (t,b) ∧
    sourceNumerator t b 0 = circuitP (t,b) := by
  exact ⟨rfl, rfl, rfl⟩

private def sourceNt (i : Fin 3) (t b : ℝ) : ℝ :=
  (sourceNumerator (X : Polynomial ℝ) (C b) i).derivative.eval t
private def sourceNb (i : Fin 3) (t b : ℝ) : ℝ :=
  (sourceNumerator (C t) (X : Polynomial ℝ) i).derivative.eval b
private def sourceDt (t b : ℝ) : ℝ :=
  (sourceD (X : Polynomial ℝ) (C b)).derivative.eval t
private def sourceDb (t b : ℝ) : ℝ :=
  (sourceD (C t) (X : Polynomial ℝ)).derivative.eval b
private def sourceQuotient (k : Fin 3) (t b : ℝ) : ℝ :=
  sourceD t b*(sourceNt 0 t b*sourceNb k t b-sourceNb 0 t b*sourceNt k t b) -
  sourceNumerator t b 0*(sourceDt t b*sourceNb k t b-sourceDb t b*sourceNt k t b) -
  sourceNumerator t b k*(sourceNt 0 t b*sourceDb t b-sourceNb 0 t b*sourceDt t b)

private theorem source_factor (k : Fin 3) (t b : ℝ) :
    sourceBt 0 t b*sourceBb k t b-sourceBb 0 t b*sourceBt k t b =
      sourceD t b*sourceQuotient k t b := by
  unfold sourceBt sourceBb sourceQuotient sourceNt sourceNb sourceDt sourceDb
  ring

private theorem quotient_e0 (t b : ℝ) :
    45 * (sourceE0 b).eval (t*b) = b^7*sourceQuotient 1 t b := by
  simp only [sourceE0, sourceQuotient, sourceNt, sourceNb, sourceDt, sourceDb,
    sourceNumerator, sourceC, sourceD, sourceN, sourceJ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_X, derivative_natCast,
    eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
    eval_natCast, eval_neg, derivative_neg, derivative_ofNat]
  ring

/-- Exact polynomial normalization before any specialization or division. -/
theorem source_e0_normalization (t b : ℝ) :
    45 * sourceD t b * (sourceE0 b).eval (t*b) =
      b^7*(sourceBt 0 t b*sourceBb 1 t b-sourceBb 0 t b*sourceBt 1 t b) := by
  rw [source_factor]
  calc
    _ = sourceD t b * (45 * (sourceE0 b).eval (t*b)) := by ring
    _ = sourceD t b * (b^7*sourceQuotient 1 t b) := by rw [quotient_e0]
    _ = _ := by ring

private theorem quotient_e1 (t b : ℝ) :
    45 * (sourceE1 b).eval (t*b) = b^7*sourceQuotient 2 t b := by
  simp only [sourceE1, sourceQuotient, sourceNt, sourceNb, sourceDt, sourceDb,
    sourceNumerator, sourceC, sourceD, sourceN, sourceJ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons,
    derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_X, derivative_natCast,
    eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
    eval_natCast, eval_neg, derivative_neg, derivative_ofNat]
  ring

/-- Exact polynomial normalization before any specialization or division. -/
theorem source_e1_normalization (t b : ℝ) :
    45 * sourceD t b * (sourceE1 b).eval (t*b) =
      b^7*(sourceBt 0 t b*sourceBb 2 t b-sourceBb 0 t b*sourceBt 2 t b) := by
  rw [source_factor]
  calc
    _ = sourceD t b * (45 * (sourceE1 b).eval (t*b)) := by ring
    _ = sourceD t b * (b^7*sourceQuotient 2 t b) := by rw [quotient_e1]
    _ = _ := by ring

/-- Fixed leading coefficients of the two literal normalized minor polynomials. -/
theorem source_leading_coefficients (b : ℝ) :
    (sourceE0 b).coeff 15 = -102720*(b^2+8*b+4) ∧
    (sourceE1 b).coeff 15 = -657408*(b^2+8*b+4) := by
  constructor <;> simp [sourceE0, sourceE1, coeff_add, coeff_C_mul] <;> ring

/-- At the selected FC root both fixed degree-fifteen leading coefficients are nonzero. -/
theorem selected_root_leading_guard :
    (sourceE0 criticalRoot).coeff 15 ≠ 0 ∧
    (sourceE1 criticalRoot).coeff 15 ≠ 0 := by
  have hb : 0 < criticalRoot := by linarith [criticalRoot_spec.1]
  rw [(source_leading_coefficients criticalRoot).1,
    (source_leading_coefficients criticalRoot).2]
  constructor <;> apply mul_ne_zero (by norm_num) <;> positivity

#print axioms source_e0_normalization
#print axioms source_e1_normalization
#print axioms selected_root_leading_guard

end D5.S3.Observer.CubicGain.SourceFixedMinor
