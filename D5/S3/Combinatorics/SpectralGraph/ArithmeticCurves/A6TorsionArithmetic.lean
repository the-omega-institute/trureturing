/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6TorsionArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6TorsionArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact actual a6 elliptic reduction groups and rational two-torsion exclusion -/
import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6EllipticModels
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Option
/-! Supplied S.torsion, original blob2bb42a5280cb3ea4ebe596259d4ffbbb1fd37588,
S.nontorsion blob01edb67a7e6753c17ecae77e581d4957fe6b94cc,
PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02.
Original Nikandish problem and Ma/Nikandish/Zhang attribution remain.
The actual finite elliptic groups and rational two-torsion exclusion below
are inputs to the received full torsion proof. Prime-to-p reduction
injectivity, Nagell-Lutz and the full torsion/infinite-order/rank/isogeny
conclusions are not asserted by these arithmetic inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6TorsionArithmetic
open A6EllipticModels WeierstrassCurve.Affine Polynomial
private instance : Fact (Nat.Prime 11):=⟨by decide⟩
private instance : Fact (Nat.Prime 17):=⟨by decide⟩
private instance : Fact (Nat.Prime 23):=⟨by decide⟩

def integerE : WeierstrassCurve ℤ := ⟨0,0,0,-78162568812,8433576786332241⟩
def integerTwist : WeierstrassCurve ℤ :=
  ⟨0,0,0,43645^2*(-78162568812),43645^3*8433576786332241⟩
def Ed : WeierstrassCurve ℚ := integerTwist.map (Int.castRingHom ℚ)

theorem integerE_rational : integerE.map (Int.castRingHom ℚ)=E := by rfl

def reduction (C : WeierstrassCurve ℤ) (p : ℕ) : WeierstrassCurve (ZMod p) :=
  C.map (Int.castRingHom (ZMod p))

theorem reductionE11 : reduction integerE 11=⟨0,0,0,2,5⟩ := by
  ext <;> norm_num [reduction,integerE,WeierstrassCurve.map] <;> decide
theorem reductionE17 : reduction integerE 17=⟨0,0,0,10,11⟩ := by
  ext <;> norm_num [reduction,integerE,WeierstrassCurve.map] <;> decide
theorem reductionTwist11 : reduction integerTwist 11=⟨0,0,0,7,8⟩ := by
  ext <;> norm_num [reduction,integerTwist,WeierstrassCurve.map] <;> decide
theorem reductionTwist17 : reduction integerTwist 17=⟨0,0,0,3,13⟩ := by
  ext <;> norm_num [reduction,integerTwist,WeierstrassCurve.map] <;> decide

private theorem short_count {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (n : ℕ)
    (hc : Fintype.card {xy : ZMod p × ZMod p // xy.2^2=xy.1^3+a*xy.1+b}=n)
    (he : (⟨0,0,0,a,b⟩ : WeierstrassCurve (ZMod p)).IsElliptic) :
    Nat.card (⟨0,0,0,a,b⟩ : WeierstrassCurve (ZMod p)).toAffine.Point=n+1 := by
  let C : WeierstrassCurve (ZMod p):=⟨0,0,0,a,b⟩
  letI : C.IsElliptic:=he
  have hiff (xy : ZMod p × ZMod p) :
      C.toAffine.Equation xy.1 xy.2 ↔ xy.2^2=xy.1^3+a*xy.1+b := by
    rw [equation_iff]
    simp [C]
  have e := (C.toAffine.pointEquiv).trans ((Equiv.subtypeEquivRight hiff).optionCongr)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_option,hc]

private theorem short_elliptic {p : ℕ} [Fact p.Prime] (a b : ZMod p)
    (h : -16*(4*a^3+27*b^2)≠0) :
    (⟨0,0,0,a,b⟩ : WeierstrassCurve (ZMod p)).IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  convert h using 1 <;>
    simp [WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈] <;> ring

theorem E11_order : Nat.card (reduction integerE 11).toAffine.Point=10 := by
  rw [reductionE11]
  exact short_count 2 5 9 (by decide) (short_elliptic _ _ (by decide))
theorem E17_order : Nat.card (reduction integerE 17).toAffine.Point=16 := by
  rw [reductionE17]
  exact short_count 10 11 15 (by decide) (short_elliptic _ _ (by decide))
theorem twist11_order : Nat.card (reduction integerTwist 11).toAffine.Point=14 := by
  rw [reductionTwist11]
  exact short_count 7 8 13 (by decide) (short_elliptic _ _ (by decide))
theorem twist17_order : Nat.card (reduction integerTwist 17).toAffine.Point=20 := by
  rw [reductionTwist17]
  exact short_count 3 13 19 (by decide) (short_elliptic _ _ (by decide))

/-- The complete specified modulo23 domain, with every horizontal value. -/
theorem mod23_no_root (x : ZMod 23) : x^3-x+15≠0 := by
  revert x
  decide

private def cubic : ℤ[X] := X^3+C (-78162568812)*X+C 8433576786332241
private theorem cubic_monic : cubic.Monic := by
  unfold cubic
  rw [add_assoc]
  apply monic_X_pow_add
  exact lt_of_le_of_lt (degree_add_le _ _) (max_lt_iff.mpr
    ⟨lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num),lt_of_le_of_lt degree_C_le (by norm_num)⟩)

/-- No rational root is discarded by choosing a finite rational search. -/
theorem rational_no_root (x : ℚ) : x^3-78162568812*x+8433576786332241≠0 := by
  intro h
  have hr : aeval x cubic=0 := by
    simp only [cubic,map_add,map_mul,map_pow,aeval_X,aeval_C]
    norm_num <;> linarith
  obtain ⟨z,hz,_⟩:=exists_integer_of_is_root_of_monic cubic_monic hr
  change x=(z:ℚ) at hz
  have hzQ : (z:ℚ)^3-78162568812*z+8433576786332241=0 := by simpa [hz] using h
  have hzZ : z^3-78162568812*z+8433576786332241=0 := by exact_mod_cast hzQ
  have hz23:=congrArg (Int.castRingHom (ZMod 23)) hzZ
  norm_num at hz23
  have ha : (78162568812:ZMod 23)=1:=by decide
  have hb : (8433576786332241:ZMod 23)=15:=by decide
  change (z:ZMod 23)^3-(78162568812:ZMod 23)*(z:ZMod 23)+(8433576786332241:ZMod 23)=0 at hz23
  rw [ha,hb,one_mul] at hz23
  exact mod23_no_root (z:ZMod 23) hz23

theorem twist_no_root (x : ℚ) :
    x^3+(43645^2*(-78162568812))*x+43645^3*8433576786332241≠0 := by
  intro h
  apply rational_no_root (x/43645)
  linear_combination h/43645^3

/-- Actual full rational point group, including the identity. -/
theorem E_no_two_torsion (P : E.toAffine.Point) (hP : P+P=0) : P=0 := by
  cases P with
  | zero => rfl
  | some x y h =>
    have hr:=Point.isRoot_twoTorsionPolynomial_of_add_self h hP
    rw [IsRoot.def,WeierstrassCurve.eval_toPoly_twoTorsionPolynomial] at hr
    rw [← integerE_rational] at hr
    simp [integerE,WeierstrassCurve.map,WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,WeierstrassCurve.b₆] at hr
    exfalso
    apply rational_no_root x
    linarith [hr]

theorem twist_no_two_torsion (P : Ed.toAffine.Point) (hP : P+P=0) : P=0 := by
  cases P with
  | zero => rfl
  | some x y h =>
    have hr:=Point.isRoot_twoTorsionPolynomial_of_add_self h hP
    rw [IsRoot.def,WeierstrassCurve.eval_toPoly_twoTorsionPolynomial] at hr
    simp [Ed,integerTwist,WeierstrassCurve.map,WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,WeierstrassCurve.b₆] at hr
    exfalso
    apply twist_no_root x
    linarith [hr]

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6TorsionArithmetic
