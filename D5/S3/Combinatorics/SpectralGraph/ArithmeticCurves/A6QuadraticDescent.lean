/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6QuadraticDescent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6QuadraticDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full actual quadratic elliptic group descent and torsion transfer -/
import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6ModelEquivalences
/-! Source: complete original S.torsion, blob
2bb42a5280cb3ea4ebe596259d4ffbbb1fd37588 at PR9
6d491f77b35dec808fc777b69939c56cdae5dc02, Ma/Nikandish/Zhang.
This formalizes the full quadratic-field group descent. Rational torsion
triviality still needs the original prime-to-p good-reduction injection;
this descent and the finite counts do not replace that missing theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6QuadraticDescent
open A6EllipticModels A6GaloisCoset A6TorsionArithmetic A6ModelEquivalences
open WeierstrassCurve.Affine

theorem sigma_twice (P : KPoint) : sigma (sigma P)=P := by
  cases P with
  | zero => change sigma (sigma (0:KPoint))=0;simp
  | some U V h =>
    simp only [sigma,Point.map_some,Point.some.injEq]
    constructor <;> ext <;> simp [conjugation]

theorem trace_rational (P : KPoint) : ∃ Q : QPoint,embed Q=P+sigma P := by
  apply (fixed_iff_rational _).mp
  rw [map_add,sigma_twice]
  exact add_comm _ _

theorem anti_sigma (P : KPoint) : sigma (P-sigma P)= -(P-sigma P) := by
  rw [map_sub,sigma_twice]
  abel

/-- The complete cubic has no root in the actual quadratic field. -/
theorem quadratic_no_root (X : K) : X^3-78162568812*X+8433576786332241≠0 := by
  intro he
  have hre:=congrArg QuadraticAlgebra.re he
  have him:=congrArg QuadraticAlgebra.im he
  norm_num [pow_succ,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat] at hre him
  by_cases hb : X.im=0
  · apply rational_no_root X.re
    simpa [hb,pow_succ] using hre
  · have hh : 3*X.re^2+43645*X.im^2-78162568812=0 := by
      apply (mul_eq_zero.mp (show (3*X.re^2+43645*X.im^2-78162568812)*X.im=0 by
        linear_combination him)).resolve_right hb
    apply rational_no_root (-2*X.re)
    linear_combination hre-3*X.re*hh

/-- No nonidentity two-torsion exists on the full actual E(K). -/
theorem shortK_no_two_torsion (P : (E.baseChange K).toAffine.Point)
    (hP : P+P=0) : P=0 := by
  cases P with
  | zero => rfl
  | some X Y h =>
    have hr:=Point.isRoot_twoTorsionPolynomial_of_add_self h hP
    rw [Polynomial.IsRoot.def,WeierstrassCurve.eval_toPoly_twoTorsionPolynomial] at hr
    simp [E,WeierstrassCurve.baseChange,WeierstrassCurve.map,WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,WeierstrassCurve.b₆] at hr
    exfalso
    apply quadratic_no_root X
    linear_combination hr/4

theorem E0K_no_two_torsion (P : KPoint) (hP : P+P=0) : P=0 := by
  apply shortKEquiv.injective
  rw [map_zero]
  apply shortK_no_two_torsion
  rw [←map_add,hP,map_zero]

/-- Every anti-invariant actual point maps to a rational point of the actual twist. -/
theorem anti_to_twist_rational (P : KPoint) (hP : sigma P= -P) :
    ∃ R : Ed.toAffine.Point,embedTwist R=twistKEquiv (shortKEquiv P) := by
  cases P with
  | zero =>
    refine ⟨0,?_⟩
    change embedTwist 0=twistKEquiv (shortKEquiv (0:KPoint))
    simp
  | some U V h =>
    have he : conjugation U=U ∧
        conjugation V=(E0.baseChange K).toAffine.negY U V := Point.some.inj hP
    have hUi : U.im=0 := by
      have hh:=congrArg QuadraticAlgebra.im he.1
      simp [conjugation] at hh
      linarith
    have hVr : V.re=0 := by
      have hh:=congrArg QuadraticAlgebra.re he.2
      simp [conjugation,negY,E0,WeierstrassCurve.baseChange,WeierstrassCurve.map] at hh
      linarith
    obtain ⟨hshort,hshortEq⟩:=shortK_some U V h
    obtain ⟨htwist,htwistEq⟩:=twistK_some _ _ hshort
    let X : K:=43645*((9*U+19920450)/100)
    let Y : K:=43645*sqrtD*(27*V/1000)
    have hXi : X.im=0 := by
      dsimp [X]
      simp [QuadraticAlgebra.div_def,QuadraticAlgebra.inv_def,QuadraticAlgebra.norm_def,hUi,
        QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
    have hYi : Y.im=0 := by
      dsimp [Y]
      simp [sqrtD,QuadraticAlgebra.div_def,QuadraticAlgebra.inv_def,
        QuadraticAlgebra.norm_def,hVr,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
    have hX : (Algebra.ofId ℚ K) X.re=X := by ext <;> simp [hXi]
    have hY : (Algebra.ofId ℚ K) Y.re=Y := by ext <;> simp [hYi]
    have hR : Ed.toAffine.Nonsingular X.re Y.re :=
      (Ed.toAffine.baseChange_nonsingular (Algebra.ofId ℚ K).injective _ _).mp
        (by simpa only [hX,hY] using htwist)
    refine ⟨.some X.re Y.re hR,?_⟩
    rw [hshortEq,htwistEq]
    change Point.some ((Algebra.ofId ℚ K) X.re) ((Algebra.ofId ℚ K) Y.re) _=
      Point.some X Y _
    simp only [Point.some.injEq]
    exact ⟨hX,hY⟩

private theorem embed_injective : Function.Injective embed :=
  Point.map_injective (W':=E0.toAffine) (Algebra.ofId ℚ K)
private theorem embedTwist_injective : Function.Injective embedTwist :=
  Point.map_injective (W':=Ed.toAffine) (Algebra.ofId ℚ K)

/-- Rational trace on every actual K-point, with no torsion assumption. -/
def rationalTrace (P : KPoint) : QPoint := Classical.choose (trace_rational P)
theorem embed_rationalTrace (P : KPoint) : embed (rationalTrace P)=P+sigma P :=
  Classical.choose_spec (trace_rational P)

def traceHom : KPoint →+ QPoint where
  toFun:=rationalTrace
  map_zero':=by
    apply embed_injective
    rw [embed_rationalTrace,map_zero,map_zero]
    simp
  map_add':=by
    intro P Q
    apply embed_injective
    rw [map_add,embed_rationalTrace,embed_rationalTrace,embed_rationalTrace,map_add]
    abel

/-- Rational twist component on every actual K-point. -/
def rationalAnti (P : KPoint) : Ed.toAffine.Point :=
  Classical.choose (anti_to_twist_rational (P-sigma P) (anti_sigma P))
theorem embed_rationalAnti (P : KPoint) :
    embedTwist (rationalAnti P)=twistKEquiv (shortKEquiv (P-sigma P)) :=
  Classical.choose_spec (anti_to_twist_rational (P-sigma P) (anti_sigma P))

def antiHom : KPoint →+ Ed.toAffine.Point where
  toFun:=rationalAnti
  map_zero':=by
    apply embedTwist_injective
    rw [embed_rationalAnti,map_zero,map_zero,sub_self,map_zero,map_zero]
  map_add':=by
    intro P Q
    apply embedTwist_injective
    rw [map_add,embed_rationalAnti,embed_rationalAnti,embed_rationalAnti,map_add]
    have he : P+Q-(sigma P+sigma Q)=(P-sigma P)+(Q-sigma Q) := by abel
    rw [he,map_add,map_add]

/-- Full actual quadratic-field group descent into the two rational point groups. -/
def descentHom : KPoint →+ QPoint × Ed.toAffine.Point := traceHom.prod antiHom

/-- The full descent is injective; the missing rational torsion theorem is not assumed. -/
theorem descent_injective : Function.Injective descentHom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro P hP
  have ht : rationalTrace P=0:=congrArg Prod.fst hP
  have ha : rationalAnti P=0:=congrArg Prod.snd hP
  have htrace : P+sigma P=0 := by rw [←embed_rationalTrace,ht,map_zero]
  have hanti : P-sigma P=0 := by
    apply shortKEquiv.injective
    apply twistKEquiv.injective
    rw [←embed_rationalAnti,ha,map_zero,map_zero,map_zero]
  apply E0K_no_two_torsion
  calc
    P+P=(P+sigma P)+(P-sigma P) := by abel
    _=0:=by rw [htrace,hanti];simp

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6QuadraticDescent
