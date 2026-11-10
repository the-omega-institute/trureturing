/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6GaloisCoset
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6GaloisCoset
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full actual quadratic-field Galois-difference fiber and rational-group coset -/

import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6EllipticModels

/-! Source: supplied S.coset, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02, original blob
8f84b430e880aeef5747688e95608220bbfc96a2. Original Nikandish
problem and Ma/Nikandish/Zhang attribution are retained.
All points and group operations below are actual Weierstrass points.
Translated integrality is imposed on the field point, not on its
rational-group parameter. No rank, saturation or point list is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped Classical QuadraticAlgebra
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6GaloisCoset
open A6EllipticModels
open WeierstrassCurve.Affine

abbrev KPoint := (E0.toAffine.baseChange K).Point
abbrev QPoint := E0.toAffine.Point

def conjugation : K →ₐ[ℚ] K :=
  { (starRingAut : RingAut K).toRingHom with
    commutes' := by intro q;ext <;> simp [QuadraticAlgebra.algebraMap_eq] }

def sigma : KPoint →+ KPoint := Point.map (W':=E0.toAffine) conjugation

def embed : QPoint →+ KPoint := Point.baseChange (W':=E0.toAffine) ℚ K

theorem sigma_embed (Q : QPoint) : sigma (embed Q)=embed Q := by
  exact Point.map_baseChange (W':=E0.toAffine) conjugation Q

/-- Fixed points of the full field group are exactly the rational group. -/
theorem fixed_iff_rational (P : KPoint) : sigma P=P ↔ ∃ Q : QPoint, embed Q=P := by
  constructor
  · intro hP
    cases P with
    | zero => exact ⟨0,rfl⟩
    | some U V h =>
      have hs : conjugation U=U ∧ conjugation V=V := Point.some.inj hP
      have hUi : U.im=0 := by
        have hh:=congrArg QuadraticAlgebra.im hs.1
        simp [conjugation] at hh
        linarith
      have hVi : V.im=0 := by
        have hh:=congrArg QuadraticAlgebra.im hs.2
        simp [conjugation] at hh
        linarith
      have hU : (Algebra.ofId ℚ K) U.re=U := by ext <;> simp [hUi]
      have hV : (Algebra.ofId ℚ K) V.re=V := by ext <;> simp [hVi]
      have hq : E0.toAffine.Nonsingular U.re V.re :=
        (E0.toAffine.baseChange_nonsingular (Algebra.ofId ℚ K).injective _ _).mp
          (by simpa only [hU,hV] using h)
      refine ⟨.some U.re V.re hq,?_⟩
      change Point.some ((Algebra.ofId ℚ K) U.re) ((Algebra.ofId ℚ K) V.re) _ =
        Point.some U V h
      simp only [Point.some.injEq]
      exact ⟨hU,hV⟩
  · rintro ⟨Q,rfl⟩
    exact sigma_embed Q

private def mkPoint (U V : K)
    (h : V^2=U^3+6640150*U^2+5047497487500*U+1053718156603125000) : KPoint :=
  .some U V (equation_iff_nonsingular.mp (by
    apply (equation_iff _ _).mpr
    simpa [E0,WeierstrassCurve.Affine.baseChange,WeierstrassCurve.map] using h))

def xstar : K := ⟨0,1950⟩
def ystar : K := ⟨1123590000,4524000⟩
def tx : K := ⟨196265550/203,0⟩
def ty : K := ⟨0,-712421190000/41209⟩

def Pstar : KPoint := mkPoint xstar ystar (by
  ext <;> norm_num [xstar,ystar,pow_succ,QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.im_ofNat])

def T : KPoint := mkPoint tx ty (by
  ext <;> norm_num [tx,ty,pow_succ,QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.im_ofNat])

private theorem xstar_ne : xstar≠conjugation xstar := by
  intro h
  have hh:=congrArg QuadraticAlgebra.im h
  norm_num [xstar,conjugation] at hh

/-- The exact nonzero Galois difference of the original base point. -/
theorem Pstar_difference : Pstar-sigma Pstar=T := by
  simp only [Pstar,T,sigma,mkPoint,sub_eq_add_neg,Point.map_some,Point.neg_some]
  rw [Point.add_of_X_ne xstar_ne]
  simp only [Point.some.injEq]
  constructor <;> ext <;>
    norm_num [addX,addY,negY,slope_of_X_ne xstar_ne,E0,
      WeierstrassCurve.Affine.baseChange,WeierstrassCurve.map,
      xstar,ystar,tx,ty,conjugation,pow_succ,
      QuadraticAlgebra.div_def,QuadraticAlgebra.inv_def,QuadraticAlgebra.norm_def,
      QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

/-- Equality of the complete Galois-difference fiber and the full translated
rational group. It is not restricted to polynomial image controls. -/
theorem full_rational_coset (P : KPoint) :
    P-sigma P=T ↔ ∃ Q : QPoint, P=Pstar+embed Q := by
  constructor
  · intro hP
    have hfixed : sigma (P-Pstar)=P-Pstar := by
      rw [map_sub]
      calc
        sigma P-sigma Pstar = (P-(P-sigma P))-(Pstar-(Pstar-sigma Pstar)) := by abel
        _ = P-Pstar := by rw [hP,Pstar_difference];abel
    obtain ⟨Q,hQ⟩:=(fixed_iff_rational (P-Pstar)).mp hfixed
    exact ⟨Q,by rw [hQ];abel⟩
  · rintro ⟨Q,rfl⟩
    rw [map_add,sigma_embed]
    have hbase:=Pstar_difference
    convert hbase using 1 <;> abel

set_option maxHeartbeats 800000 in
/-- Exact translation identity for the full positive rational quartic,
including both W signs. The rational parameter need not be integral. -/
theorem polynomial_translation (q : PositiveQuarticPoint) :
    fieldPoint q=Pstar-embed (rationalPoint q) := by
  rcases q with ⟨⟨b,W⟩,hbpos,hw⟩
  have hb : b≠0:=hbpos.ne'
  let U : K:=⟨rationalU b W,0⟩
  let V : K:=⟨rationalV b W,0⟩
  let m : K:=⟨-(W+975)/b,-b⟩
  let Eaff:=E0.toAffine.baseChange K
  have hx : xstar≠U := by
    intro he
    have hi:=congrArg QuadraticAlgebra.im he
    norm_num [xstar,U] at hi
  have hs : Eaff.slope xstar U ystar (Eaff.negY U V)=m := by
    rw [slope_of_X_ne hx]
    apply (div_eq_iff (sub_ne_zero.mpr hx)).2
    ext <;>
      simp [Eaff,E0,WeierstrassCurve.Affine.baseChange,WeierstrassCurve.map,
        negY,xstar,ystar,U,V,m,
        QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat,pow_succ]
    all_goals (try simp only [rationalU,rationalV,modelL])
    all_goals field_simp [hb] <;> ring
  have hX : Eaff.addX xstar U m=polynomialU b W := by
    ext <;>
      simp [Eaff,E0,WeierstrassCurve.Affine.baseChange,WeierstrassCurve.map,
        addX,xstar,U,m,polynomialU,
        QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat,pow_succ]
    all_goals (try simp only [rationalU,rationalV,modelL])
    all_goals field_simp [hb]
    all_goals dsimp [f] at hw
    all_goals nlinarith [hw]
  have hY : Eaff.addY xstar U ystar m=polynomialV b W := by
    dsimp only [addY,negAddY]
    rw [hX]
    ext <;>
      simp [Eaff,E0,WeierstrassCurve.Affine.baseChange,WeierstrassCurve.map,
        negY,xstar,ystar,U,m,polynomialU,polynomialV,
        QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat,pow_succ]
    all_goals (try simp only [rationalU,rationalV,modelL])
    all_goals field_simp [hb]
    all_goals dsimp [f] at hw
    all_goals nlinarith [hw]
  have hRQ : E0.toAffine.Nonsingular (rationalU b W) (rationalV b W) := by
    apply equation_iff_nonsingular.mp
    apply (equation_iff _ _).mpr
    simpa [E0] using rational_cubic b W hb hw
  have hR : Eaff.Nonsingular U V :=
    (E0.toAffine.baseChange_nonsingular (Algebra.ofId ℚ K).injective _ _).mpr hRQ
  have hP : Eaff.Nonsingular (polynomialU b W) (polynomialV b W) := by
    apply equation_iff_nonsingular.mp
    apply (equation_iff _ _).mpr
    simpa [Eaff,E0,WeierstrassCurve.Affine.baseChange,WeierstrassCurve.map]
      using polynomial_cubic b W hw
  have heq : Pstar-Point.some U V hR =
      Point.some (polynomialU b W) (polynomialV b W) hP := by
    unfold Pstar mkPoint
    rw [sub_eq_add_neg,Point.neg_some,Point.add_of_X_ne hx]
    simp only [Point.some.injEq]
    rw [hs]
    exact ⟨hX,hY⟩
  exact heq.symm

/-- The actual image has the original nonzero Galois difference. -/
theorem polynomial_galois_difference (q : PositiveQuarticPoint) :
    fieldPoint q-sigma (fieldPoint q)=T := by
  apply (full_rational_coset (fieldPoint q)).2
  refine ⟨-rationalPoint q,?_⟩
  rw [map_neg,←sub_eq_add_neg]
  exact polynomial_translation q


end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6GaloisCoset
