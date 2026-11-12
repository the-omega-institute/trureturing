/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6ModelEquivalences
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6ModelEquivalences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual elliptic point-group scaling and original model transfers -/
import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6DyadicInfiniteOrder
import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6TorsionArithmetic
/-! Source: S.nontorsion and S.torsion, original Ma/Nikandish/Zhang
PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02, blobs
01edb67a7e6753c17ecae77e581d4957fe6b94cc and
2bb42a5280cb3ea4ebe596259d4ffbbb1fd37588.
The generic scaling proof is task-local engineering of the received
actual elliptic model isomorphisms. No exact rank/basis is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6ModelEquivalences
open WeierstrassCurve.Affine
private def model {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c : F) : WeierstrassCurve F := ⟨0,a,0,b,c⟩
private def scaled {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r : F) : WeierstrassCurve F :=
  model (u^2*a-3*r) (u^4*b-2*u^2*a*r+3*r^2)
    (u^6*c-u^4*b*r+u^2*a*r^2-r^3)

private theorem scaled_delta {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r : F) :
    (scaled a b c u r).Δ=u^12*(model a b c).Δ := by
  simp only [scaled,model,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

private theorem scaled_elliptic {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r : F)
    [h : (model a b c).IsElliptic] (hu : u≠0) : (scaled a b c u r).IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  rw [scaled_delta]
  exact mul_ne_zero (pow_ne_zero _ hu) (isUnit_iff_ne_zero.mp h.isUnit)

private theorem scaled_equation {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r x y : F)
    (h : (model a b c).toAffine.Equation x y) :
    (scaled a b c u r).toAffine.Equation (u^2*x+r) (u^3*y) := by
  rw [equation_iff] at h ⊢
  simp only [model,scaled] at h ⊢
  linear_combination u^6*h

private def scalePoint {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r : F)
    [(model a b c).IsElliptic] (hu : u≠0) :
    (model a b c).toAffine.Point → (scaled a b c u r).toAffine.Point
  | .zero => .zero
  | .some x y h => by
      letI := scaled_elliptic a b c u r hu
      exact .mk (scaled_equation a b c u r x y h.1)

private theorem scaled_negY {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r x y : F) :
    (scaled a b c u r).toAffine.negY (u^2*x+r) (u^3*y)=
      u^3*(model a b c).toAffine.negY x y := by
  simp only [scaled,model,negY]
  ring

private theorem scaled_slope {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r x z y w : F)
    (hu : u≠0) :
    (scaled a b c u r).toAffine.slope (u^2*x+r) (u^2*z+r) (u^3*y) (u^3*w)=
      u*(model a b c).toAffine.slope x z y w := by
  have hu2 : u^2≠0:=pow_ne_zero _ hu
  have hu3 : u^3≠0:=pow_ne_zero _ hu
  by_cases hx : x=z
  · subst z
    by_cases hy : y=(model a b c).toAffine.negY x w
    · have he : u^3*y=(scaled a b c u r).toAffine.negY (u^2*x+r) (u^3*w) := by
        rw [scaled_negY]
        exact congrArg (fun t=>u^3*t) hy
      rw [slope_of_Y_eq rfl he,slope_of_Y_eq rfl hy,mul_zero]
    · have he : u^3*y≠(scaled a b c u r).toAffine.negY (u^2*x+r) (u^3*w) := by
        rw [scaled_negY]
        exact fun h=>hy (mul_left_cancel₀ hu3 h)
      rw [slope_of_Y_ne rfl he,slope_of_Y_ne rfl hy]
      simp only [scaled,model,negY]
      by_cases hy0 : y=0
      · simp [hy0]
      · field_simp [hy0,hu]
        <;> ring
  · have he : u^2*x+r≠u^2*z+r := by
      simpa [hu2] using hx
    rw [slope_of_X_ne he,slope_of_X_ne hx]
    field_simp
    <;> ring

private theorem scalePoint_add {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r : F)
    [(model a b c).IsElliptic] (hu : u≠0)
    (P Q : (model a b c).toAffine.Point) :
    scalePoint a b c u r hu (P+Q)=scalePoint a b c u r hu P+scalePoint a b c u r hu Q := by
  cases P with
  | zero => change scalePoint a b c u r hu (0+Q)=0+_;simp [scalePoint]
  | some x y h =>
    cases Q with
    | zero =>
      change scalePoint a b c u r hu (Point.some x y h+0)=_+0
      simp [scalePoint]
    | some z w k =>
      have hu2 : u^2≠0:=pow_ne_zero _ hu
      have hu3 : u^3≠0:=pow_ne_zero _ hu
      by_cases hi : x=z ∧ y=(model a b c).toAffine.negY z w
      · have ht : u^2*x+r=u^2*z+r ∧
            u^3*y=(scaled a b c u r).toAffine.negY (u^2*z+r) (u^3*w) := by
          constructor
          · rw [hi.1]
          · rw [scaled_negY]
            exact congrArg (fun t=>u^3*t) hi.2
        rw [Point.add_of_Y_eq hi.1 hi.2]
        simp only [scalePoint,Point.mk]
        rw [Point.add_of_Y_eq ht.1 ht.2]
        rfl
      · have ht : ¬(u^2*x+r=u^2*z+r ∧
            u^3*y=(scaled a b c u r).toAffine.negY (u^2*z+r) (u^3*w)) := by
          rintro ⟨hx,hy⟩
          rw [scaled_negY] at hy
          exact hi ⟨mul_left_cancel₀ hu2 (add_right_cancel hx),mul_left_cancel₀ hu3 hy⟩
        rw [Point.add_some hi]
        simp only [scalePoint,Point.mk]
        rw [Point.add_some ht]
        simp only [Point.some.injEq]
        rw [scaled_slope a b c u r x z y w hu]
        constructor <;> simp only [addX,addY,negAddY,negY,scaled,model] <;> ring

private def scaleHom {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r : F)
    [(model a b c).IsElliptic] (hu : u≠0) :
    (model a b c).toAffine.Point →+ (scaled a b c u r).toAffine.Point where
  toFun := scalePoint a b c u r hu
  map_zero' := rfl
  map_add' := scalePoint_add a b c u r hu

private theorem scalePoint_injective {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r : F)
    [(model a b c).IsElliptic] (hu : u≠0) :
    Function.Injective (scalePoint a b c u r hu) := by
  intro P Q he
  cases P with
  | zero => cases Q <;> simp_all [scalePoint,Point.mk]
  | some x y h =>
    cases Q with
    | zero => simp_all [scalePoint,Point.mk]
    | some z w k =>
      simp only [scalePoint,Point.mk,Point.some.injEq] at he ⊢
      exact ⟨mul_left_cancel₀ (pow_ne_zero 2 hu) (add_right_cancel he.1),
        mul_left_cancel₀ (pow_ne_zero 3 hu) he.2⟩

private theorem inverse_equation {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r X Y : F)
    (hu : u≠0) (h : (scaled a b c u r).toAffine.Equation X Y) :
    (model a b c).toAffine.Equation ((X-r)/u^2) (Y/u^3) := by
  rw [equation_iff] at h ⊢
  simp only [scaled,model] at h ⊢
  field_simp
  <;> linear_combination h

private theorem scalePoint_surjective {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r : F)
    [(model a b c).IsElliptic] (hu : u≠0) :
    Function.Surjective (scalePoint a b c u r hu) := by
  intro Q
  cases Q with
  | zero => exact ⟨0,rfl⟩
  | some X Y h =>
    refine ⟨.mk (inverse_equation a b c u r X Y hu h.1),?_⟩
    simp only [Point.mk,scalePoint,Point.some.injEq]
    constructor <;> field_simp <;> ring

private def scaleEquiv {F : Type*} [Field F] [CharZero F] [DecidableEq F] (a b c u r : F)
    [(model a b c).IsElliptic] (hu : u≠0) :
    (model a b c).toAffine.Point ≃+ (scaled a b c u r).toAffine.Point :=
  AddEquiv.ofBijective (scaleHom a b c u r hu)
    ⟨scalePoint_injective a b c u r hu,scalePoint_surjective a b c u r hu⟩

@[simp] private theorem scaleEquiv_apply {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (a b c u r : F) [(model a b c).IsElliptic] (hu : u≠0)
    (P : (model a b c).toAffine.Point) :
    scaleEquiv a b c u r hu P=scalePoint a b c u r hu P := rfl

private def pointCongr {F : Type*} [Field F] [DecidableEq F]
    {C D : WeierstrassCurve F} (h : C=D) : C.toAffine.Point ≃+ D.toAffine.Point := by
  subst D
  exact AddEquiv.refl _

@[simp] private theorem pointCongr_some {F : Type*} [Field F] [DecidableEq F]
    {C D : WeierstrassCurve F} (he : C=D) {x y : F} (h : C.toAffine.Nonsingular x y) :
    pointCongr he (.some x y h)=.some x y (by simpa only [←he] using h) := by
  subst D
  rfl

open A6EllipticModels A6GaloisCoset A6DyadicInfiniteOrder A6TorsionArithmetic

private def shortModelEquiv (F : Type*) [Field F] [CharZero F] [DecidableEq F] :
    (model (6640150:F) 5047497487500 1053718156603125000).toAffine.Point ≃+
      (model (0:F) (-78162568812) 8433576786332241).toAffine.Point := by
  have hsrc : (model (6640150:F) 5047497487500 1053718156603125000).IsElliptic := by
    constructor
    apply isUnit_iff_ne_zero.mpr
    norm_num [model,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  letI := hsrc
  have he : scaled (6640150:F) 5047497487500 1053718156603125000 (3/10) (19920450/100)=
      model (0:F) (-78162568812) 8433576786332241 := by
    ext <;> norm_num [scaled,model]
  exact (scaleEquiv (6640150:F) 5047497487500 1053718156603125000
    (3/10) (19920450/100) (by norm_num)).trans (pointCongr he)

/-- The full actual rational point-group isomorphism to the original short E. -/
def shortQEquiv : QPoint ≃+ E.toAffine.Point := by
  have hs : E0=model (6640150:ℚ) 5047497487500 1053718156603125000 := by
    ext <;> norm_num [E0,model]
  have ht : model (0:ℚ) (-78162568812) 8433576786332241=E := by
    ext <;> norm_num [E,model]
  exact (pointCongr hs).trans ((shortModelEquiv ℚ).trans (pointCongr ht))

/-- The full actual quadratic-field point-group isomorphism to the original short E. -/
def shortKEquiv : KPoint ≃+ (E.baseChange K).toAffine.Point := by
  have hs : E0.baseChange K=model (6640150:K) 5047497487500 1053718156603125000 := by
    ext <;> norm_num [E0,model,WeierstrassCurve.baseChange,WeierstrassCurve.map,
      QuadraticAlgebra.algebraMap_eq]
  have ht : model (0:K) (-78162568812) 8433576786332241=E.baseChange K := by
    ext <;> norm_num [E,model,WeierstrassCurve.baseChange,WeierstrassCurve.map,
      QuadraticAlgebra.algebraMap_eq]
  exact (pointCongr hs).trans ((shortModelEquiv K).trans (pointCongr ht))

/-- Infinite additive order on the original actual short model E(Q). -/
theorem short_S_infinite_order : ¬IsOfFinAddOrder (shortQEquiv S) := by
  intro h
  obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp h
  apply S_infinite_order
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  exact ⟨n,hn,shortQEquiv.injective (by simpa only [map_nsmul,map_zero] using he)⟩

/-- The received lower bound, on the original actual rational short model. -/
theorem short_rational_rank_lower : (1:Cardinal)≤Module.rank ℤ E.toAffine.Point := by
  rw [←shortQEquiv.toIntLinearEquiv.rank_eq]
  exact rational_group_rank_lower

/-- The received lower bound, on the original actual quadratic short model. -/
theorem short_quadratic_rank_lower : (2:Cardinal)≤Module.rank ℤ (E.baseChange K).toAffine.Point := by
  rw [←shortKEquiv.toIntLinearEquiv.rank_eq]
  exact quadratic_group_rank_lower

private theorem sqrtD_ne_zero : sqrtD≠0 := by
  intro he
  have hs:=sqrtD_sq
  rw [he] at hs
  norm_num at hs

private def twistModelEquiv :
    (model (0:K) (-78162568812) 8433576786332241).toAffine.Point ≃+
      (model (0:K) (43645^2*(-78162568812)) (43645^3*8433576786332241)).toAffine.Point := by
  have hsrc : (model (0:K) (-78162568812) 8433576786332241).IsElliptic := by
    constructor
    apply isUnit_iff_ne_zero.mpr
    norm_num [model,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  letI := hsrc
  have h4 : sqrtD^4=(43645:K)^2 := by rw [show 4=2*2 by decide,pow_mul,sqrtD_sq]
  have h6 : sqrtD^6=(43645:K)^3 := by rw [show 6=2*3 by decide,pow_mul,sqrtD_sq]
  have he : scaled (0:K) (-78162568812) 8433576786332241 sqrtD 0=
      model (0:K) (43645^2*(-78162568812)) (43645^3*8433576786332241) := by
    ext <;> simp [scaled,model,h4,h6]
  exact (scaleEquiv (0:K) (-78162568812) 8433576786332241
    sqrtD 0 sqrtD_ne_zero).trans (pointCongr he)

/-- Full actual K-point group isomorphism from the original curve to its d-twist. -/
def twistKEquiv : (E.baseChange K).toAffine.Point ≃+ (Ed.baseChange K).toAffine.Point := by
  have hs : E.baseChange K=model (0:K) (-78162568812) 8433576786332241 := by
    ext <;> norm_num [E,model,WeierstrassCurve.baseChange,WeierstrassCurve.map,
      QuadraticAlgebra.algebraMap_eq]
  have ht : model (0:K) (43645^2*(-78162568812)) (43645^3*8433576786332241)=
      Ed.baseChange K := by
    ext <;> norm_num [Ed,integerTwist,model,WeierstrassCurve.baseChange,
      WeierstrassCurve.map,QuadraticAlgebra.algebraMap_eq]
  exact (pointCongr hs).trans (twistModelEquiv.trans (pointCongr ht))


instance : Ed.IsElliptic := by
  constructor
  apply isUnit_iff_ne_zero.mpr
  norm_num [Ed,integerTwist,WeierstrassCurve.map,WeierstrassCurve.Δ,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

instance : (E.baseChange K).IsElliptic := by
  change (E.map (algebraMap ℚ K)).IsElliptic
  infer_instance

instance : (Ed.baseChange K).IsElliptic := by
  change (Ed.map (algebraMap ℚ K)).IsElliptic
  infer_instance

/-- Original short-model rational control, not a positive integer graph example. -/
def shortS : E.toAffine.Point := .mk (by
  apply (equation_iff _ _).mpr
  norm_num [E] : E.toAffine.Equation (19517052/121) (6328630035/1331))

/-- Original rational point on the full actual43645 twist. -/
def twistWitness : Ed.toAffine.Point := .mk (by
  apply (equation_iff _ _).mpr
  norm_num [Ed,integerTwist,WeierstrassCurve.map] :
    Ed.toAffine.Equation 12492018795 (-889155076709250))

def embedTwist : Ed.toAffine.Point →+ (Ed.baseChange K).toAffine.Point :=
  Point.baseChange (W':=Ed.toAffine) ℚ K

/-- Both coordinates of the received original S are preserved by the group transfer. -/
theorem short_S_image : shortQEquiv S=shortS := by
  rw [S_received_chart]
  simp only [shortQEquiv,shortModelEquiv,AddEquiv.trans_apply,scaleEquiv_apply,
    rationalPoint,shortS,Point.mk,pointCongr_some,scalePoint,Point.some.injEq]
  constructor <;> norm_num [rationalU,rationalV,modelL]

/-- The received Galois-difference point maps to its exact rational twist witness. -/
theorem twist_T_image : twistKEquiv (shortKEquiv T)=embedTwist twistWitness := by
  change twistKEquiv (shortKEquiv (Point.some tx ty _))=
    Point.some ((Algebra.ofId ℚ K) 12492018795)
      ((Algebra.ofId ℚ K) (-889155076709250)) _
  simp only [twistKEquiv,shortKEquiv,shortModelEquiv,twistModelEquiv,
    AddEquiv.trans_apply,scaleEquiv_apply,pointCongr_some,scalePoint,Point.mk,Point.some.injEq]
  constructor <;> ext <;>
    norm_num [tx,ty,sqrtD,QuadraticAlgebra.algebraMap_eq,pow_succ,
      QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat,QuadraticAlgebra.div_def,
      QuadraticAlgebra.inv_def,QuadraticAlgebra.norm_def]

/-- Infinite order on the actual rational quadratic-twist group. -/
theorem twistWitness_infinite_order : ¬IsOfFinAddOrder twistWitness := by
  intro h
  obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp h
  apply T_infinite_order
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n,hn,?_⟩
  apply shortKEquiv.injective
  apply twistKEquiv.injective
  rw [map_nsmul,map_nsmul,twist_T_image,←map_nsmul,he,map_zero,map_zero,map_zero]

/-- Received rational twist rank lower bound, with no exact rank or saturation claim. -/
theorem twist_rational_rank_lower : (1:Cardinal)≤Module.rank ℤ Ed.toAffine.Point := by
  have hli : LinearIndependent ℤ (fun _ : Fin 1=>twistWitness) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have he : c 0•twistWitness=0 := by simpa [Fin.sum_univ_one] using hc
    have h0 : c 0=0 := by
      by_contra hn
      exact twistWitness_infinite_order (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨c 0,hn,he⟩)
    fin_cases i
    exact h0
  simpa using hli.cardinal_le_rank

/-- Exact coordinate interface on every actual finite K-point of E0. -/
theorem shortK_some (U V : K) (h : (E0.baseChange K).toAffine.Nonsingular U V) :
    ∃ h',shortKEquiv (Point.some U V h)=
      Point.some ((9*U+19920450)/100) (27*V/1000) h' := by
  simp only [shortKEquiv,shortModelEquiv,AddEquiv.trans_apply,scaleEquiv_apply,
    pointCongr_some,scalePoint,Point.mk]
  have hx : (3/10:K)^2*U+19920450/100=(9*U+19920450)/100 := by ring
  have hy : (3/10:K)^3*V=27*V/1000 := by ring
  simp_rw [hx,hy]
  refine ⟨?_,trivial⟩
  apply equation_iff_nonsingular.mp
  apply (equation_iff _ _).mpr
  have hc:=(equation_iff _ _).mp h.1
  norm_num [E0,E,WeierstrassCurve.baseChange,WeierstrassCurve.map,
    QuadraticAlgebra.algebraMap_eq] at hc ⊢
  linear_combination (729/1000000:K)*hc

/-- Exact coordinate interface on every actual finite K-point of the short E. -/
theorem twistK_some (X Y : K) (h : (E.baseChange K).toAffine.Nonsingular X Y) :
    ∃ h',twistKEquiv (Point.some X Y h)=
      Point.some (43645*X) (43645*sqrtD*Y) h' := by
  simp only [twistKEquiv,twistModelEquiv,AddEquiv.trans_apply,scaleEquiv_apply,
    pointCongr_some,scalePoint,Point.mk]
  have hx : sqrtD^2*X+0=43645*X := by rw [sqrtD_sq,add_zero]
  have hy : sqrtD^3*Y=43645*sqrtD*Y := by rw [pow_succ,sqrtD_sq]
  simp_rw [hx,hy]
  refine ⟨?_,trivial⟩
  apply equation_iff_nonsingular.mp
  apply (equation_iff _ _).mpr
  have hc:=(equation_iff _ _).mp h.1
  norm_num [E,Ed,integerTwist,WeierstrassCurve.baseChange,WeierstrassCurve.map,
    QuadraticAlgebra.algebraMap_eq,mul_pow,sqrtD_sq] at hc ⊢
  linear_combination (43645^3:K)*hc

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6ModelEquivalences
