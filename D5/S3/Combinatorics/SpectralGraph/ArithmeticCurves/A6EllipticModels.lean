/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6EllipticModels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6EllipticModels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual a6 elliptic models and exact affine integrality recovery -/

import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.RootTwoTailCurve
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! Sources: complete supplied S.a6/S.affine/S.coset notes at PR9
6d491f77b35dec808fc777b69939c56cdae5dc02, blobs
 ddd0b661130caffadd5e43722cc42f2d98356a73,
 dfdfbfc801a97b38858985bfba1301226e29b21a,
 8f84b430e880aeef5747688e95608220bbfc96a2.
Original Nikandish graph/problem and Ma/Nikandish/Zhang proof attribution
are retained. All formal proof engineering is independent. The field
map preserves affine integrality; the rational chart generally does not.
Both W signs, all exceptional points, translated integrality and the
original c-divisibility/positivity/repeated-minimum filters remain required.
No elliptic rank, saturated basis, complete integral-point list, LLL
certificate or complete a6 classification is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6EllipticModels
open D5.S3.Combinatorics.SpectralGraph

private theorem radicand_nonsquare : ¬ IsSquare (43645:ℚ) := by
  rw [show (43645:ℚ)=((43645:ℕ):ℚ) by norm_num,Rat.isSquare_natCast_iff]
  rintro ⟨n,hn⟩
  have hlo : 209≤n := by
    by_contra h
    have hh : n≤208 := by omega
    have hs:=Nat.mul_le_mul hh hh
    nlinarith
  have hs:=Nat.mul_le_mul hlo hlo
  nlinarith

private instance : Fact (¬ IsSquare (43645:ℚ)) := ⟨radicand_nonsquare⟩

/-- The actual quadratic field Q(sqrt43645), with unique rational coordinates. -/
abbrev K := QuadraticAlgebra ℚ 43645 0

def sqrtD : K := QuadraticAlgebra.omega

theorem sqrtD_sq : sqrtD^2=(43645:K) := by
  ext <;> norm_num [sqrtD,pow_two,QuadraticAlgebra.omega]

def E : WeierstrassCurve ℚ := ⟨0,0,0,-78162568812,8433576786332241⟩
def E0 : WeierstrassCurve ℚ := ⟨0,6640150,0,5047497487500,1053718156603125000⟩

theorem E_discriminant : E.Δ= -164468670344965775252034431406000 := by
  norm_num [E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]

theorem E0_discriminant : E0.Δ= -309476819336418859764366000000000000000 := by
  norm_num [E0,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]

instance : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by rw [E_discriminant];norm_num)⟩
instance : E0.IsElliptic := ⟨isUnit_iff_ne_zero.mpr (by rw [E0_discriminant];norm_num)⟩

instance : (E0.baseChange K).IsElliptic := by
  change (E0.map (algebraMap ℚ K)).IsElliptic
  infer_instance

/-- All positive rational points on the original affine quartic. -/
def f {R : Type*} [CommRing R] (b : R) : R :=
  43645*b^4+1152400*b^3+6640150*b^2+4524000*b+950625

def aCoefficient {R : Type*} [CommRing R] (b : R) : R := -13*b^2+420*b-35

def squareCoordinate {R : Type*} [CommRing R] (b c : R) : R :=
  aCoefficient b*c+210*b^2+2650*b+950

def PositiveQuarticPoint := {q : ℚ × ℚ // 0<q.1 ∧ q.2^2=f q.1}

theorem square_completion {R : Type*} [CommRing R] (b c : R) :
    squareCoordinate b c^2-f b=aCoefficient b*RootTwoTailCurve.equation 6 b c := by
  unfold squareCoordinate aCoefficient f RootTwoTailCurve.equation
    RootTwoTailCurve.A RootTwoTailCurve.B RootTwoTailCurve.C₀
  ring

theorem a_coefficient_nonzero (b : ℚ) : aCoefficient b≠0 := by
  intro h
  apply radicand_nonsquare
  refine ⟨13*b-210,?_⟩
  dsimp [aCoefficient] at h
  linear_combination 13*h

theorem f_positive (b : ℚ) (hb : 0<b) : 0<f b := by unfold f;positivity

theorem quartic_W_nonzero (q : PositiveQuarticPoint) : q.1.2≠0 := by
  intro h
  have hf:=f_positive q.1.1 q.2.1
  have hq:=q.2.2
  rw [h] at hq
  norm_num at hq
  linarith

/-- Exact polynomial coordinates in the actual quadratic field. -/
def polynomialU (b W : ℚ) : K := ⟨2*43645*b^2+1152400*b,2*W⟩
def polynomialV (b W : ℚ) : K :=
  ⟨(4*43645*b+1152400)*W,4*43645*b^3+3*1152400*b^2+2*6640150*b+4524000⟩

theorem polynomial_cubic (b W : ℚ) (hw : W^2=f b) :
    polynomialV b W^2=polynomialU b W^3+6640150*polynomialU b W^2+
      5047497487500*polynomialU b W+1053718156603125000 := by
  ext
  · simp [polynomialU,polynomialV,pow_succ,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
    dsimp [f] at hw
    linear_combination (-8*43645^2*b^2-4*43645*b*1152400-4*43645*6640150+1152400^2)*hw
  · simp [polynomialU,polynomialV,pow_succ,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
    dsimp [f] at hw
    linear_combination (-8*W*43645)*hw

/-- A genuine nonsingular elliptic-curve point, not a scalar cubic proxy. -/
def fieldPoint (q : PositiveQuarticPoint) : (E0.baseChange K).toAffine.Point :=
  .some (polynomialU q.1.1 q.1.2) (polynomialV q.1.1 q.1.2)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      apply (WeierstrassCurve.Affine.equation_iff _ _).mpr
      simpa [E0,WeierstrassCurve.baseChange,WeierstrassCurve.map] using
        polynomial_cubic q.1.1 q.1.2 q.2.2))

/-- The coefficient inverse uses no selection of the sign of W. -/
def recoverW (U : K) : ℚ := U.im/2
def recoverB (U V : K) : ℚ := (2*V.re-1152400*U.im)/(4*43645*U.im)

theorem recover_polynomial_W (b W : ℚ) : recoverW (polynomialU b W)=W := by
  dsimp [recoverW,polynomialU]
  ring

theorem recover_polynomial_B (b W : ℚ) (hW : W≠0) :
    recoverB (polynomialU b W) (polynomialV b W)=b := by
  dsimp [recoverB,polynomialU,polynomialV]
  field_simp
  <;>ring

theorem polynomial_map_injective : Function.Injective
    (fun q : PositiveQuarticPoint => (polynomialU q.1.1 q.1.2,polynomialV q.1.1 q.1.2)) := by
  intro p q hpq
  obtain ⟨hU,hV⟩:=Prod.mk.inj hpq
  have hW:=congrArg recoverW hU
  rw [recover_polynomial_W,recover_polynomial_W] at hW
  have hb:=congrArg (fun z : K × K => recoverB z.1 z.2) hpq
  rw [recover_polynomial_B _ _ (quartic_W_nonzero p),
    recover_polynomial_B _ _ (quartic_W_nonzero q)] at hb
  exact Subtype.ext (Prod.ext hb hW)


/-- Integrality is in the entire integral closure, rather than in the
proper order Z[sqrtD]. Half-integral coordinates are never excluded. -/
abbrev fullIntegers := integralClosure ℤ K

theorem sqrtD_integral : IsIntegral ℤ sqrtD := by
  apply IsIntegral.of_pow (n:=2) (by norm_num)
  rw [sqrtD_sq]
  exact isIntegral_algebraMap

/-- Full exact coefficient reconstruction in the actual quadratic field.
All four identities are checked; neither W sign is selected. -/
theorem coefficient_reconstruction (U V : K) (b W : ℚ) :
    (U=polynomialU b W ∧ V=polynomialV b W) ↔
      U.re=2*43645*b^2+1152400*b ∧ U.im=2*W ∧
      V.re=(4*43645*b+1152400)*W ∧
      V.im=4*43645*b^3+3*1152400*b^2+2*6640150*b+4524000 := by
  simp only [QuadraticAlgebra.ext_iff,polynomialU,polynomialV]
  tauto

theorem polynomial_coordinates_integral (b W : ℤ) :
    IsIntegral ℤ (polynomialU (b:ℚ) (W:ℚ)) ∧
      IsIntegral ℤ (polynomialV (b:ℚ) (W:ℚ)) := by
  have hcoords := (coefficient_reconstruction
    ((2*43645*(b:K)^2+1152400*(b:K))+2*(W:K)*sqrtD)
    ((4*43645*(b:K)+1152400)*(W:K)+
      (4*43645*(b:K)^3+3*1152400*(b:K)^2+2*6640150*(b:K)+4524000)*sqrtD)
    (b:ℚ) (W:ℚ)).mpr (by
      simp [sqrtD,pow_succ,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
      <;> ring)
  rw [←hcoords.1,←hcoords.2]
  have hb : IsIntegral ℤ (b:K) := isIntegral_algebraMap
  have hW : IsIntegral ℤ (W:K) := isIntegral_algebraMap
  constructor
  · exact (((isIntegral_algebraMap.mul isIntegral_algebraMap).mul (hb.pow 2)).add
      (isIntegral_algebraMap.mul hb)).add
        ((isIntegral_algebraMap.mul hW).mul sqrtD_integral)
  · exact (((isIntegral_algebraMap.mul isIntegral_algebraMap).mul hb).add
      isIntegral_algebraMap |>.mul hW).add
      (((((isIntegral_algebraMap.mul isIntegral_algebraMap).mul (hb.pow 3)).add
          ((isIntegral_algebraMap.mul isIntegral_algebraMap).mul (hb.pow 2))).add
          ((isIntegral_algebraMap.mul isIntegral_algebraMap).mul hb)).add
          isIntegral_algebraMap |>.mul sqrtD_integral)

/-- The original integer-tail filter is exactly equivalent to the
root-two equation; it is not a graph-spectrum sufficiency criterion. -/
theorem integer_tail_filter (b W : ℤ) (hw : W^2=f b) :
    (∃ c : ℤ, 0<c ∧ RootTwoTailCurve.equation 6 b c=0 ∧
      W=squareCoordinate b c) ↔
      ∃ c : ℤ, 0<c ∧ W-210*b^2-2650*b-950=aCoefficient b*c := by
  constructor
  · rintro ⟨c,hc,hz,rfl⟩
    exact ⟨c,hc,by unfold squareCoordinate;ring⟩
  · rintro ⟨c,hc,hc'⟩
    have he : W=squareCoordinate b c := by unfold squareCoordinate;linarith
    have h:=square_completion b c
    rw [←he,hw,sub_self] at h
    have hA : aCoefficient b≠0 := by
      intro hA
      have hQ : aCoefficient (b:ℚ)=0 := by
        dsimp [aCoefficient] at hA ⊢
        exact_mod_cast hA
      exact a_coefficient_nonzero _ hQ
    exact ⟨c,hc,(mul_eq_zero.mp h.symm).resolve_left hA,he⟩

/-- Integral quartic points have the necessary factor five, with no
exponent bound or enumeration premise. -/
theorem five_dvd_W (b W : ℤ) (hw : W^2=f b) : 5∣W := by
  have hs : (5:ℤ)∣W^2 := by
    rw [hw]
    unfold f
    omega
  exact (by norm_num : Prime (5:ℤ)).dvd_of_dvd_pow hs

/-- Injectivity is retained on actual elliptic-curve points. -/
theorem fieldPoint_injective : Function.Injective fieldPoint := by
  intro p q h
  apply polynomial_map_injective
  exact Prod.ext (WeierstrassCurve.Affine.Point.some.inj h).1
    (WeierstrassCurve.Affine.Point.some.inj h).2

/-- Every original positive integer root-two pair defines a full positive
quartic point. The defining equation is proved by square completion. -/
def integerQuarticPoint (b c : ℤ) (hb : 0<b)
    (hz : RootTwoTailCurve.equation 6 b c=0) : PositiveQuarticPoint := by
  refine ⟨((b:ℚ),((squareCoordinate b c : ℤ):ℚ)),by change (0:ℚ)<(b:ℚ);exact_mod_cast hb,?_⟩
  have h:=square_completion b c
  rw [hz,mul_zero] at h
  have he:=sub_eq_zero.mp h
  dsimp [squareCoordinate,aCoefficient,f] at he ⊢
  exact_mod_cast he

/-- The actual point coordinates belong to the full integral closure. -/
theorem integer_image_integral (b c : ℤ) :
    IsIntegral ℤ (polynomialU (b:ℚ) ((squareCoordinate b c : ℤ):ℚ)) ∧
      IsIntegral ℤ (polynomialV (b:ℚ) ((squareCoordinate b c : ℤ):ℚ)) :=
  polynomial_coordinates_integral b (squareCoordinate b c)

def recoverC (b W : ℚ) : ℚ :=
  (W-210*b^2-2650*b-950)/aCoefficient b

theorem recoverC_square (b W : ℚ) : squareCoordinate b (recoverC b W)=W := by
  dsimp [squareCoordinate,recoverC]
  field_simp [a_coefficient_nonzero]
  <;>ring

/-- Exact rational inverse at every b, with no vanished A fiber. -/
theorem recovered_tail_equation (b W : ℚ) :
    RootTwoTailCurve.equation 6 b (recoverC b W)=0 ↔ W^2=f b := by
  have h:=square_completion b (recoverC b W)
  rw [recoverC_square] at h
  constructor
  · intro hz
    rw [hz,mul_zero] at h
    exact sub_eq_zero.mp h
  · intro hw
    rw [hw,sub_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (a_coefficient_nonzero b)


/-- Rational chart on every nonzero affine quartic fiber, with both W signs. -/
def rationalU (b W : ℚ) : ℚ := (1950*(W+975)+4524000*b)/b^2

def modelL (U : ℚ) : ℚ := U^2-3802500*43645

def modelQ (U b : ℚ) : ℚ :=
  modelL U*b^2-(9048000*U+3802500*1152400)*b+
    4524000^2-3802500*U-3802500*6640150

def rationalV (b W : ℚ) : ℚ :=
  (modelL (rationalU b W)*b-4524000*rationalU b W-1901250*1152400)/1950

theorem rational_quadratic (b W : ℚ) (hb : b≠0) (hw : W^2=f b) :
    modelQ (rationalU b W) b=0 := by
  have he : b^2*modelQ (rationalU b W) b=3802500*(W^2-f b) := by
    dsimp [modelQ,modelL,rationalU,f]
    field_simp [hb]
    <;>ring
  rw [hw,sub_self,mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hb)

private theorem complete_square (U b : ℚ) :
    ((modelL U*b-4524000*U-1901250*1152400)/1950)^2-
      (U^3+6640150*U^2+5047497487500*U+1053718156603125000)=
      modelL U*modelQ U b/3802500 := by
  dsimp [modelL,modelQ]
  ring

theorem rational_cubic (b W : ℚ) (hb : b≠0) (hw : W^2=f b) :
    rationalV b W^2=rationalU b W^3+6640150*rationalU b W^2+
      5047497487500*rationalU b W+1053718156603125000 := by
  have h:=complete_square (rationalU b W) b
  rw [rational_quadratic b W hb hw,mul_zero,zero_div] at h
  exact sub_eq_zero.mp h

/-- The actual nonsingular rational elliptic point of the full quartic chart. -/
def rationalPoint (q : PositiveQuarticPoint) : E0.toAffine.Point :=
  .some (rationalU q.1.1 q.1.2) (rationalV q.1.1 q.1.2)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      apply (WeierstrassCurve.Affine.equation_iff _ _).mpr
      simpa [E0] using rational_cubic q.1.1 q.1.2 q.2.1.ne' q.2.2))

/-- No rational finite elliptic point is lost at the inverse denominator. -/
theorem modelL_nonzero (U : ℚ) : modelL U≠0 := by
  intro h
  apply radicand_nonsquare
  refine ⟨U/1950,?_⟩
  dsimp [modelL] at h
  linear_combination -h/3802500

def inverseB (U V : ℚ) : ℚ :=
  (1950*V+4524000*U+1901250*1152400)/modelL U

def inverseW (U V : ℚ) : ℚ :=
  (U*inverseB U V^2-4524000*inverseB U V)/1950-975

theorem inverse_forward_B (b W : ℚ) (hb : b≠0) :
    inverseB (rationalU b W) (rationalV b W)=b := by
  dsimp [inverseB,rationalV]
  field_simp [modelL_nonzero]
  <;>ring

theorem inverse_forward_W (b W : ℚ) (hb : b≠0) :
    inverseW (rationalU b W) (rationalV b W)=W := by
  dsimp only [inverseW]
  rw [inverse_forward_B b W hb]
  dsimp [rationalU]
  field_simp [hb]
  <;>ring

theorem inverse_cubic_quadratic (U V : ℚ)
    (hcurve : V^2=U^3+6640150*U^2+5047497487500*U+1053718156603125000) :
    modelQ U (inverseB U V)=0 := by
  have hV : (modelL U*inverseB U V-4524000*U-1901250*1152400)/1950=V := by
    dsimp [inverseB]
    field_simp [modelL_nonzero]
    <;>ring
  have h:=complete_square U (inverseB U V)
  rw [hV,hcurve,sub_self] at h
  have hz : modelL U*modelQ U (inverseB U V)=0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left (modelL_nonzero U)

/-- Every finite rational cubic point has an affine quartic inverse,
including the exceptional zero-b fiber. -/
theorem inverse_quartic (U V : ℚ)
    (hcurve : V^2=U^3+6640150*U^2+5047497487500*U+1053718156603125000) :
    inverseW U V^2=f (inverseB U V) := by
  have he : 3802500*(inverseW U V^2-f (inverseB U V))=
      inverseB U V^2*modelQ U (inverseB U V) := by
    dsimp only [inverseW]
    dsimp [f,modelQ,modelL]
    ring
  rw [inverse_cubic_quadratic U V hcurve,mul_zero] at he
  linarith

theorem forward_inverse_U (U V : ℚ) (hb : inverseB U V≠0) :
    rationalU (inverseB U V) (inverseW U V)=U := by
  dsimp [rationalU,inverseW]
  field_simp [hb]
  <;>ring

theorem forward_inverse_V (U V : ℚ) (hb : inverseB U V≠0) :
    rationalV (inverseB U V) (inverseW U V)=V := by
  dsimp only [rationalV]
  rw [forward_inverse_U U V hb]
  dsimp [inverseB]
  field_simp [modelL_nonzero]
  <;>ring

/-- The unique rational finite zero-b inverse is the original P0. -/
theorem inverse_zero_iff (U V : ℚ)
    (hcurve : V^2=U^3+6640150*U^2+5047497487500*U+1053718156603125000) :
    inverseB U V=0 ↔ U= -1257750 ∧ V=1794390000 := by
  constructor
  · intro hb
    have h:=inverse_cubic_quadratic U V hcurve
    rw [hb] at h
    dsimp [modelQ] at h
    have hU : U= -1257750 := by linarith
    have hN : 1950*V+4524000*U+1901250*1152400=0 := by
      exact (div_eq_zero_iff.mp hb).resolve_right (modelL_nonzero U)
    exact ⟨hU,by rw [hU] at hN;linarith⟩
  · rintro ⟨rfl,rfl⟩
    norm_num [inverseB,modelL]

theorem quartic_zero_fibers (W : ℚ) : W^2=f 0 ↔ W=975 ∨ W= -975 := by
  norm_num [f]
  constructor
  · intro h
    have he : (W-975)*(W+975)=0 := by nlinarith
    rcases mul_eq_zero.mp he with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Rational scaling is an exact equivalence of both nonsingular models. -/
theorem short_model_scaling (U V : ℚ) :
    V^2=U^3+6640150*U^2+5047497487500*U+1053718156603125000 ↔
      (27*V/1000)^2=((9*U+3*6640150)/100)^3-
        78162568812*((9*U+3*6640150)/100)+8433576786332241 := by
  constructor <;> intro h <;> nlinarith [h]

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6EllipticModels
