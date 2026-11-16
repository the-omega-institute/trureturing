/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6RationalCurveIsogeny
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6RationalCurveIsogeny
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual rational local-coordinate curve morphisms preserve the Galois obstruction -/
import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6DyadicInfiniteOrder
import Mathlib.RingTheory.MvPolynomial.Homogeneous
/-! Original complete S.nontorsion, blob01edb67a7e6753c17ecae77e581d4957fe6b94cc
at PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02,
Ma/Nikandish/Zhang. The curve map is supplied by a finite rational
homogeneous coordinate atlas on the entire source curve over every
characteristic-zero field, with the actual point-group map and finite
kernel. Conjugation compatibility is derived from those polynomial
charts, not assumed of an arbitrary finite-kernel group homomorphism.
The coordinate-atlas representation and its relation to other intrinsic
scheme isogeny APIs remain an explicit representation boundary. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6RationalCurveIsogeny
open A6EllipticModels A6GaloisCoset A6DyadicInfiniteOrder
open WeierstrassCurve.Affine

/-- Normalized coordinates of every actual projective elliptic point,
including the identity (0:1:0). -/
def coordinates {F : Type} [Field F] {W : WeierstrassCurve.Affine F} :
    W.Point → Fin 3 → F
  | .zero => ![0,1,0]
  | .some x y _ => ![x,y,1]

private theorem coordinates_ext {F : Type} [Field F]
    {W : WeierstrassCurve.Affine F} (P Q : W.Point)
    (v : Fin 3 → F) (a b : F) (ha : a≠0) (hb : b≠0)
    (hP : ∀ j,coordinates P j=a*v j) (hQ : ∀ j,coordinates Q j=b*v j) : P=Q := by
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y h =>
      have hv : v 2=0 := (mul_eq_zero.mp (hP 2).symm).resolve_left ha
      have he:=hQ 2
      simp [coordinates,hv] at he
  | some x y h =>
    cases Q with
    | zero =>
      have hv : v 2=0 := (mul_eq_zero.mp (hQ 2).symm).resolve_left hb
      have he:=hP 2
      simp [coordinates,hv] at he
    | some x' y' h' =>
      have hv : v 2≠0 := by
        intro he
        have hh:=hP 2
        simp [coordinates,he] at hh
      have hab : a=b := mul_right_cancel₀ hv ((hP 2).symm.trans (hQ 2))
      simp only [Point.some.injEq]
      constructor
      · calc
          x=a*v 0 := by simpa [coordinates] using hP 0
          _=b*v 0 := by rw [hab]
          _=x' := by simpa [coordinates] using (hQ 0).symm
      · calc
          y=a*v 1 := by simpa [coordinates] using hP 1
          _=b*v 1 := by rw [hab]
          _=y' := by simpa [coordinates] using (hQ 1).symm

/-- A rational algebraic curve map is described on a finite Zariski
cover by homogeneous polynomial triples over Q. The cover and actual
elliptic point-group realization hold over every field, not a sample
of K-points. No commutation-with-conjugation premise is present. -/
structure RationalCurveIsogeny (W : WeierstrassCurve ℚ) where
  chartCount : ℕ
  domain : Fin chartCount → MvPolynomial (Fin 3) ℚ
  domainDegree : Fin chartCount → ℕ
  domain_homogeneous : ∀ i,(domain i).IsHomogeneous (domainDegree i)
  image : Fin chartCount → Fin 3 → MvPolynomial (Fin 3) ℚ
  imageDegree : Fin chartCount → ℕ
  image_homogeneous : ∀ i j,(image i j).IsHomogeneous (imageDegree i)
  pointMap (F : Type) [Field F] [CharZero F] [Algebra ℚ F] [DecidableEq F] :
    (E0.baseChange F).toAffine.Point →+ (W.baseChange F).toAffine.Point
  cover (F : Type) [Field F] [CharZero F] [Algebra ℚ F] [DecidableEq F]
    (P : (E0.baseChange F).toAffine.Point) :
    ∃ i,MvPolynomial.eval₂ (algebraMap ℚ F) (coordinates P) (domain i)≠0
  regular (F : Type) [Field F] [CharZero F] [Algebra ℚ F] [DecidableEq F]
    (P : (E0.baseChange F).toAffine.Point) (i : Fin chartCount)
    (hi : MvPolynomial.eval₂ (algebraMap ℚ F) (coordinates P) (domain i)≠0) :
    ∃ c : F,c≠0 ∧ ∀ j,coordinates (pointMap F P) j=
      c*MvPolynomial.eval₂ (algebraMap ℚ F) (coordinates P) (image i j)
  finite_kernel (F : Type) [Field F] [CharZero F] [Algebra ℚ F] [DecidableEq F] :
    Set.Finite ((pointMap F).ker : Set (E0.baseChange F).toAffine.Point)

def targetSigma (W : WeierstrassCurve ℚ) :
    (W.baseChange K).toAffine.Point →+ (W.baseChange K).toAffine.Point :=
  Point.map (W':=W.toAffine) conjugation

def targetEmbed (W : WeierstrassCurve ℚ) :
    W.toAffine.Point →+ (W.baseChange K).toAffine.Point :=
  Point.baseChange (W':=W.toAffine) ℚ K

private theorem coordinates_sigma (W : WeierstrassCurve ℚ)
    (P : (W.baseChange K).toAffine.Point) (j : Fin 3) :
    coordinates (targetSigma W P) j=conjugation (coordinates P j) := by
  cases P with
  | zero =>
    change coordinates (targetSigma W (0:(W.baseChange K).toAffine.Point)) j=
      conjugation (coordinates (0:(W.baseChange K).toAffine.Point) j)
    rw [map_zero]
    fin_cases j <;> simp [coordinates]
  | some x y h =>
    simp only [targetSigma,Point.map_some]
    fin_cases j <;> simp [coordinates]

private theorem conjugation_eval (p : MvPolynomial (Fin 3) ℚ) (v : Fin 3 → K) :
    conjugation (MvPolynomial.eval₂ (algebraMap ℚ K) v p)=
      MvPolynomial.eval₂ (algebraMap ℚ K) (conjugation ∘ v) p := by
  change conjugation.toRingHom (MvPolynomial.eval₂ (algebraMap ℚ K) v p)=_
  rw [MvPolynomial.eval₂_comp_left]
  have hc : conjugation.toRingHom.comp (algebraMap ℚ K)=algebraMap ℚ K :=
    RingHom.ext (fun q=>conjugation.commutes q)
  rw [hc]
  rfl

/-- Galois equivariance is a consequence of the actual rational curve charts. -/
theorem isogeny_sigma (W : WeierstrassCurve ℚ) (φ : RationalCurveIsogeny W)
    (P : KPoint) : φ.pointMap K (sigma P)=targetSigma W (φ.pointMap K P) := by
  obtain ⟨i,hi⟩:=φ.cover K P
  have hcoords : coordinates (sigma P)=conjugation ∘ coordinates P := by
    funext j
    exact coordinates_sigma E0 P j
  have hactive : MvPolynomial.eval₂ (algebraMap ℚ K) (coordinates (sigma P)) (φ.domain i)≠0 := by
    rw [hcoords,←conjugation_eval]
    exact (map_ne_zero conjugation).mpr hi
  obtain ⟨a,ha,hPa⟩:=φ.regular K P i hi
  obtain ⟨b,hb,hPb⟩:=φ.regular K (sigma P) i hactive
  apply coordinates_ext _ _
    (fun j=>MvPolynomial.eval₂ (algebraMap ℚ K) (coordinates (sigma P)) (φ.image i j))
    b (conjugation a) hb ((map_ne_zero conjugation).mpr ha) hPb
  intro j
  rw [coordinates_sigma,hPa,map_mul,conjugation_eval,hcoords]

/-- The actual original infinite-order obstruction survives every rational curve isogeny. -/
theorem isogeny_T_infinite_order (W : WeierstrassCurve ℚ) (φ : RationalCurveIsogeny W) :
    ¬IsOfFinAddOrder (φ.pointMap K T) := by
  intro ht
  obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp ht
  letI : Fintype (φ.pointMap K).ker := (φ.finite_kernel K).fintype
  let t : (φ.pointMap K).ker:=⟨n•T,by
    change φ.pointMap K (n•T)=0
    simpa only [map_nsmul] using he⟩
  have ht' : IsOfFinAddOrder t:=isOfFinAddOrder_of_finite t
  obtain ⟨m,hm,heq⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp ht'
  apply T_infinite_order
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨m*n,Nat.mul_pos hm hn,?_⟩
  rw [Nat.mul_comm,mul_nsmul]
  exact congrArg Subtype.val heq

/-- Every point in the entire original Galois-difference coset remains
nonrational under every rational curve isogeny in the full atlas representation. -/
theorem isogeny_no_rational_image (W : WeierstrassCurve ℚ)
    (φ : RationalCurveIsogeny W) (P : KPoint) (hP : P - sigma P = T) :
    ¬∃ Q : W.toAffine.Point,targetEmbed W Q=φ.pointMap K P := by
  rintro ⟨Q,hQ⟩
  have hfixed : targetSigma W (φ.pointMap K P)=φ.pointMap K P := by
    rw [←hQ]
    exact Point.map_baseChange (W':=W.toAffine) conjugation Q
  have he : φ.pointMap K T=0 := by
    rw [←hP,map_sub,isogeny_sigma,hfixed,sub_self]
  exact isogeny_T_infinite_order W φ (isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨1,by norm_num,by simp [he]⟩)

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6RationalCurveIsogeny
