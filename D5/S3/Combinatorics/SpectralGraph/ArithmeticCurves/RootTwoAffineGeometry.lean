/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/RootTwoAffineGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/RootTwoAffineGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full original root-two affine curve rings remain integral over every field extension -/
import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.RootTwoTailCurve
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.PolynomialAlgebra
/-! Complete original S.root2curve, PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02,
Ma/Nikandish/Zhang. This supplies actual full affine coordinate rings and Spec
objects throughout every original a>=2 and every extension field of Q.
Smooth projective normalization, genus one and the original Siegel method
remain separate obligations; no genus or finiteness premise is used here. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.RootTwoAffineGeometry
open Polynomial RootTwoTailCurve

private theorem fraction_nonsquare {F : Type*} [Field F] (f : F[X])
    (hf : Squarefree f) (hn : ¬ IsUnit f) (x : FractionRing F[X]) :
    x ^ 2 ≠ algebraMap F[X] (FractionRing F[X]) f := by
  intro hx
  have hi : IsIntegral F[X] (x^2) := by
    rw [hx]
    exact isIntegral_algebraMap
  obtain ⟨g,hg⟩:=IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by decide : 0<2) hi
  have hg2 : g*g=f := by
    apply IsFractionRing.injective F[X] (FractionRing F[X])
    rw [map_mul,hg,←pow_two,hx]
  have hu : IsUnit g:=hf g (by rw [←hg2])
  exact hn (hg2 ▸ hu.mul hu)

private theorem quadratic_irreducible {F : Type*} [Field F] (f : F[X])
    (hf : Squarefree f) (hn : ¬ IsUnit f) :
    Irreducible (X^2-C f : F[X][X]) := by
  have hm : (X^2-C f : F[X][X]).Monic:=monic_X_pow_sub_C f (by decide)
  apply (hm.irreducible_iff_irreducible_map_fraction_map
    (K:=FractionRing F[X])).mpr
  simpa only [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C] using
    X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 2) (fraction_nonsquare f hf hn)

private theorem quartic_coeff_four (a : ℚ) :
    (quarticPolynomial a).coeff 4=4*(a-1)*(a+1)*(a^2-a-1)*(a^2+a+1) := by
  have hq : quarticPolynomial a=
      C (4*(a-1)*(a+1)*(a^2-a-1)*(a^2+a+1))*X^4+
      C (4*(a-1)^2*(a^2+a+1)*(4*a^3+6*a^2-a-2))*X^3+
      C ((a-1)^2*(16*a^6+40*a^5+8*a^4-20*a^3-31*a^2-8*a+4))*X^2+
      C (2*a*(a-1)^3*(2*a+1)*(4*a^3+2*a^2-a-2))*X+
      C (a^2*(a-1)^4*(2*a+1)^2) := by
    apply Polynomial.funext
    intro b
    simp [quarticPolynomial,quartic,A,B,C₀]
    ring
  rw [hq]
  norm_num only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] <;> simp

private theorem extension_quartic_nonunit {F : Type*} [Field F] [Algebra ℚ F]
    (a : ℚ) (ha : 2 ≤ a) : ¬ IsUnit ((quarticPolynomial a).map (algebraMap ℚ F)) := by
  intro hu
  have hz : ((quarticPolynomial a).map (algebraMap ℚ F)).coeff 4=0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [natDegree_eq_zero_of_isUnit hu];omega)
  rw [coeff_map,quartic_coeff_four] at hz
  have ha0 : 0<a := by linarith
  have ha1 : 0<a-1 := by linarith
  have ha2 : 0<a^2-a-1 := by nlinarith [sq_nonneg (a-2)]
  have hc : 4*(a-1)*(a+1)*(a^2-a-1)*(a^2+a+1)≠0 := by positivity
  apply hc
  exact (algebraMap ℚ F).injective (by simpa using hz)

/-- Exact original affine equation over each complete extension field. -/
def planePolynomial (a : ℚ) (F : Type*) [Field F] [Algebra ℚ F] : F[X][X] :=
  X^2-C ((quarticPolynomial a).map (algebraMap ℚ F))

/-- No algebraic extension introduces a component into the entire
original affine curve, for any a>=2. -/
theorem planePolynomial_irreducible (a : ℚ) (ha : 2 ≤ a)
    (F : Type*) [Field F] [Algebra ℚ F] : Irreducible (planePolynomial a F) :=
  quadratic_irreducible _ (quartic_geometrically_separable a ha).squarefree
    (extension_quartic_nonunit a ha)

/-- The actual affine coordinate algebra, with both coordinates and the
entire defining equation; this is not the rational function field alone. -/
abbrev CoordinateRing (a : ℚ) (F : Type*) [Field F] [Algebra ℚ F] :=
  AdjoinRoot (planePolynomial a F)

/-- The full affine coordinate ring is an integral domain after every
field extension, including the algebraic closure. -/
theorem coordinateRing_isDomain (a : ℚ) (ha : 2 ≤ a)
    (F : Type*) [Field F] [Algebra ℚ F] : IsDomain (CoordinateRing a F) :=
  AdjoinRoot.isDomain_of_prime (planePolynomial_irreducible a ha F).prime

def affineCurve (a : ℚ) (F : Type*) [Field F] [Algebra ℚ F] : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (CoordinateRing a F))

open TensorProduct Algebra.TensorProduct

/-- Scalar extension of the entire coordinate ring agrees with the
original full polynomial presentation over the extension field. -/
def baseChangeEquiv (a : ℚ) (F : Type*) [Field F] [Algebra ℚ F] :
    F ⊗[ℚ] CoordinateRing a ℚ ≃ₐ[F] CoordinateRing a F := by
  let p := planePolynomial a ℚ
  let q := p.map (includeRight : ℚ[X] →ₐ[ℚ] F ⊗[ℚ] ℚ[X]).toRingHom
  let e := (polyEquivTensor' ℚ F).symm
  refine (AdjoinRoot.tensorAlgEquiv p q rfl).trans (AdjoinRoot.mapAlgEquiv e q
    (planePolynomial a F) ?_)
  apply Associated.of_eq
  change (p.map (includeRight : ℚ[X] →ₐ[ℚ] F ⊗[ℚ] ℚ[X]).toRingHom).map
    e.toRingHom = planePolynomial a F
  have he (f : ℚ[X]) : e (includeRight f) = f.map (algebraMap ℚ F) := by
    simp [e, includeRight_apply, coe_polyEquivTensor'_symm]
  simp only [p, planePolynomial, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe]
  change X^2 - C (e (includeRight ((quarticPolynomial a).map (algebraMap ℚ ℚ)))) =
    X^2 - C ((quarticPolynomial a).map (algebraMap ℚ F))
  rw [he]
  simp [Polynomial.map_map]


open CategoryTheory AlgebraicGeometry

/-- The actual structure map of the entire rational affine curve. -/
def structureMorphism (a : ℚ) : affineCurve a ℚ ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (CoordinateRing a ℚ)))

/-- All geometric fibers of the actual structure map are integral.
The tensor presentation, not a separately declared family, carries this claim. -/
theorem affineCurve_geometricallyIntegral (a : ℚ) (ha : 2 ≤ a) :
    GeometricallyIntegral (structureMorphism a) := by
  rw [GeometricallyIntegral.eq_geometrically,
    geometrically_iff_of_commRing]
  intro F _ _ Z fst snd hZ
  letI := coordinateRing_isDomain a ha F
  let e := (Algebra.TensorProduct.comm ℚ (CoordinateRing a ℚ) F).toRingEquiv.trans
    (baseChangeEquiv a F).toRingEquiv
  letI := e.toMulEquiv.isDomain (CoordinateRing a F)
  let iso := hZ.isoPullback ≪≫ pullbackSpecIso ℚ (CoordinateRing a ℚ) F
  exact IsIntegral.of_isIso iso.inv

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.RootTwoAffineGeometry
