/- GID: D5/S3/VertexAlgebra/Lattice/ActualCoefficientRealForm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualCoefficientRealForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient conjugation of actual lattice fields and their theta-fixed restriction. -/

import D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCriticalMatter

/-! The charged seed uses the original polynomial translation and cocycle.
The word and basis arguments follow the native normal-product and basis steps
of `LatticeInvolution.wordField_theta` and `LatticeInvolution.stateField_theta`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator
open ComplexConjugate

namespace D5.S3.VertexAlgebra.Lattice.ActualCoefficientRealForm

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeInvolution FieldNormalProduct MvPolynomial
open LatticeSugawaraCurrents SourceBPZ.OriginalMatterHermitian
open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open private kappa_rawCoeff from D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy

private def kappaAdd (D : LatticeData) : Carrier D →+ Carrier D where
  toFun := kappaCarrier
  map_zero' := kappaCarrier_zero
  map_add' := kappaCarrier_add

private theorem kappa_actualField_ncoeff (D : LatticeData) (d : Charge D)
    (n : ℤ) (v : Carrier D) :
    kappaCarrier (((actualField D d)[[n]]) v) = ((actualField D d)[[n]]) (kappaCarrier v) := by
  simp only [actualField, VertexOperator.ncoeff_of_coeff]
  exact kappa_rawCoeff d (-n-1) v

private theorem kappa_dividedDerivative (D : LatticeData) (x : Index D)
    (n : ℤ) (v : Carrier D) :
    kappaCarrier (((dividedDerivative x.2 (neutralField D x.1))[[n]]) v) =
      ((dividedDerivative x.2 (neutralField D x.1))[[n]]) (kappaCarrier v) := by
  change kappaCarrier (Ring.choose (-n-1+x.2) x.2 •
    HVertexOperator.coeff (neutralField D x.1) (-n-1+x.2) v) =
    Ring.choose (-n-1+x.2) x.2 •
      HVertexOperator.coeff (neutralField D x.1) (-n-1+x.2) (kappaCarrier v)
  have hmap (z : ℤ) (u : Carrier D) :
      kappaCarrier (z • u) = z • kappaCarrier u :=
    (kappaAdd D).map_zsmul z u
  simp only [hmap, VertexOperator.coeff_eq_ncoeff, neutralField_ncoeff,
    kappaCarrier_neutralMode]

private theorem kappa_normalMinusOne (D : LatticeData)
    (A B : VertexOperator ℂ (Carrier D))
    (hA : ∀ n v, kappaCarrier ((A[[n]]) v) = (A[[n]]) (kappaCarrier v))
    (hB : ∀ n v, kappaCarrier ((B[[n]]) v) = (B[[n]]) (kappaCarrier v))
    (n : ℤ) (v : Carrier D) :
    kappaCarrier (((normalMinusOne A B).1[[n]]) v) =
      ((normalMinusOne A B).1[[n]]) (kappaCarrier v) := by
  rw [(normalMinusOne A B).2 n v, (normalMinusOne A B).2 n (kappaCarrier v), kappaCarrier_add]
  have hmap (f : ℕ → Carrier D) (hf : Function.HasFiniteSupport f) :
      kappaCarrier (∑ᶠ i, f i) = ∑ᶠ i, kappaCarrier (f i) :=
    (kappaAdd D).map_finsum hf
  rw [hmap _ (normal_forward_finite D A B n v),
    hmap _ (normal_reverse_finite D A B n v)]
  simp only [hA, hB]

/-- Coefficient conjugation commutes with every normalized coefficient of an
actual ordered word field and preserves its integral charge label. -/
theorem wordField_kappa (D : LatticeData) (d : Charge D) (w : List (Index D))
    (n : ℤ) (v : Carrier D) :
    kappaCarrier (((wordField D d w)[[n]]) v) =
      ((wordField D d w)[[n]]) (kappaCarrier v) := by
  induction w generalizing n v with
  | nil => simpa only [wordField] using kappa_actualField_ncoeff D d n v
  | cons x w ih =>
      simp only [wordField]
      exact kappa_normalMinusOne D (dividedDerivative x.2 (neutralField D x.1))
        (wordField D d w) (kappa_dividedDerivative D x) ih n v

/-- Coefficient conjugation on both inputs commutes with every actual
all-state lattice coefficient. -/
theorem stateField_kappa (D : LatticeData) (a b : Carrier D) (n : ℤ) :
    kappaCarrier (((Y D a)[[n]]) b) = ((Y D (kappaCarrier a))[[n]]) (kappaCarrier b) := by
  classical
  have basis_case (d : Charge D) (e : Index D →₀ ℕ) :
      kappaCarrier (((Y D (Finsupp.single d (monomial e 1)))[[n]]) b) =
        ((Y D (kappaCarrier (Finsupp.single d (monomial e 1))))[[n]]) (kappaCarrier b) := by
    have fixed_basis : kappaCarrier (Finsupp.single d (monomial e 1)) =
        Finsupp.single d (monomial e 1) := by
      simp [kappaOsc, MvPolynomial.map_monomial]
    rw [fixed_basis, stateField_monomial]
    exact wordField_kappa D d (occurrences D e) n b
  -- Expand first in charge singles and then in oscillator monomials.
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a c ha hc =>
      simp only [map_add, Pi.add_apply, LinearMap.add_apply, kappaCarrier_add, ha, hc]
  | single d p =>
      induction p using MvPolynomial.induction_on' with
      | add p q hp hq =>
          simp only [Finsupp.single_add, map_add, Pi.add_apply, LinearMap.add_apply,
            kappaCarrier_add, hp, hq]
      | monomial e c =>
          have hc : monomial e c = c • (monomial e 1 : Oscillator D) := by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
          rw [hc, ← Finsupp.smul_single]
          simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply,
            kappaCarrier_smul, basis_case]

theorem kappa_mem_fixedSpace (D : LatticeData) {v : Carrier D} (hv : v ∈ fixedSpace D) :
    kappaCarrier v ∈ fixedSpace D := by
  rw [mem_fixedSpace] at hv ⊢
  rw [← kappaCarrier_theta, hv]

local instance fixedCarrierGroup (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

/-- The original coefficient conjugation on the actual theta-fixed sector. -/
def fixedKappa (D : LatticeData) (v : FixedCarrier D) : FixedCarrier D :=
  ⟨kappaCarrier v.val, kappa_mem_fixedSpace D v.property⟩

theorem fixedKappa_add (D : LatticeData) (a b : FixedCarrier D) :
    fixedKappa D (a + b) = fixedKappa D a + fixedKappa D b := by
  apply Subtype.ext
  exact kappaCarrier_add a.val b.val

theorem fixedKappa_smul (D : LatticeData) (c : ℂ) (a : FixedCarrier D) :
    fixedKappa D (c • a) = conj c • fixedKappa D a := by
  apply Subtype.ext
  exact kappaCarrier_smul c a.val

theorem fixedKappa_involutive (D : LatticeData) : Function.Involutive (fixedKappa D) := by
  intro a
  apply Subtype.ext
  exact kappaCarrier_involutive a.val

theorem fixedY_kappa (D : LatticeData) (a b : FixedCarrier D) (n : ℤ) :
    fixedKappa D (((fixedY D a)[[n]]) b) =
      ((fixedY D (fixedKappa D a))[[n]]) (fixedKappa D b) := by
  apply Subtype.ext
  simpa only [fixedKappa, fixedY_mode_val] using stateField_kappa D a.val b.val n

theorem kappa_vacuum (D : LatticeData) : kappaCarrier (vacuum D) = vacuum D := by
  simp [vacuum, kappaOsc]

theorem fixedKappa_vacuum (D : LatticeData) : fixedKappa D (fixedVacuum D) = fixedVacuum D := by
  apply Subtype.ext
  exact kappa_vacuum D

theorem kappa_translation (D : LatticeData) (v : Carrier D) :
    kappaCarrier (LatticeSugawaraConformal.translation D v) =
      LatticeSugawaraConformal.translation D (kappaCarrier v) := by
  simp only [LatticeActualVertexAlgebra.translation_as_mode, stateField_kappa, kappa_vacuum]

private theorem kappa_omega (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hH : ∀ i j, conj (H i j) = H i j) :
    kappaCarrier (LatticeActualConformalState.omega D H) = LatticeActualConformalState.omega D H := by
  have hsum (s : Finset (Fin D.rank)) (f : Fin D.rank → Oscillator D) :
      kappaOsc (∑ i ∈ s, f i) = ∑ i ∈ s, kappaOsc (f i) :=
    map_sum (MvPolynomial.map (starRingEnd ℂ)) f s
  have hhalf : conj ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [map_inv₀]
    rw [show conj (2 : ℂ) = 2 by apply Complex.ext <;> norm_num]
  simp only [LatticeActualConformalState.omega, LatticeActualConformalState.conformalPolynomial,
    kappaCarrier_single, kappaOsc_smul, hsum, hhalf, hH, kappaOsc_mul, kappaOsc_X]

/-- The literal stress state in the fixed summand of the Leech orbifold. -/
theorem fixedKappa_leechStress :
    fixedKappa leechData ActualLeechOrbifoldMatter.omega.1 = ActualLeechOrbifoldMatter.omega.1 := by
  apply Subtype.ext
  let H := HalfFockSpectralFiberSource.actualInverse leechData
  change kappaCarrier (LatticeActualConformalState.omega leechData H) =
    LatticeActualConformalState.omega leechData H
  apply kappa_omega
  intro i j
  simp [H, HalfFockSpectralFiberSource.actualInverse]

/-- The actual quadratic state for the standalone hyperbolic plane's stress field. -/
theorem kappa_hyperbolicStress :
    kappaCarrier (LatticeActualConformalState.omega hyperbolicPlane (gramComplex hyperbolicPlane)) =
      LatticeActualConformalState.omega hyperbolicPlane (gramComplex hyperbolicPlane) := by
  apply kappa_omega
  intro i j
  simp [gramComplex]

end D5.S3.VertexAlgebra.Lattice.ActualCoefficientRealForm
