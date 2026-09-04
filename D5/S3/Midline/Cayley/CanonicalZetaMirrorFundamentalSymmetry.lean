/- GID: D5/S3/Midline/Cayley/CanonicalZetaMirrorFundamentalSymmetry
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/CanonicalZetaMirrorFundamentalSymmetry
   mirror-E: none(waiver:canonical-zeta-krein-interface)
   anchors: []
   digest: Lift the same-height zero mirror to a self-adjoint involutive isometry on the multiplicity-expanded zero Hilbert space. -/

import D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv
import D5.S3.Weil.ZetaBridge.UnconditionalCanonicalZeroData
import D5.S3.Midline.Cayley.ZeroHilbertCayleyUnitarity

/-!
# Mirror fundamental symmetry on the zero Hilbert space

The functional-equation reflection and complex conjugation combine to the
same-height mirror `rho ↦ 1 - conj rho`.  Its index permutation preserves
analytic multiplicity.  Hence it lifts to the multiplicity-expanded zero
coordinate type and then to a linear isometric involution on `ell^2`.

The induced indefinite form is positive on mirror-even vectors and negative on
mirror-odd vectors.  Every nonfixed mirror coordinate supplies an explicit
strict negative direction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry

open D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
open D5.S3.Midline.Cayley.ZeroHilbertCayleyUnitarity
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv
open D5.S3.Weil.ZetaBridge.UnconditionalCanonicalZeroData
open scoped ENNReal InnerProduct lp

/-- The same-height mirror lifted through the analytic-multiplicity fibers. -/
noncomputable def mirrorCoordinatePerm (Z : ZeroData) :
    Equiv.Perm (ZeroCoordinate Z) :=
  (mirrorIndex Z).sigmaCongr fun n =>
    finCongr (mirrorIndex_multiplicity Z n).symm

@[simp]
theorem mirrorCoordinatePerm_fst (Z : ZeroData) (v : ZeroCoordinate Z) :
    (mirrorCoordinatePerm Z v).1 = mirrorIndex Z v.1 := rfl

/-- The lifted coordinate mirror is an involution. -/
@[simp]
theorem mirrorCoordinatePerm_involutive (Z : ZeroData)
    (v : ZeroCoordinate Z) :
    mirrorCoordinatePerm Z (mirrorCoordinatePerm Z v) = v := by
  rcases v with ⟨n, k⟩
  apply Sigma.ext
  · exact mirrorIndex_involutive Z n
  · apply heq_of_eq
    apply Fin.ext
    rfl

/-- The inverse lifted mirror equals the lifted mirror. -/
theorem mirrorCoordinatePerm_symm (Z : ZeroData) :
    (mirrorCoordinatePerm Z).symm = mirrorCoordinatePerm Z := by
  apply Equiv.ext
  intro v
  apply (mirrorCoordinatePerm Z).injective
  simp [mirrorCoordinatePerm_involutive]

/-- Coordinate fixedness is exactly fixedness of the underlying zero index. -/
theorem mirrorCoordinatePerm_fixed_iff (Z : ZeroData)
    (v : ZeroCoordinate Z) :
    mirrorCoordinatePerm Z v = v ↔ mirrorIndex Z v.1 = v.1 := by
  constructor
  · intro h
    exact congrArg Sigma.fst h
  · intro h
    rcases v with ⟨n, k⟩
    apply Sigma.ext
    · exact h
    · apply heq_of_eq
      apply Fin.ext
      rfl

/-- The multiplicity-expanded zero Hilbert space. -/
abbrev MirrorZeroHilbertSpace (Z : ZeroData) :=
  ObserverHilbertSpace (ZeroCoordinate Z)

/-- The mirror permutation represented as a surjective linear isometry. -/
noncomputable def mirrorFundamentalSymmetry (Z : ZeroData) :
    MirrorZeroHilbertSpace Z ≃ₗᵢ[Complex] MirrorZeroHilbertSpace Z :=
  updateLinearIsometryEquiv (mirrorCoordinatePerm Z)

@[simp]
theorem mirrorFundamentalSymmetry_apply (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) (v : ZeroCoordinate Z) :
    mirrorFundamentalSymmetry Z psi v =
      psi (mirrorCoordinatePerm Z v) := by
  change psi ((mirrorCoordinatePerm Z).symm v) = _
  rw [mirrorCoordinatePerm_symm]

/-- The Hilbert-space mirror squares to identity. -/
@[simp]
theorem mirrorFundamentalSymmetry_involutive (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorFundamentalSymmetry Z (mirrorFundamentalSymmetry Z psi) = psi := by
  apply lp.ext
  funext v
  simp [mirrorFundamentalSymmetry_apply, mirrorCoordinatePerm_involutive]

/-- The mirror is self-adjoint in inner-product form. -/
theorem mirrorFundamentalSymmetry_inner_left (Z : ZeroData)
    (psi phi : MirrorZeroHilbertSpace Z) :
    ⟪mirrorFundamentalSymmetry Z psi, phi⟫_Complex =
      ⟪psi, mirrorFundamentalSymmetry Z phi⟫_Complex := by
  have h := (mirrorFundamentalSymmetry Z).inner_map_map psi
    (mirrorFundamentalSymmetry Z phi)
  simpa [mirrorFundamentalSymmetry_involutive] using h

/-- The indefinite inner product determined by the mirror involution. -/
noncomputable def mirrorKreinForm (Z : ZeroData)
    (psi phi : MirrorZeroHilbertSpace Z) : Complex :=
  ⟪psi, mirrorFundamentalSymmetry Z phi⟫_Complex

/-- The antisymmetrization of a vector is mirror odd. -/
noncomputable def mirrorOddPart (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) : MirrorZeroHilbertSpace Z :=
  psi - mirrorFundamentalSymmetry Z psi

/-- Mirror antisymmetrization lies in the `-1` eigenspace. -/
theorem mirrorOddPart_eigenvalue_neg_one (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorFundamentalSymmetry Z (mirrorOddPart Z psi) =
      -mirrorOddPart Z psi := by
  rw [mirrorOddPart, map_sub, mirrorFundamentalSymmetry_involutive]
  module

/-- The explicit odd vector generated from one coordinate basis vector. -/
noncomputable def mirrorOddVector (Z : ZeroData) (v : ZeroCoordinate Z) :
    MirrorZeroHilbertSpace Z :=
  mirrorOddPart Z
    (lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1)

/-- A nonfixed mirror coordinate produces a nonzero odd vector. -/
theorem mirrorOddVector_ne_zero (Z : ZeroData) (v : ZeroCoordinate Z)
    (hmove : mirrorCoordinatePerm Z v ≠ v) :
    mirrorOddVector Z v ≠ 0 := by
  intro hzero
  have happly := congrArg (fun psi : MirrorZeroHilbertSpace Z => psi v) hzero
  have hreverse : v ≠ mirrorCoordinatePerm Z v := fun h => hmove h.symm
  simpa [mirrorOddVector, mirrorOddPart, mirrorFundamentalSymmetry_apply,
    lp.single_apply, Pi.single_apply, hreverse] using happly

/-- The Krein quadratic value of an odd vector is minus its Hilbert norm
squared. -/
theorem mirrorOddVector_krein_eq_neg_norm_sq (Z : ZeroData)
    (v : ZeroCoordinate Z) :
    (mirrorKreinForm Z (mirrorOddVector Z v) (mirrorOddVector Z v)).re =
      -‖mirrorOddVector Z v‖ ^ 2 := by
  rw [mirrorKreinForm, mirrorOddVector,
    mirrorOddPart_eigenvalue_neg_one, inner_neg_right,
    Complex.neg_re, norm_sq_eq_re_inner]

/-- Every nonfixed mirror coordinate gives an explicit strict negative Krein
direction. -/
theorem mirror_odd_vector_strictly_negative (Z : ZeroData)
    (v : ZeroCoordinate Z) (hmove : mirrorCoordinatePerm Z v ≠ v) :
    (mirrorKreinForm Z (mirrorOddVector Z v) (mirrorOddVector Z v)).re < 0 := by
  rw [mirrorOddVector_krein_eq_neg_norm_sq]
  have hnorm : 0 < ‖mirrorOddVector Z v‖ :=
    norm_pos_iff.mpr (mirrorOddVector_ne_zero Z v hmove)
  nlinarith

/-- The unconditional zeta mirror fundamental symmetry. -/
noncomputable def zetaMirrorFundamentalSymmetry :
    MirrorZeroHilbertSpace zetaZeroData ≃ₗᵢ[Complex]
      MirrorZeroHilbertSpace zetaZeroData :=
  mirrorFundamentalSymmetry zetaZeroData

#print axioms mirrorCoordinatePerm_involutive
#print axioms mirrorCoordinatePerm_fixed_iff
#print axioms mirrorFundamentalSymmetry_inner_left
#print axioms mirror_odd_vector_strictly_negative

end D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry
