/- GID: D5/S3/Midline/Cayley/CanonicalZetaMirrorEvenOddDecomposition
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/CanonicalZetaMirrorEvenOddDecomposition
   mirror-E: none(waiver:canonical-zeta-krein-interface)
   anchors: []
   digest: Construct normalized mirror-even and mirror-odd projections, prove orthogonality, and decompose the Krein form as positive energy minus negative energy. -/

import D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry

/-!
# Canonical mirror even-odd decomposition

The mirror fundamental symmetry is an involutive self-adjoint isometry.  This
node constructs its normalized `+1` and `-1` spectral projections directly on
the multiplicity-expanded zero Hilbert space.  It proves exact reconstruction,
idempotence, mutual annihilation, Hilbert orthogonality, and the fundamental
Krein energy identity.

These are projection and form identities on the actual zero Hilbert space.
They are stronger than the existence of one odd witness and do not assume RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Midline.Cayley.CanonicalZetaMirrorEvenOddDecomposition

open D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry
open D5.S3.Weil.ZeroSum
open scoped ENNReal InnerProduct lp

/-- The normalized projection onto the mirror-even sector. -/
noncomputable def mirrorEvenPart (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) : MirrorZeroHilbertSpace Z :=
  (1 / 2 : Complex) • (psi + mirrorFundamentalSymmetry Z psi)

/-- The normalized projection onto the mirror-odd sector. -/
noncomputable def mirrorOddProjectionPart (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) : MirrorZeroHilbertSpace Z :=
  (1 / 2 : Complex) • (psi - mirrorFundamentalSymmetry Z psi)

/-- The even projection is a `+1` mirror eigenvector. -/
@[simp]
theorem mirrorEvenPart_eigenvalue_one (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorFundamentalSymmetry Z (mirrorEvenPart Z psi) =
      mirrorEvenPart Z psi := by
  rw [mirrorEvenPart, map_smul, map_add,
    mirrorFundamentalSymmetry_involutive]
  module

/-- The odd projection is a `-1` mirror eigenvector. -/
@[simp]
theorem mirrorOddProjectionPart_eigenvalue_neg_one (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorFundamentalSymmetry Z (mirrorOddProjectionPart Z psi) =
      -mirrorOddProjectionPart Z psi := by
  rw [mirrorOddProjectionPart, map_smul, map_sub,
    mirrorFundamentalSymmetry_involutive]
  module

/-- Even and odd projections reconstruct the original vector exactly. -/
theorem mirrorEvenPart_add_mirrorOddProjectionPart (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorEvenPart Z psi + mirrorOddProjectionPart Z psi = psi := by
  rw [mirrorEvenPart, mirrorOddProjectionPart]
  module

/-- The mirror image is the even component minus the odd component. -/
theorem mirrorFundamentalSymmetry_eq_even_sub_odd (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorFundamentalSymmetry Z psi =
      mirrorEvenPart Z psi - mirrorOddProjectionPart Z psi := by
  rw [mirrorEvenPart, mirrorOddProjectionPart]
  module

/-- The even projection is idempotent. -/
@[simp]
theorem mirrorEvenPart_idempotent (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorEvenPart Z (mirrorEvenPart Z psi) = mirrorEvenPart Z psi := by
  rw [mirrorEvenPart, mirrorEvenPart_eigenvalue_one]
  module

/-- The odd projection is idempotent. -/
@[simp]
theorem mirrorOddProjectionPart_idempotent (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorOddProjectionPart Z (mirrorOddProjectionPart Z psi) =
      mirrorOddProjectionPart Z psi := by
  rw [mirrorOddProjectionPart, mirrorOddProjectionPart_eigenvalue_neg_one]
  module

/-- The even projection annihilates the odd sector. -/
@[simp]
theorem mirrorEvenPart_odd_eq_zero (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorEvenPart Z (mirrorOddProjectionPart Z psi) = 0 := by
  rw [mirrorEvenPart, mirrorOddProjectionPart_eigenvalue_neg_one]
  module

/-- The odd projection annihilates the even sector. -/
@[simp]
theorem mirrorOddProjectionPart_even_eq_zero (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorOddProjectionPart Z (mirrorEvenPart Z psi) = 0 := by
  rw [mirrorOddProjectionPart, mirrorEvenPart_eigenvalue_one]
  module

/-- The odd projection vanishes exactly on mirror-fixed vectors. -/
theorem mirrorOddProjectionPart_eq_zero_iff (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorOddProjectionPart Z psi = 0 ↔
      mirrorFundamentalSymmetry Z psi = psi := by
  constructor
  · intro hzero
    have hscaled := congrArg
      (fun x : MirrorZeroHilbertSpace Z => (2 : Complex) • x) hzero
    have hsub : psi - mirrorFundamentalSymmetry Z psi = 0 := by
      simpa [mirrorOddProjectionPart] using hscaled
    exact (sub_eq_zero.mp hsub).symm
  · intro hfixed
    rw [mirrorOddProjectionPart, hfixed, sub_self, smul_zero]

/-- Mirror-even and mirror-odd sectors are Hilbert orthogonal. -/
theorem mirror_even_odd_inner_eq_zero (Z : ZeroData)
    (psi phi : MirrorZeroHilbertSpace Z) :
    ⟪mirrorEvenPart Z psi, mirrorOddProjectionPart Z phi⟫_Complex = 0 := by
  have hself := mirrorFundamentalSymmetry_inner_left Z
    (mirrorEvenPart Z psi) (mirrorOddProjectionPart Z phi)
  rw [mirrorEvenPart_eigenvalue_one,
    mirrorOddProjectionPart_eigenvalue_neg_one,
    inner_neg_right] at hself
  have htwo :
      (2 : Complex) *
        ⟪mirrorEvenPart Z psi, mirrorOddProjectionPart Z phi⟫_Complex = 0 := by
    linear_combination hself
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Reversing the two parity sectors is also orthogonal. -/
theorem mirror_odd_even_inner_eq_zero (Z : ZeroData)
    (psi phi : MirrorZeroHilbertSpace Z) :
    ⟪mirrorOddProjectionPart Z psi, mirrorEvenPart Z phi⟫_Complex = 0 := by
  have h := congrArg conj
    (mirror_even_odd_inner_eq_zero Z phi psi)
  simpa only [map_zero, inner_conj_symm] using h

/-- The mirror fundamental symmetry squares to the identity as a bounded
operator. -/
theorem mirrorFundamentalSymmetry_mul_self (Z : ZeroData) :
    (mirrorFundamentalSymmetry Z :
        MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z) *
      (mirrorFundamentalSymmetry Z :
        MirrorZeroHilbertSpace Z →L[Complex] MirrorZeroHilbertSpace Z) = 1 := by
  apply ContinuousLinearMap.ext
  intro psi
  exact mirrorFundamentalSymmetry_involutive Z psi

/-- The mirror sends a coordinate basis vector to the basis vector of its
mirror coordinate. -/
theorem mirrorFundamentalSymmetry_single (Z : ZeroData)
    (v : ZeroCoordinate Z) :
    mirrorFundamentalSymmetry Z
        (lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2 v 1) =
      lp.single (E := fun _ : ZeroCoordinate Z => Complex) 2
        (mirrorCoordinatePerm Z v) 1 := by
  apply lp.ext
  funext w
  by_cases h : mirrorCoordinatePerm Z w = v
  · have hw : w = mirrorCoordinatePerm Z v := by
      calc
        w = mirrorCoordinatePerm Z (mirrorCoordinatePerm Z w) :=
          (mirrorCoordinatePerm_involutive Z w).symm
        _ = mirrorCoordinatePerm Z v := congrArg (mirrorCoordinatePerm Z) h
    simp [mirrorFundamentalSymmetry_apply, lp.single_apply,
      Pi.single_apply, h, hw]
  · have hw : w ≠ mirrorCoordinatePerm Z v := by
      intro hw
      apply h
      rw [hw, mirrorCoordinatePerm_involutive]
    simp [mirrorFundamentalSymmetry_apply, lp.single_apply,
      Pi.single_apply, h, hw]

/-- The Krein form is the positive Hilbert energy of the even sector minus the
positive Hilbert energy of the odd sector. -/
theorem mirrorKreinForm_even_odd_decomposition (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorKreinForm Z psi psi =
      ⟪mirrorEvenPart Z psi, mirrorEvenPart Z psi⟫_Complex -
        ⟪mirrorOddProjectionPart Z psi,
          mirrorOddProjectionPart Z psi⟫_Complex := by
  calc
    mirrorKreinForm Z psi psi =
        ⟪mirrorEvenPart Z psi + mirrorOddProjectionPart Z psi,
          mirrorEvenPart Z psi - mirrorOddProjectionPart Z psi⟫_Complex := by
      rw [mirrorKreinForm,
        mirrorEvenPart_add_mirrorOddProjectionPart,
        ← mirrorFundamentalSymmetry_eq_even_sub_odd]
    _ =
        ⟪mirrorEvenPart Z psi, mirrorEvenPart Z psi⟫_Complex -
          ⟪mirrorOddProjectionPart Z psi,
            mirrorOddProjectionPart Z psi⟫_Complex := by
      rw [inner_add_left, inner_sub_right, inner_sub_right,
        mirror_even_odd_inner_eq_zero,
        mirror_odd_even_inner_eq_zero]
      ring

/-- Real Krein energy is exactly even norm-square minus odd norm-square. -/
theorem mirrorKreinForm_re_eq_even_norm_sq_sub_odd_norm_sq (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    (mirrorKreinForm Z psi psi).re =
      ‖mirrorEvenPart Z psi‖ ^ 2 -
        ‖mirrorOddProjectionPart Z psi‖ ^ 2 := by
  rw [mirrorKreinForm_even_odd_decomposition, Complex.sub_re,
    ← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner]

/-- The complete normalized parity decomposition package. -/
theorem canonical_mirror_even_odd_decomposition (Z : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) :
    mirrorEvenPart Z psi + mirrorOddProjectionPart Z psi = psi ∧
      mirrorFundamentalSymmetry Z (mirrorEvenPart Z psi) =
        mirrorEvenPart Z psi ∧
      mirrorFundamentalSymmetry Z (mirrorOddProjectionPart Z psi) =
        -mirrorOddProjectionPart Z psi ∧
      ⟪mirrorEvenPart Z psi, mirrorOddProjectionPart Z psi⟫_Complex = 0 ∧
      (mirrorKreinForm Z psi psi).re =
        ‖mirrorEvenPart Z psi‖ ^ 2 -
          ‖mirrorOddProjectionPart Z psi‖ ^ 2 := by
  exact ⟨mirrorEvenPart_add_mirrorOddProjectionPart Z psi,
    mirrorEvenPart_eigenvalue_one Z psi,
    mirrorOddProjectionPart_eigenvalue_neg_one Z psi,
    mirror_even_odd_inner_eq_zero Z psi psi,
    mirrorKreinForm_re_eq_even_norm_sq_sub_odd_norm_sq Z psi⟩

#print axioms mirrorEvenPart_idempotent
#print axioms mirrorOddProjectionPart_eq_zero_iff
#print axioms mirror_even_odd_inner_eq_zero
#print axioms mirrorKreinForm_even_odd_decomposition
#print axioms canonical_mirror_even_odd_decomposition

end D5.S3.Midline.Cayley.CanonicalZetaMirrorEvenOddDecomposition
