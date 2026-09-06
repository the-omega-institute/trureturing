/- GID: D5/S3/Midline/Cayley/ZeroDataHilbertPresentationTransport
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/ZeroDataHilbertPresentationTransport
   mirror-E: none(waiver:canonical-zeta-krein-interface)
   anchors: []
   digest: Lift the unique ZeroData reindexing to a unitary Hilbert transport intertwining mirror symmetry, Cayley dynamics, and the Krein form. -/

import D5.S3.Midline.Cayley.CanonicalZetaCayleyJUnitary

/-!
# Hilbert transport between `ZeroData` presentations

The natural-number order in `ZeroData` is presentation data.  This node lifts
the unique zero-preserving reindexing to the multiplicity-expanded coordinate
space and then to a unitary map of the corresponding `ell^2` spaces.

The resulting unitary intertwines the same-height mirror, the zero Cayley
operator, and the mirror Krein form.  Hence the operator geometry constructed
from a valid `ZeroData` does not depend on the chosen enumeration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Midline.Cayley.ZeroDataHilbertPresentationTransport

open D5.S3.Observer.Approximation.ReadoutUpdateCommutatorFactorization
open D5.S3.Midline.Cayley.ZeroHilbertCayleyUnitarity
open D5.S3.Midline.Cayley.CanonicalZetaMirrorFundamentalSymmetry
open D5.S3.Midline.Cayley.CanonicalZetaCayleyJUnitary
open D5.S3.Midline.Cayley.CayleyUnitarityDefect
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ZeroDataPresentationEquiv
open scoped ENNReal InnerProduct lp

/-- The unique zero-preserving presentation equivalence, lifted through each
analytic-multiplicity fiber. -/
noncomputable def zeroCoordinatePresentationEquiv (Z Z' : ZeroData) :
    ZeroCoordinate Z ≃ ZeroCoordinate Z' :=
  (zeroDataPresentationEquiv Z Z').sigmaCongr fun n =>
    finCongr (zeroDataPresentationEquiv_multiplicity Z Z' n).symm

@[simp]
theorem zeroCoordinatePresentationEquiv_fst (Z Z' : ZeroData)
    (v : ZeroCoordinate Z) :
    (zeroCoordinatePresentationEquiv Z Z' v).1 =
      zeroDataPresentationEquiv Z Z' v.1 := rfl

/-- The lifted equivalence preserves the represented complex zero. -/
theorem zeroCoordinatePresentationEquiv_zero (Z Z' : ZeroData)
    (v : ZeroCoordinate Z) :
    Z'.zero (zeroCoordinatePresentationEquiv Z Z' v).1 = Z.zero v.1 := by
  rw [zeroCoordinatePresentationEquiv_fst,
    zeroDataPresentationEquiv_zero]

/-- The lifted presentation equivalence intertwines the multiplicity-expanded
same-height mirror. -/
theorem zeroCoordinatePresentationEquiv_mirror (Z Z' : ZeroData)
    (v : ZeroCoordinate Z) :
    zeroCoordinatePresentationEquiv Z Z' (mirrorCoordinatePerm Z v) =
      mirrorCoordinatePerm Z' (zeroCoordinatePresentationEquiv Z Z' v) := by
  rcases v with ⟨n, k⟩
  apply Sigma.ext
  · exact zeroDataPresentationEquiv_mirror Z Z' n
  · apply heq_of_eq
    apply Fin.ext
    rfl

private theorem presentationTransport_memℓp
    {I J : Type*} (e : I ≃ J) (psi : ObserverHilbertSpace I) :
    Memℓp (fun j => psi (e.symm j)) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  change Summable ((fun i => ‖psi i‖ ^ (2 : ENNReal).toReal) ∘ e.symm)
  exact e.symm.summable_iff.mpr
    ((memℓp_gen_iff (by norm_num)).mp psi.2)

private def presentationTransportVector
    {I J : Type*} (e : I ≃ J) (psi : ObserverHilbertSpace I) :
    ObserverHilbertSpace J :=
  ⟨fun j => psi (e.symm j), presentationTransport_memℓp e psi⟩

private theorem presentationTransportVector_norm
    {I J : Type*} (e : I ≃ J) (psi : ObserverHilbertSpace I) :
    ‖presentationTransportVector e psi‖ = ‖psi‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_sq_eq_re_inner (𝕜 := Complex) (presentationTransportVector e psi),
    norm_sq_eq_re_inner (𝕜 := Complex) psi]
  congr 1
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simpa only [presentationTransportVector, Subtype.coe_mk] using
    (e.symm.tsum_eq (fun i => inner (𝕜 := Complex) (psi i) (psi i)))

/-- The unitary reindexing between the multiplicity-expanded zero Hilbert
spaces of two valid presentations. -/
noncomputable def zeroHilbertPresentationUnitary (Z Z' : ZeroData) :
    MirrorZeroHilbertSpace Z ≃ₗᵢ[Complex] MirrorZeroHilbertSpace Z' where
  toFun := presentationTransportVector (zeroCoordinatePresentationEquiv Z Z')
  invFun := presentationTransportVector (zeroCoordinatePresentationEquiv Z Z').symm
  left_inv psi := by
    apply lp.ext
    funext v
    rfl
  right_inv psi := by
    apply lp.ext
    funext v
    rfl
  map_add' psi phi := by
    apply lp.ext
    funext v
    rfl
  map_smul' c psi := by
    apply lp.ext
    funext v
    rfl
  norm_map' := presentationTransportVector_norm
    (zeroCoordinatePresentationEquiv Z Z')

@[simp]
theorem zeroHilbertPresentationUnitary_apply (Z Z' : ZeroData)
    (psi : MirrorZeroHilbertSpace Z) (v : ZeroCoordinate Z') :
    zeroHilbertPresentationUnitary Z Z' psi v =
      psi ((zeroCoordinatePresentationEquiv Z Z').symm v) := rfl

/-- Presentation transport intertwines the mirror fundamental symmetries. -/
theorem zeroHilbertPresentationUnitary_intertwines_mirror
    (Z Z' : ZeroData) (psi : MirrorZeroHilbertSpace Z) :
    zeroHilbertPresentationUnitary Z Z'
        (mirrorFundamentalSymmetry Z psi) =
      mirrorFundamentalSymmetry Z'
        (zeroHilbertPresentationUnitary Z Z' psi) := by
  apply lp.ext
  funext v
  rw [zeroHilbertPresentationUnitary_apply,
    mirrorFundamentalSymmetry_apply,
    mirrorFundamentalSymmetry_apply,
    zeroHilbertPresentationUnitary_apply]
  congr 1
  apply (zeroCoordinatePresentationEquiv Z Z').injective
  rw [zeroCoordinatePresentationEquiv_mirror,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Presentation transport intertwines the diagonal zero Cayley operators. -/
theorem zeroHilbertPresentationUnitary_intertwines_cayley
    (Z Z' : ZeroData) (psi : MirrorZeroHilbertSpace Z) :
    zeroHilbertPresentationUnitary Z Z' (zeroCayleyOperator Z psi) =
      zeroCayleyOperator Z' (zeroHilbertPresentationUnitary Z Z' psi) := by
  apply lp.ext
  funext v
  rw [zeroHilbertPresentationUnitary_apply,
    zeroCayleyOperator_apply, zeroCayleyOperator_apply,
    zeroHilbertPresentationUnitary_apply]
  have hzero := zeroCoordinatePresentationEquiv_zero Z Z'
    ((zeroCoordinatePresentationEquiv Z Z').symm v)
  simp only [Equiv.apply_symm_apply] at hzero
  rw [hzero]

/-- The mirror Krein form is independent of the chosen `ZeroData`
presentation. -/
theorem zeroHilbertPresentationUnitary_preserves_krein
    (Z Z' : ZeroData) (psi phi : MirrorZeroHilbertSpace Z) :
    mirrorKreinForm Z'
        (zeroHilbertPresentationUnitary Z Z' psi)
        (zeroHilbertPresentationUnitary Z Z' phi) =
      mirrorKreinForm Z psi phi := by
  rw [mirrorKreinForm, mirrorKreinForm,
    ← zeroHilbertPresentationUnitary_intertwines_mirror]
  exact (zeroHilbertPresentationUnitary Z Z').inner_map_map psi
    (mirrorFundamentalSymmetry Z phi)

/-- The unique presentation transport simultaneously preserves zero labels,
analytic multiplicity, mirror geometry, Cayley dynamics, and the indefinite
inner product. -/
theorem zeroData_hilbert_presentation_transport_spec (Z Z' : ZeroData) :
    (∀ v : ZeroCoordinate Z,
      Z'.zero (zeroCoordinatePresentationEquiv Z Z' v).1 = Z.zero v.1) ∧
    (∀ psi : MirrorZeroHilbertSpace Z,
      zeroHilbertPresentationUnitary Z Z'
          (mirrorFundamentalSymmetry Z psi) =
        mirrorFundamentalSymmetry Z'
          (zeroHilbertPresentationUnitary Z Z' psi)) ∧
    (∀ psi : MirrorZeroHilbertSpace Z,
      zeroHilbertPresentationUnitary Z Z' (zeroCayleyOperator Z psi) =
        zeroCayleyOperator Z' (zeroHilbertPresentationUnitary Z Z' psi)) ∧
    (∀ psi phi : MirrorZeroHilbertSpace Z,
      mirrorKreinForm Z'
          (zeroHilbertPresentationUnitary Z Z' psi)
          (zeroHilbertPresentationUnitary Z Z' phi) =
        mirrorKreinForm Z psi phi) := by
  exact ⟨zeroCoordinatePresentationEquiv_zero Z Z',
    zeroHilbertPresentationUnitary_intertwines_mirror Z Z',
    zeroHilbertPresentationUnitary_intertwines_cayley Z Z',
    zeroHilbertPresentationUnitary_preserves_krein Z Z'⟩

#print axioms zeroCoordinatePresentationEquiv_mirror
#print axioms zeroHilbertPresentationUnitary_intertwines_mirror
#print axioms zeroHilbertPresentationUnitary_intertwines_cayley
#print axioms zeroHilbertPresentationUnitary_preserves_krein
#print axioms zeroData_hilbert_presentation_transport_spec

end D5.S3.Midline.Cayley.ZeroDataHilbertPresentationTransport
