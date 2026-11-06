/- GID: D5/S3/VertexAlgebra/Analysis/OriginalWeakSmearedLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalWeakSmearedLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original bounded and same-domain weak smeared locality. -/

import D5.S3.VertexAlgebra.Analysis.OriginalModeCommutator
import D5.S3.VertexAlgebra.Analysis.SmoothCircleContact

/-!
The formal adjoint and invariance facts are supplied by the existing
original_smooth_fields theorem.

All operators act on the existing Model, Sobolev, Smooth, and smoothDomain.
The two ordered source indices are identified with r+s+k by equality transport,
without a Sobolev inclusion or an increase in the domain's regularity.
The opposite-charge weak identity uses conjugate symmetry of the actual formal
adjoint identity; it does not posit an opposite involution.

proof_shape: original_smooth_fields_commute: content
admission_basis: escape-witness
escape_witness: The genuine-test contact theorem consumes the original bounded
mode commutator's transferred locality, polynomial growth, and absolute double
composition expansion; dependent family components then identify literal field
products on the existing invariant domain and give opposite-charge pairings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProductSpace Topology ComplexConjugate

namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing

open LatticeGeneratingFieldLocality SmoothCircleFourier Model

variable (M : Model)

/-- Every Sobolev layer, on the common source H_(order a + order b + k).
The exponent N may be zero and the charges and lattice rank may be zero. -/
theorem smearComposition_eq_reverse_of_disjoint_tsupport
    (a b : Charge M.D) (f g : Test)
    (hfg : Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift)) (k : ℕ) :
    M.smearComposition a b f g k = M.reverseSmearComposition a b f g k := by
  have hK : 0 ≤ 2 * M.modeConstant a * M.modeConstant b :=
    mul_nonneg (mul_nonneg (by norm_num) (modeConstant_pos M a).le)
      (modeConstant_pos M b).le
  apply sub_eq_zero.mp
  calc
    M.smearComposition a b f g k - M.reverseSmearComposition a b f g k =
        ∑' p : ℤ × ℤ, (f.coefficient p.1 * g.coefficient p.2) •
          M.modeCommutator a b k p.1 p.2 :=
      smear_comp_eq_double_tsum M a b f g k
    _ = 0 := FiniteDeltaContact.double_smear_eq_zero_of_disjoint_tsupport
      (M.modeCommutator a b k) (2 * M.modeConstant a * M.modeConstant b)
      (M.order a + M.order b + k) (-bilinear M.D a b).toNat hK
      (modeCommutator_norm M a b k) (modeCommutator_delta M a b k) f g hfg

/-- Dependent family evaluation commutes with source equality transport.
This uses equality of orders, rather than treating them as definitionally equal. -/
private theorem castSource_family {i j k : ℕ} (h : i = j)
    (A : M.Sobolev i →L[ℂ] M.Sobolev k) (x : M.Smooth) :
    M.castSource h A (x.1 j) = A (x.1 i) := by
  cases h
  rfl

/-- The first actual family composition uses s+(r+k), transported to R=r+s+k. -/
private theorem smearFamily_comp_component (a b : Charge M.D) (f g : Test)
    (x : M.Smooth) (k : ℕ) :
    (M.smearFamily a f (M.smearFamily b g x)).1 k =
      M.smearComposition a b f g k (x.1 (M.order a + M.order b + k)) := by
  change M.smear a f k
      (M.smear b g (M.order a + k) (x.1 (M.order b + (M.order a + k)))) = _
  exact (castSource_family M
    (by omega : M.order b + (M.order a + k) = M.order a + M.order b + k)
    ((M.smear a f k).comp (M.smear b g (M.order a + k))) x).symm

/-- The reverse actual family composition uses r+(s+k), on that same R. -/
private theorem reverseSmearFamily_comp_component (a b : Charge M.D) (f g : Test)
    (x : M.Smooth) (k : ℕ) :
    (M.smearFamily b g (M.smearFamily a f x)).1 k =
      M.reverseSmearComposition a b f g k (x.1 (M.order a + M.order b + k)) := by
  change M.smear b g k
      (M.smear a f (M.order b + k) (x.1 (M.order a + (M.order b + k)))) = _
  exact (castSource_family M
    (by omega : M.order a + (M.order b + k) = M.order a + M.order b + k)
    ((M.smear b g k).comp (M.smear a f (M.order b + k))) x).symm

/-- Commutation of the existing endomorphisms of the same compatible-family space. -/
theorem smearFamily_comp_eq_of_disjoint_tsupport
    (a b : Charge M.D) (f g : Test)
    (hfg : Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift)) :
    (M.smearFamily a f).comp (M.smearFamily b g) =
      (M.smearFamily b g).comp (M.smearFamily a f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext k
  change (M.smearFamily a f (M.smearFamily b g x)).1 k =
    (M.smearFamily b g (M.smearFamily a f x)).1 k
  rw [smearFamily_comp_component, reverseSmearFamily_comp_component,
    smearComposition_eq_reverse_of_disjoint_tsupport M a b f g hfg k]

/-- Transport an actual field image back to its existing compatible family.
The membership proof is immaterial; domainEquiv already contains the proved
injectivity of evaluation. This is not a new field or a replacement domain. -/
private theorem field_image_family (a : Charge M.D) (f : Test)
    (u : M.smoothDomain) (hu : M.field a f u ∈ M.smoothDomain) :
    M.domainEquiv.symm ⟨M.field a f u, hu⟩ =
      M.smearFamily a f (M.domainEquiv.symm u) := by
  apply M.domainEquiv.injective
  rw [M.domainEquiv.apply_symm_apply]
  apply Subtype.ext
  rfl

/-- Literal vector equality of field products. Invariance is supplied by the
existing public endpoint, not by an extra analytic assumption. -/
theorem field_comp_eq_of_disjoint_tsupport
    (a b : Charge M.D) (f g : Test)
    (hfg : Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift)) :
    let ha := ((original_smooth_fields M a).choose_spec.2 f).2.2.2.1
    let hb := ((original_smooth_fields M b).choose_spec.2 g).2.2.2.1
    ∀ u : M.smoothDomain,
      M.field a f ⟨M.field b g u, hb u⟩ =
        M.field b g ⟨M.field a f u, ha u⟩ := by
  dsimp only
  intro u
  change M.evaluation (M.smearFamily a f
      (M.domainEquiv.symm ⟨M.field b g u, _⟩)) =
    M.evaluation (M.smearFamily b g
      (M.domainEquiv.symm ⟨M.field a f u, _⟩))
  rw [field_image_family, field_image_family]
  exact congrArg (fun A : M.Smooth →ₗ[ℂ] M.Smooth =>
    M.evaluation (A (M.domainEquiv.symm u)))
      (smearFamily_comp_eq_of_disjoint_tsupport M a b f g hfg)

/-- Original weak smeared locality, including every bounded layer, the SAME
Smooth endomorphisms, literal field products, arbitrary H_0 test vectors, and
the actual opposite-charge form. No closure product occurs in this statement.
Here opposite(a,f) is exactly eta(a) * field(-a,f.conjugate), with the accepted
parity/cocycle sign and pointwise conjugation of the genuine periodic test. -/
theorem original_smooth_fields_commute
    (a b : Charge M.D) (f g : Test)
    (hfg : Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift)) :
    (∀ k : ℕ, M.smearComposition a b f g k =
      M.reverseSmearComposition a b f g k) ∧
    ((M.smearFamily a f).comp (M.smearFamily b g) =
      (M.smearFamily b g).comp (M.smearFamily a f)) ∧
    (let ha := ((original_smooth_fields M a).choose_spec.2 f).2.2.2.1
     let hb := ((original_smooth_fields M b).choose_spec.2 g).2.2.2.1
     ∀ u : M.smoothDomain,
       (M.field a f ⟨M.field b g u, hb u⟩ =
         M.field b g ⟨M.field a f u, ha u⟩) ∧
       (∀ y : M.Hilbert,
         ⟪y, M.field a f ⟨M.field b g u, hb u⟩⟫_ℂ =
           ⟪y, M.field b g ⟨M.field a f u, ha u⟩⟫_ℂ) ∧
       (∀ v : M.smoothDomain,
         ⟪M.opposite a f v, M.field b g u⟫_ℂ =
           ⟪M.opposite b g v, M.field a f u⟫_ℂ)) := by
  refine ⟨smearComposition_eq_reverse_of_disjoint_tsupport M a b f g hfg,
    smearFamily_comp_eq_of_disjoint_tsupport M a b f g hfg, ?_⟩
  dsimp only
  intro u
  let ub : M.smoothDomain := ⟨M.field b g u,
    ((original_smooth_fields M b).choose_spec.2 g).2.2.2.1 u⟩
  let ua : M.smoothDomain := ⟨M.field a f u,
    ((original_smooth_fields M a).choose_spec.2 f).2.2.2.1 u⟩
  have hvector : M.field a f ub = M.field b g ua :=
    field_comp_eq_of_disjoint_tsupport M a b f g hfg u
  refine ⟨hvector, ?_, ?_⟩
  · intro y
    exact congrArg (fun w : M.Hilbert => ⟪y, w⟫_ℂ) hvector
  · intro v
    have hformal_a : (M.field a f).IsFormalAdjoint (M.opposite a f) :=
      ((original_smooth_fields M a).choose_spec.2 f).2.2.2.2.1
    have hformal_b : (M.field b g).IsFormalAdjoint (M.opposite b g) :=
      ((original_smooth_fields M b).choose_spec.2 g).2.2.2.2.1
    have hpair_a := hformal_a ub v
    have hpair_b := hformal_b ua v
    calc
      ⟪M.opposite a f v, M.field b g u⟫_ℂ =
          ⟪(v : M.Hilbert), M.field a f ub⟫_ℂ := by
        simpa only [inner_conj_symm] using
          (congrArg (starRingEnd ℂ) hpair_a).symm
      _ = ⟪(v : M.Hilbert), M.field b g ua⟫_ℂ :=
        congrArg (fun w : M.Hilbert => ⟪(v : M.Hilbert), w⟫_ℂ) hvector
      _ = ⟪M.opposite b g v, M.field a f u⟫_ℂ := by
        simpa only [inner_conj_symm] using
          congrArg (starRingEnd ℂ) hpair_b

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing
