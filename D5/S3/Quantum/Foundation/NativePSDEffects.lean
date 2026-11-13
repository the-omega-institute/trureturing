/- GID: D5/S3/Quantum/Foundation/NativePSDEffects
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/NativePSDEffects
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole native PSD effects and mixed exclusions retain the entire real dual. -/

import D5.S3.Quantum.Foundation.RegularAnchorNormalChart
import D5.S3.Quantum.Foundation.SectionROGFrame
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.States.Mixed.MState
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The carrier is the full real space of complex Hermitian matrices. Effects
range over every real linear functional, and exclusions over every density matrix. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace Matrix ComplexOrder

namespace D5.S3.Quantum.Foundation.NativePSDEffects

open CircuitBalancedConfirmation FacetZeroGluing OrthogonalJointCompletion
open RegularAnchorNormalChart SectionROGFrame

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The entire PSD cone on the native Hermitian real carrier. -/
abbrev cone : PointedCone ℝ (HermitianMat d ℂ) :=
  PointedCone.positive ℝ (HermitianMat d ℂ)

/-- The real trace unit. -/
def unit : HermitianMat d ℂ →ₗ[ℝ] ℝ := HermitianMat.innerₗ 1

/-- The real trace pairing, defined on the entire original carrier. -/
def effect (E : HermitianMat d ℂ) : HermitianMat d ℂ →ₗ[ℝ] ℝ :=
  HermitianMat.innerₗ E

private theorem unit_apply (X : HermitianMat d ℂ) : unit X = X.trace :=
  HermitianMat.one_inner X

private theorem effect_apply (E X : HermitianMat d ℂ) : effect E X = ⟪E, X⟫ := rfl

private theorem effect_surjective : Function.Surjective (effect (d := d)) := by
  intro f
  refine ⟨(InnerProductSpace.toDual ℝ (HermitianMat d ℂ)).symm
    f.toContinuousLinearMap, ?_⟩
  ext X
  exact InnerProductSpace.toDual_symm_apply

private theorem effect_injective : Function.Injective (effect (d := d)) := by
  intro A B h
  apply ext_inner_right ℝ
  intro X
  exact LinearMap.congr_fun h X

private theorem proper_iff (E : HermitianMat d ℂ) :
    proper cone unit (effect E) ↔ 0 ≤ E ∧ E ≤ 1 := by
  constructor
  · intro h
    refine ⟨(HermitianMat.nonneg_iff_inner_nonneg E).2 (fun X hX => (h X hX).1), ?_⟩
    apply sub_nonneg.mp
    apply (HermitianMat.nonneg_iff_inner_nonneg (1 - E)).2
    intro X hX
    have hh := (h X hX).2
    simpa [effect_apply, unit_apply, inner_sub_left, HermitianMat.one_inner]
      using sub_nonneg.mpr hh
  · rintro ⟨hE, hI⟩ X hX
    refine ⟨HermitianMat.inner_ge_zero hE hX, ?_⟩
    simpa [effect_apply, unit_apply, HermitianMat.one_inner] using
      HermitianMat.inner_mono' hX hI

private theorem base_iff (X : HermitianMat d ℂ) :
    X ∈ CircuitBalancedConfirmation.base cone unit ↔ 0 ≤ X ∧ X.trace = 1 := by
  simp only [CircuitBalancedConfirmation.base, Set.mem_setOf_eq,
    PointedCone.mem_positive, unit_apply]

private theorem cone_closed : IsClosed (cone (d := d) : Set (HermitianMat d ℂ)) := by
  change IsClosed {X : HermitianMat d ℂ | 0 ≤ X}
  exact HermitianMat.isClosed_nonneg

private theorem unit_strict (X : HermitianMat d ℂ) (hX : X ∈ cone) (hne : X ≠ 0) :
    0 < unit X := by
  rw [unit_apply]
  exact HermitianMat.trace_pos (lt_of_le_of_ne hX (Ne.symm hne))

private theorem cone_generating :
    Submodule.span ℝ (cone (d := d) : Set (HermitianMat d ℂ)) = ⊤ := by
  apply top_unique
  intro X _
  rw [← HermitianMat.posPart_add_negPart X]
  exact Submodule.sub_mem _
    (Submodule.subset_span (HermitianMat.posPart_nonneg X))
    (Submodule.subset_span (HermitianMat.negPart_nonneg X))

private theorem rank_one_self (v : EuclideanSpace ℂ d) (hv : ‖v‖ = 1) :
    (rankOne v).mat * (rankOne v).mat = (rankOne v).mat := by
  change Matrix.vecMulVec (v : d → ℂ) (star (v : d → ℂ)) *
    Matrix.vecMulVec (v : d → ℂ) (star (v : d → ℂ)) = _
  rw [Matrix.vecMulVec_mul_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct]
  have hn : ⟪v, v⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hv]
    norm_num
  rw [hn, one_smul]

/-- A confirming positive contraction dominates the confirmed unit projection.
The proof constructs its positive complementary block on the same carrier. -/
theorem confirming_dominates (v : EuclideanSpace ℂ d) (hv : ‖v‖ = 1)
    (E : HermitianMat d ℂ) (hE : 0 ≤ E) (hI : E ≤ 1)
    (hconfirm : ⟪E, rankOne v⟫ = 1) : rankOne v ≤ E := by
  let P := rankOne v
  have hPtr : P.trace = 1 := by
    dsimp [P]
    rw [rankOne_trace_norm, hv]
    norm_num
  have hzero : ⟪1 - E, P⟫_ℝ = 0 := by
    rw [inner_sub_left, HermitianMat.one_inner, hPtr, hconfirm]
    ring
  have hmul : (1 - E).mat * P.mat = 0 := by
    have hz := (HermitianMat.inner_zero_iff (sub_nonneg.mpr hI)
      (rankOne_nonneg v)).mp hzero
    rw [← LinearMap.range_le_ker_iff] at hz
    exact Matrix.toEuclideanLin.injective hz
  have hEP : E.mat * P.mat = P.mat := by
    simpa [HermitianMat.mat_sub, Matrix.sub_mul, HermitianMat.mat_one,
      sub_eq_zero] using hmul
  have hPE : P.mat * E.mat = P.mat := by
    have hh := congrArg Matrix.conjTranspose hEP
    simpa [Matrix.conjTranspose_mul] using hh
  have hblock : E.conj (1 - P.mat) = E - P := by
    apply HermitianMat.ext
    change (1 - P.mat) * E.mat * (1 - P.mat).conjTranspose = E.mat - P.mat
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, P.H,
      Matrix.sub_mul, Matrix.one_mul, hPE, Matrix.mul_sub,
      Matrix.mul_one, hEP, Matrix.sub_mul, Matrix.mul_one,
      rank_one_self v hv]
    abel
  have hp := HermitianMat.conj_nonneg (M := 1 - P.mat) hE
  rw [hblock] at hp
  exact sub_nonneg.mp hp

end D5.S3.Quantum.Foundation.NativePSDEffects
