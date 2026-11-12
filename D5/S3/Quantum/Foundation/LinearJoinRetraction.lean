/- GID: D5/S3/Quantum/Foundation/LinearJoinRetraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/LinearJoinRetraction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Real rank one generated PSD sections localize to their supported sides and admit matrix congruence retractions along full projective overlaps. -/

import D5.S3.Quantum.Foundation.WeightedRelationConfirmation
import D5.S3.Quantum.Foundation.SectionROGFrame
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.CFC.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.LinearJoinRetraction

open CircuitBalancedConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-! ### The two sides of a linear join -/

/-- The cone and unit obtained by restricting the original carrier to a subspace. -/
def sideCone (C : PointedCone ℝ A) (U : Submodule ℝ A) : PointedCone ℝ U :=
  C.comap U.subtype

def sideUnit (u : A →ₗ[ℝ] ℝ) (U : Submodule ℝ A) : U →ₗ[ℝ] ℝ :=
  u.comp U.subtype

/-- A linear join with an explicit overlap projection on each side.  The two
projections are the abstract form of the orthogonal maps π_S used in (97.7).
The overlap equations make the glued maps independent of a chosen decomposition. -/
structure JoinData where
  leftSubspace : Submodule ℝ A
  rightSubspace : Submodule ℝ A
  overlapSubspace : Submodule ℝ A
  hSU : (overlapSubspace : Submodule ℝ A) ≤ leftSubspace
  hSW : (overlapSubspace : Submodule ℝ A) ≤ rightSubspace
  hjoin : leftSubspace ⊔ rightSubspace = ⊤
  hoverlap : leftSubspace ⊓ rightSubspace = overlapSubspace
  piY : rightSubspace →ₗ[ℝ] overlapSubspace
  piZ : leftSubspace →ₗ[ℝ] overlapSubspace
  piY_fix : ∀ s : overlapSubspace, piY (overlapSubspace.inclusion hSW s) = s
  piZ_fix : ∀ s : overlapSubspace, piZ (overlapSubspace.inclusion hSU s) = s

namespace JoinData

/-- The sum map from the two subspaces onto their linear join. -/
def sumMap (J : JoinData (A := A)) : J.leftSubspace × J.rightSubspace →ₗ[ℝ] A :=
  J.leftSubspace.subtype.coprod J.rightSubspace.subtype

private theorem sumMap_surjective (J : JoinData (A := A)) :
    Function.Surjective J.sumMap := by
  intro x
  obtain ⟨u, hu, w, hw, hsum⟩ :=
    (Submodule.sup_eq_top_iff J.leftSubspace J.rightSubspace).mp J.hjoin x
  refine ⟨(⟨u, hu⟩, ⟨w, hw⟩), ?_⟩
  simpa [sumMap, LinearMap.coprod_apply] using hsum.symm

private theorem left_kernel_compatibility (J : JoinData (A := A)) :
    LinearMap.ker J.sumMap ≤
      LinearMap.ker (LinearMap.id.coprod
        ((Submodule.inclusion J.hSU).comp J.piY)) := by
  intro x hx
  rcases x with ⟨u, w⟩
  have hsum : (u : A) + (w : A) = 0 := by
    change J.sumMap (u, w) = 0 at hx
    simpa [sumMap, LinearMap.coprod_apply] using hx
  have hwU : (w : A) ∈ J.leftSubspace := by
    have huU : (u : A) ∈ J.leftSubspace := u.property
    rw [eq_neg_of_add_eq_zero_right hsum]
    exact J.leftSubspace.neg_mem huU
  have hwS : (w : A) ∈ J.overlapSubspace := by
    rw [← J.hoverlap]
    exact ⟨hwU, w.property⟩
  let s : J.overlapSubspace := ⟨(w : A), hwS⟩
  have hsW : J.overlapSubspace.inclusion J.hSW s = w := by
    apply Subtype.ext
    rfl
  have hpi : J.piY w = s := by
    rw [← hsW]
    exact J.piY_fix s
  apply Subtype.ext
  change (u : A) + ((Submodule.inclusion J.hSU) (J.piY w) : A) = 0
  rw [hpi]
  change (u : A) + (J.overlapSubspace.inclusion J.hSW s : A) = 0
  have hsW' : ((J.overlapSubspace.inclusion J.hSW s : J.rightSubspace) : A) =
      (w : A) := congrArg (fun t : J.rightSubspace => (t : A)) hsW
  change (u : A) + (w : A) = 0
  exact hsum

/-- The left retraction (R_Y), obtained by gluing the identity on (U) to
(pi_S:W	o S). -/
def leftRetraction (J : JoinData (A := A)) : A →ₗ[ℝ] J.leftSubspace :=
  J.sumMap.liftOfSurjective (sumMap_surjective J)
    ⟨LinearMap.id.coprod ((Submodule.inclusion J.hSU).comp J.piY),
      left_kernel_compatibility J⟩

theorem leftRetraction_on_left (J : JoinData (A := A)) (x : J.leftSubspace) :
    J.leftRetraction (J.leftSubspace.subtype x) = x := by
  have h := LinearMap.equivOfSurjective_apply
    (sumMap_surjective J) (left_kernel_compatibility J)
      (m := (x, 0))
  simpa [leftRetraction, sumMap] using h

theorem leftRetraction_on_right (J : JoinData (A := A)) (x : J.rightSubspace) :
    J.leftRetraction (J.rightSubspace.subtype x) =
      Submodule.inclusion J.hSU (J.piY x) := by
  have h := LinearMap.equivOfSurjective_apply
    (sumMap_surjective J) (left_kernel_compatibility J)
      (m := (0, x))
  simpa [leftRetraction, sumMap] using h

end JoinData


open scoped Matrix RealInnerProductSpace
open SectionROGFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A projective join written on its full inverse images of nonzero vectors.
The matrix space L and the vector spaces U,W are different carriers. -/
structure RealJoin (ι : Type*) [Fintype ι] [DecidableEq ι] where
  L : Submodule ℝ (HermitianMat ι ℝ)
  identity_mem : (1 : HermitianMat ι ℝ) ∈ L
  rog : ROG L
  Y Z : Set (EuclideanSpace ℝ ι)
  U W : Submodule ℝ (EuclideanSpace ℝ ι)
  nonzero_Y : (0 : EuclideanSpace ℝ ι) ∉ Y
  nonzero_Z : (0 : EuclideanSpace ℝ ι) ∉ Z
  span_Y : Submodule.span ℝ Y = U
  span_Z : Submodule.span ℝ Z = W
  join : U ⊔ W = ⊤
  rays : ∀ v : EuclideanSpace ℝ ι, v ≠ 0 →
    (rankOne v ∈ L ↔ v ∈ Y ∨ v ∈ Z)
  overlap : Y ∩ Z = {v | v ≠ 0 ∧ v ∈ U ⊓ W}

namespace RealJoin

variable (J : RealJoin ι)

/-- Exchanging the two projective sides preserves the original matrix section. -/
def swap : RealJoin ι where
  L := J.L
  identity_mem := J.identity_mem
  rog := J.rog
  Y := J.Z
  Z := J.Y
  U := J.W
  W := J.U
  nonzero_Y := J.nonzero_Z
  nonzero_Z := J.nonzero_Y
  span_Y := J.span_Z
  span_Z := J.span_Y
  join := sup_comm J.U J.W ▸ J.join
  rays v hv := (J.rays v hv).trans or_comm
  overlap := by simpa [Set.inter_comm, inf_comm] using J.overlap

/-- The original matrix span of all rank one generators on Y. -/
def space : Submodule ℝ (HermitianMat ι ℝ) :=
  Submodule.span ℝ (rankOne '' J.Y)

/-- The full conic hull of those same generators. -/
def cone : PointedCone ℝ (HermitianMat ι ℝ) :=
  PointedCone.hull ℝ (rankOne '' J.Y)

private theorem vector_mem (v : EuclideanSpace ℝ ι) (hv : v ∈ J.Y) : v ∈ J.U := by
  rw [← J.span_Y]
  exact Submodule.subset_span hv

private theorem vector_ne (v : EuclideanSpace ℝ ι) (hv : v ∈ J.Y) : v ≠ 0 := by
  intro hz
  exact J.nonzero_Y (hz ▸ hv)


private theorem space_le : J.space ≤ J.L := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  exact (J.rays v (J.vector_ne v hv)).mpr (Or.inl hv)

/-- Orthogonal overlap projections supply the vector gluing data. -/
def vectorJoin : JoinData (A := EuclideanSpace ℝ ι) where
  leftSubspace := J.U
  rightSubspace := J.W
  overlapSubspace := J.U ⊓ J.W
  hSU := inf_le_left
  hSW := inf_le_right
  hjoin := J.join
  hoverlap := rfl
  piY := (J.U ⊓ J.W).orthogonalProjectionOnto.toLinearMap.comp J.W.subtype
  piZ := (J.U ⊓ J.W).orthogonalProjectionOnto.toLinearMap.comp J.U.subtype
  piY_fix s := by simpa using (J.U ⊓ J.W).orthogonalProjectionOnto_mem_subspace_eq_self s
  piZ_fix s := by simpa using (J.U ⊓ J.W).orthogonalProjectionOnto_mem_subspace_eq_self s

/-- T fixes U and is orthogonal projection to U intersect W on W. -/
def vectorMap : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
  J.U.subtype.comp J.vectorJoin.leftRetraction

private theorem vectorMap_on_Y (v : EuclideanSpace ℝ ι) (hv : v ∈ J.Y) :
    J.vectorMap v = v := by
  have h := J.vectorJoin.leftRetraction_on_left ⟨v, J.vector_mem v hv⟩
  exact congrArg (fun x : J.U => (x : EuclideanSpace ℝ ι)) h

private theorem vectorMap_on_W (v : EuclideanSpace ℝ ι) (hv : v ∈ J.W) :
    J.vectorMap v = (J.U ⊓ J.W).starProjection v := by
  have h := J.vectorJoin.leftRetraction_on_right ⟨v, hv⟩
  exact congrArg (fun x : J.U => (x : EuclideanSpace ℝ ι)) h

/-- The actual real matrix T, in the original normalized Euclidean coordinates. -/
def matrix : Matrix ι ι ℝ := Matrix.toEuclideanLin.symm J.vectorMap

/-- The ambient congruence X maps to T X T-transpose. -/
def congruence : HermitianMat ι ℝ →ₗ[ℝ] HermitianMat ι ℝ :=
  HermitianMat.conjLinear ℝ J.matrix

private theorem congruence_rankOne (v : EuclideanSpace ℝ ι) :
    J.congruence (rankOne v) = rankOne (J.vectorMap v) := by
  apply HermitianMat.ext
  change J.matrix * Matrix.vecMulVec (v : ι → ℝ) (star (v : ι → ℝ)) *
    J.matrix.conjTranspose =
      Matrix.vecMulVec (J.vectorMap v : ι → ℝ) (star (J.vectorMap v : ι → ℝ))
  have hv : J.matrix *ᵥ (v : ι → ℝ) = (J.vectorMap v : ι → ℝ) := by
    have h := congrArg (fun f : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι => f v)
      (Matrix.toEuclideanLin.apply_symm_apply J.vectorMap)
    exact congrArg WithLp.ofLp h
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  rw [← Matrix.star_mulVec, hv]

private theorem image_generator (v : EuclideanSpace ℝ ι)
    (hv : v ≠ 0) (hL : rankOne v ∈ J.L) :
    J.congruence (rankOne v) ∈ J.cone ∧
      (J.congruence (rankOne v)).trace ≤ (rankOne v).trace := by
  rw [J.congruence_rankOne]
  rcases (J.rays v hv).mp hL with hY | hZ
  · rw [J.vectorMap_on_Y v hY]
    exact ⟨PointedCone.subset_hull ⟨v, hY, rfl⟩, le_rfl⟩
  · have hW : v ∈ J.W := J.swap.vector_mem v hZ
    rw [J.vectorMap_on_W v hW]
    refine ⟨?_, ?_⟩
    · by_cases hz : (J.U ⊓ J.W).starProjection v = 0
      · simp [hz, rankOne, cone]
      · apply PointedCone.subset_hull
        refine ⟨(J.U ⊓ J.W).starProjection v, ?_, rfl⟩
        exact (show (J.U ⊓ J.W).starProjection v ∈ J.Y ∩ J.Z from by
          rw [J.overlap]
          exact ⟨hz, (J.U ⊓ J.W).starProjection_apply_mem v⟩).1
    · rw [rankOne_trace_norm, rankOne_trace_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) ((J.U ⊓ J.W).norm_starProjection_apply_le v) 2

/-- Every original positive matrix is mapped into the actual Y cone, and its
trace decreases, using its same finite original ROG decomposition. -/
theorem congruence_positive_subunit (X : HermitianMat ι ℝ)
    (hX : X ∈ J.L) (hpos : 0 ≤ X) :
    J.congruence X ∈ J.cone ∧ (J.congruence X).trace ≤ X.trace := by
  obtain ⟨m, v, hv, hsum⟩ := J.rog X hX hpos
  rw [hsum, map_sum]
  refine ⟨J.cone.sum_mem (fun i _ => (J.image_generator (v i) (hv i).1 (hv i).2).1), ?_⟩
  simp only [← HermitianMat.one_inner, inner_sum]
  exact Finset.sum_le_sum (fun i _ => (J.image_generator (v i) (hv i).1 (hv i).2).2)


/-- Symmetric matrices whose entire range is contained in the vector space U. -/
def supportedSpace (U : Submodule ℝ (EuclideanSpace ℝ ι)) :
    Submodule ℝ (HermitianMat ι ℝ) where
  carrier := {X | ∀ v, X.lin v ∈ U}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY v
    simpa [HermitianMat.lin, Matrix.toLpLin_apply, Matrix.add_mulVec] using U.add_mem (hX v) (hY v)
  smul_mem' := by
    intro r X hX v
    simpa [HermitianMat.lin, Matrix.toLpLin_apply, Matrix.smul_mulVec] using U.smul_mem r (hX v)

private theorem rankOne_supported (v : EuclideanSpace ℝ ι)
    {U : Submodule ℝ (EuclideanSpace ℝ ι)} (hv : v ∈ U) :
    rankOne v ∈ supportedSpace U := by
  intro x
  have h := U.smul_mem ((star (v : ι → ℝ)) ⬝ᵥ (x : ι → ℝ)) hv
  simpa [HermitianMat.lin, rankOne, Matrix.toLpLin_apply,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul] using h

private theorem space_supported : J.space ≤ supportedSpace J.U := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  exact rankOne_supported v (J.vector_mem v hv)

private theorem rankOne_support_self (v : EuclideanSpace ℝ ι) (hv : v ≠ 0) :
    v ∈ (rankOne v).support := by
  have hnorm : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  refine ⟨(‖v‖ ^ 2)⁻¹ • v, ?_⟩
  change (rankOne v).lin ((‖v‖ ^ 2)⁻¹ • v) = v
  rw [map_smul]
  have heval : (rankOne v).lin v = (‖v‖ ^ 2) • v := by
    apply WithLp.ofLp_injective
    simp only [HermitianMat.lin, rankOne, Matrix.toLpLin_apply,
      ContinuousLinearMap.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      real_inner_self_eq_norm_sq]
    rfl
  rw [heval, smul_smul, inv_mul_cancel₀ hnorm, one_smul]

/-- Every nonzero vector in a positive rank one summand belongs to the range
of its PSD sum. The order relation is obtained from that very decomposition. -/
private theorem summand_supported {m : ℕ} (v : Fin m → EuclideanSpace ℝ ι)
    (i : Fin m) (hi : v i ≠ 0) :
    v i ∈ (∑ j, rankOne (v j)).support := by
  have hle : rankOne (v i) ≤ ∑ j, rankOne (v j) :=
    Finset.single_le_sum (fun j _ => rankOne_nonneg (v j)) (Finset.mem_univ i)
  have hker := HermitianMat.ker_antitone (rankOne_nonneg (v i)) hle
  have hs : (rankOne (v i)).support ≤ (∑ j, rankOne (v j)).support := by
    rw [← HermitianMat.ker_orthogonal_eq_support, ← HermitianMat.ker_orthogonal_eq_support]
    exact Submodule.orthogonal_le hker
  exact hs (rankOne_support_self (v i) hi)

/-- The actual supported PSD section, and not merely an image cone, is exactly
Y's conic hull. Every term of a supported original ROG decomposition lies on Y. -/
theorem supported_cone (X : HermitianMat ι ℝ) :
    X ∈ J.cone ↔ X ∈ J.L ∧ 0 ≤ X ∧ X.support ≤ J.U := by
  constructor
  · intro hX
    refine ⟨J.space_le (PointedCone.hull_le_span ℝ _ hX), ?_, ?_⟩
    · have hcone : J.cone ≤ PointedCone.positive ℝ (HermitianMat ι ℝ) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨v, hv, rfl⟩
        exact rankOne_nonneg v
      exact hcone hX
    · exact J.space_supported (PointedCone.hull_le_span ℝ _ hX)
  · rintro ⟨hL, hpos, hsupp⟩
    obtain ⟨m, v, hv, hsum⟩ := J.rog X hL hpos
    have hY (i : Fin m) : v i ∈ J.Y := by
      have hiU : v i ∈ J.U := hsupp (hsum ▸ summand_supported v i (hv i).1)
      rcases (J.rays (v i) (hv i).1).mp (hv i).2 with hiY | hiZ
      · exact hiY
      · have hiS : v i ∈ J.U ⊓ J.W := ⟨hiU, J.swap.vector_mem _ hiZ⟩
        exact (show v i ∈ J.Y ∩ J.Z from by rw [J.overlap]; exact ⟨(hv i).1, hiS⟩).1
    rw [hsum]
    exact J.cone.sum_mem (fun i _ => PointedCone.subset_hull ⟨v i, hY i, rfl⟩)

/-- The full section on L_Y equals the original supported cone. -/
theorem section_cone (X : HermitianMat ι ℝ) :
    X ∈ J.cone ↔ X ∈ J.space ∧ 0 ≤ X := by
  constructor
  · intro hX
    exact ⟨PointedCone.hull_le_span ℝ _ hX, (J.supported_cone X).mp hX |>.2.1⟩
  · rintro ⟨hX, hpos⟩
    exact (J.supported_cone X).mpr ⟨J.space_le hX, hpos, J.space_supported hX⟩

/-- The actual side remains a real rank one generated PSD section. -/
theorem side_rog : ROG J.space := by
  intro X hX hpos
  obtain ⟨m, v, hv, hsum⟩ := J.rog X (J.space_le hX) hpos
  refine ⟨m, v, ?_, hsum⟩
  intro i
  refine ⟨(hv i).1, ?_⟩
  have hsupp : (rankOne (v i)).support ≤ J.U := by
    have hle : rankOne (v i) ≤ X := by
      rw [hsum]
      exact Finset.single_le_sum (fun j _ => rankOne_nonneg (v j)) (Finset.mem_univ i)
    have hker := HermitianMat.ker_antitone (rankOne_nonneg (v i)) hle
    apply le_trans _ (J.space_supported hX)
    rw [← HermitianMat.ker_orthogonal_eq_support, ← HermitianMat.ker_orthogonal_eq_support]
    exact Submodule.orthogonal_le hker
  exact PointedCone.hull_le_span ℝ _
    ((J.supported_cone _).mpr ⟨(hv i).2, rankOne_nonneg _, hsupp⟩)

end RealJoin
end D5.S3.Quantum.Foundation.LinearJoinRetraction
