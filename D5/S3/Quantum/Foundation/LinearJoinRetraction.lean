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

/-! Matrix congruences on full real ROG sections and their complete effect intervals. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.LinearJoinRetraction

open CircuitBalancedConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-! ### The two sides of a linear join -/

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
  piY_fix : ∀ s : overlapSubspace, piY (overlapSubspace.inclusion hSW s) = s

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

private theorem leftRetraction_on_left (J : JoinData (A := A)) (x : J.leftSubspace) :
    J.leftRetraction (J.leftSubspace.subtype x) = x := by
  have h := LinearMap.equivOfSurjective_apply
    (sumMap_surjective J) (left_kernel_compatibility J)
      (m := (x, 0))
  simpa [leftRetraction, sumMap] using h

private theorem leftRetraction_on_right (J : JoinData (A := A)) (x : J.rightSubspace) :
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
  Y : Set (EuclideanSpace ℝ ι)
  Z : Set (EuclideanSpace ℝ ι)
  U : Submodule ℝ (EuclideanSpace ℝ ι)
  W : Submodule ℝ (EuclideanSpace ℝ ι)
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
  piY_fix s := by simpa using (J.U ⊓ J.W).orthogonalProjectionOnto_mem_subspace_eq_self s

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
private theorem congruence_positive_subunit (X : HermitianMat ι ℝ)
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
  carrier := {X | X.support ≤ U}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY z hz
    obtain ⟨v, rfl⟩ := hz
    have hx : X.lin v ∈ U := hX ⟨v, rfl⟩
    have hy : Y.lin v ∈ U := hY ⟨v, rfl⟩
    simpa [HermitianMat.lin, Matrix.toLpLin_apply, Matrix.add_mulVec] using U.add_mem hx hy
  smul_mem' := by
    intro r X hX z hz
    obtain ⟨v, rfl⟩ := hz
    have hx : X.lin v ∈ U := hX ⟨v, rfl⟩
    simpa [HermitianMat.lin, Matrix.toLpLin_apply, Matrix.smul_mulVec] using U.smul_mem r hx

private theorem rankOne_supported (v : EuclideanSpace ℝ ι)
    {U : Submodule ℝ (EuclideanSpace ℝ ι)} (hv : v ∈ U) :
    rankOne v ∈ supportedSpace U := by
  intro z hz
  obtain ⟨x, rfl⟩ := hz
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
private theorem supported_cone (X : HermitianMat ι ℝ) :
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
      have hiU : v i ∈ J.U := hsupp (by rw [hsum]; exact summand_supported v i (hv i).1)
      rcases (J.rays (v i) (hv i).1).mp (hv i).2 with hiY | hiZ
      · exact hiY
      · have hiS : v i ∈ J.U ⊓ J.W := ⟨hiU, J.swap.vector_mem _ hiZ⟩
        exact (show v i ∈ J.Y ∩ J.Z from by rw [J.overlap]; exact ⟨(hv i).1, hiS⟩).1
    rw [hsum]
    exact J.cone.sum_mem (fun i _ => PointedCone.subset_hull ⟨v i, hY i, rfl⟩)

/-- The full section on L_Y equals the original supported cone. -/
private theorem section_cone (X : HermitianMat ι ℝ) :
    X ∈ J.cone ↔ X ∈ J.space ∧ 0 ≤ X := by
  constructor
  · intro hX
    exact ⟨PointedCone.hull_le_span ℝ _ hX, (J.supported_cone X).mp hX |>.2.1⟩
  · rintro ⟨hX, hpos⟩
    exact (J.supported_cone X).mpr ⟨J.space_le hX, hpos, J.space_supported hX⟩

/-- The actual side remains a real rank one generated PSD section. -/
private theorem side_rog : ROG J.space := by
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


private theorem congruence_fixes {X : HermitianMat ι ℝ} (hX : X ∈ J.space) :
    J.congruence X = X := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hX
  · rintro _ ⟨v, hv, rfl⟩
    rw [J.congruence_rankOne, J.vectorMap_on_Y v hv]
  · exact map_zero _
  · intro X Y _ _ hx hy
    rw [map_add, hx, hy]
  · intro r X _ hx
    rw [map_smul, hx]

private theorem carrier_image {X : HermitianMat ι ℝ} (hX : X ∈ J.L) :
    J.congruence X ∈ J.space := by
  let t : ℝ := ‖-X‖
  have hbound : -X ≤ t • (1 : HermitianMat ι ℝ) :=
    HermitianMat.lt_smul_of_norm_lt (le_refl _)
  have hp : 0 ≤ X + t • (1 : HermitianMat ι ℝ) := by order
  have hn : 0 ≤ t • (1 : HermitianMat ι ℝ) := smul_nonneg (norm_nonneg _) (by positivity)
  have htL : t • (1 : HermitianMat ι ℝ) ∈ J.L := J.L.smul_mem t J.identity_mem
  have hpc := (J.congruence_positive_subunit _ (J.L.add_mem hX htL) hp).1
  have hnc := (J.congruence_positive_subunit _ htL hn).1
  have hh := J.space.sub_mem (PointedCone.hull_le_span ℝ _ hpc)
    (PointedCone.hull_le_span ℝ _ hnc)
  simpa only [← map_sub, add_sub_cancel_right] using hh

/-- The actual congruence restricted from L to L_Y. -/
def retraction : J.L →ₗ[ℝ] J.space :=
  (J.congruence.comp J.L.subtype).codRestrict J.space (fun X => J.carrier_image X.property)

/-- Inclusion of the actual side into the unchanged original matrix section. -/
def inclusion : J.space →ₗ[ℝ] J.L := Submodule.inclusion J.space_le

private theorem retraction_fixes (X : J.space) : J.retraction (J.inclusion X) = X := by
  apply Subtype.ext
  exact J.congruence_fixes X.property

end RealJoin

/-- The entire original positive cone on a specified matrix section. -/
def sectionCone (L : Submodule ℝ (HermitianMat ι ℝ)) : PointedCone ℝ L :=
  (PointedCone.positive ℝ (HermitianMat ι ℝ)).comap L.subtype

/-- The same original trace unit restricted to the specified section. -/
def traceUnit (L : Submodule ℝ (HermitianMat ι ℝ)) : L →ₗ[ℝ] ℝ where
  toFun X := X.val.trace
  map_add' X Y := HermitianMat.trace_add _ _
  map_smul' r X := HermitianMat.trace_smul _ _

namespace RealJoin
variable (J : RealJoin ι)

/-- Every local proper effect extends along the actual matrix congruence. -/
private theorem effect_extension (g : J.space →ₗ[ℝ] ℝ)
    (hg : proper (sectionCone J.space) (traceUnit J.space) g) :
    proper (sectionCone J.L) (traceUnit J.L) (g.comp J.retraction) ∧
      (g.comp J.retraction).comp J.inclusion = g := by
  refine ⟨?_, ?_⟩
  · intro X hX
    have hx : 0 ≤ X.val := hX
    have hR := J.congruence_positive_subunit X.val X.property hx
    have hgR := hg (J.retraction X) ((J.section_cone _).mp hR.1).2
    exact ⟨hgR.1, hgR.2.trans hR.2⟩
  · ext X
    change g (J.retraction (J.inclusion X)) = g X
    rw [J.retraction_fixes]

/-- Restriction onto the whole local proper interval is surjective. -/
private theorem effect_onto (g : J.space →ₗ[ℝ] ℝ)
    (hg : proper (sectionCone J.space) (traceUnit J.space) g) :
    ∃ f : J.L →ₗ[ℝ] ℝ, proper (sectionCone J.L) (traceUnit J.L) f ∧
      f.comp J.inclusion = g :=
  ⟨g.comp J.retraction, J.effect_extension g hg⟩


private theorem restrict_proper (f : J.L →ₗ[ℝ] ℝ)
    (hf : proper (sectionCone J.L) (traceUnit J.L) f) :
    proper (sectionCone J.space) (traceUnit J.space) (f.comp J.inclusion) := by
  intro X hX
  exact hf (J.inclusion X) hX

/-- The full sets of confirming-effect readings agree for every local reference
and every local matrix, including all mixed states. In particular their infima agree. -/
private theorem comparison_exact (p x : J.space) :
    comparison (sectionCone J.L) (traceUnit J.L) (J.inclusion p) (J.inclusion x) =
      comparison (sectionCone J.space) (traceUnit J.space) p x := by
  unfold comparison
  congr 1
  ext r
  constructor
  · rintro ⟨f, hf, hfx⟩
    exact ⟨f.comp J.inclusion, ⟨J.restrict_proper f hf.1, hf.2⟩, hfx⟩
  · rintro ⟨g, hg, hgx⟩
    refine ⟨g.comp J.retraction, ⟨(J.effect_extension g hg.1).1, ?_⟩, ?_⟩
    · change g (J.retraction (J.inclusion p)) = 1
      rw [J.retraction_fixes, hg.2]
    · change g (J.retraction (J.inclusion x)) = r
      rw [J.retraction_fixes, hgx]

/-- Every local normalized native rank one pure point is the identical original
pure point, by inclusion into the original matrix section. -/
private theorem pure_inclusion (p : J.space) (hp : p.val ∈ pureRanks J.space) :
    (J.inclusion p).val ∈ pureRanks J.L := by
  obtain ⟨v, hv, heq, hmem⟩ := hp
  exact ⟨v, hv, heq, J.space_le hmem⟩

end RealJoin

private theorem proper_norm_bound
    (L : Submodule ℝ (HermitianMat ι ℝ)) (hI : (1 : HermitianMat ι ℝ) ∈ L)
    (f : StrongDual ℝ L) (hf : proper (sectionCone L) (traceUnit L) f.toLinearMap) :
    ‖f‖ ≤ (Fintype.card ι : ℝ) := by
  let I : L := ⟨1, hI⟩
  have hIpos : I ∈ sectionCone L := by change 0 ≤ (1 : HermitianMat ι ℝ); positivity
  have hfI : f I ≤ (Fintype.card ι : ℝ) := by
    simpa [traceUnit, I] using (hf I hIpos).2
  apply f.opNorm_le_bound (Nat.cast_nonneg _)
  intro X
  let t : ℝ := ‖X.val‖
  have hup : X.val ≤ t • (1 : HermitianMat ι ℝ) :=
    HermitianMat.lt_smul_of_norm_lt (le_refl _)
  have hlo : -X.val ≤ t • (1 : HermitianMat ι ℝ) :=
    HermitianMat.lt_smul_of_norm_lt (by simp [t])
  have hplus : t • I + X ∈ sectionCone L := by
    change 0 ≤ t • (1 : HermitianMat ι ℝ) + X.val
    order
  have hminus : t • I - X ∈ sectionCone L := by
    change 0 ≤ t • (1 : HermitianMat ι ℝ) - X.val
    exact sub_nonneg.mpr hup
  have h1 := (hf (t • I + X) hplus).1
  have h2 := (hf (t • I - X) hminus).1
  change 0 ≤ f (t • I + X) at h1
  change 0 ≤ f (t • I - X) at h2
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at h1 h2
  have hb := mul_le_mul_of_nonneg_left hfI (norm_nonneg X.val)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> change _ ≤ _ <;> dsimp [t] at * <;> nlinarith

private theorem proper_compact
    (L : Submodule ℝ (HermitianMat ι ℝ)) (hI : (1 : HermitianMat ι ℝ) ∈ L) :
    IsCompact {f : StrongDual ℝ L |
      proper (sectionCone L) (traceUnit L) f.toLinearMap} := by
  have hclosed : IsClosed {f : StrongDual ℝ L |
      proper (sectionCone L) (traceUnit L) f.toLinearMap} := by
    change IsClosed (⋂ X : L, ⋂ (_ : X ∈ sectionCone L),
      {f : StrongDual ℝ L | 0 ≤ f X ∧ f X ≤ traceUnit L X})
    apply isClosed_iInter
    intro X
    apply isClosed_iInter
    intro _
    exact (isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le (by fun_prop) continuous_const)
  apply (isCompact_closedBall (0 : StrongDual ℝ L) (Fintype.card ι)).of_isClosed_subset hclosed
  intro f hf
  simpa using proper_norm_bound L hI f hf

/-- On the full original proper interval, the native infimum is a minimum.
Every comparison-zero statement has one confirming effect with reading zero. -/
private theorem comparison_attained
    (L : Submodule ℝ (HermitianMat ι ℝ)) (hI : (1 : HermitianMat ι ℝ) ∈ L)
    (p x : L) (hp : traceUnit L p = 1) (hx : x ∈ sectionCone L) :
    ∃ f : L →ₗ[ℝ] ℝ, confirms (sectionCone L) (traceUnit L) p f ∧
      f x = comparison (sectionCone L) (traceUnit L) p x := by
  let F : Set (StrongDual ℝ L) := {f | proper (sectionCone L) (traceUnit L) f.toLinearMap ∧ f p = 1}
  have hcompact : IsCompact F := (proper_compact L hI).inter_right
    (isClosed_eq (by fun_prop) continuous_const)
  have hunit : (traceUnit L).toContinuousLinearMap ∈ F := by
    refine ⟨?_, hp⟩
    intro X hX
    exact ⟨HermitianMat.trace_nonneg hX, le_rfl⟩
  obtain ⟨f, hf, hmin⟩ := hcompact.exists_isMinOn ⟨_, hunit⟩ (show ContinuousOn (fun g : StrongDual ℝ L => g x) F by fun_prop)
  refine ⟨f.toLinearMap, hf, ?_⟩
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨f.toLinearMap, hf, rfl⟩, ?_⟩
  rintro r ⟨g, hg, rfl⟩
  exact hmin (show g.toContinuousLinearMap ∈ F from hg)

/-- The native zero relation is exactly a proper effect confirming p at one
and vanishing at x. The zero effect cannot satisfy this test. -/
private theorem comparison_zero_iff
    (L : Submodule ℝ (HermitianMat ι ℝ)) (hI : (1 : HermitianMat ι ℝ) ∈ L)
    (p x : L) (hp : traceUnit L p = 1) (hx : x ∈ sectionCone L) :
    comparison (sectionCone L) (traceUnit L) p x = 0 ↔
      ∃ f : L →ₗ[ℝ] ℝ, confirms (sectionCone L) (traceUnit L) p f ∧ f x = 0 := by
  constructor
  · intro h
    obtain ⟨f, hf, hfx⟩ := comparison_attained L hI p x hp hx
    exact ⟨f, hf, hfx.trans h⟩
  · rintro ⟨f, hf, hfx⟩
    apply le_antisymm
    · apply csInf_le
      · exact ⟨0, by rintro r ⟨g, hg, rfl⟩; exact (hg.1 x hx).1⟩
      · exact ⟨f, hf, hfx⟩
    · apply le_csInf
      · exact ⟨0, f, hf, hfx⟩
      · rintro r ⟨g, hg, rfl⟩
        exact (hg.1 x hx).1

/-- Native G2 uses comparison equal to zero over the entire proper interval.
The pure carrier is the full original normalized rank one set; ROG identifies
it with the extreme points of the entire normalized PSD base. -/
def nativeG2 (L : Submodule ℝ (HermitianMat ι ℝ)) : Prop :=
  ∀ p q r : L, p.val ∈ pureRanks L → q.val ∈ pureRanks L → r.val ∈ pureRanks L →
    comparison (sectionCone L) (traceUnit L) p q = 0 →
    comparison (sectionCone L) (traceUnit L) p r = 0 →
    comparison (sectionCone L) (traceUnit L) p ((1 / 2 : ℝ) • (q + r)) = 0

namespace RealJoin
variable (J : RealJoin ι)

private theorem local_attainment (p x : J.space)
    (hp : traceUnit J.space p = 1) (hx : x ∈ sectionCone J.space) :
    ∃ g : J.space →ₗ[ℝ] ℝ, confirms (sectionCone J.space) (traceUnit J.space) p g ∧
      g x = comparison (sectionCone J.space) (traceUnit J.space) p x := by
  obtain ⟨f, hf, hfx⟩ := comparison_attained J.L J.identity_mem
    (J.inclusion p) (J.inclusion x) hp hx
  exact ⟨f.comp J.inclusion, ⟨J.restrict_proper f hf.1, hf.2⟩,
    hfx.trans (J.comparison_exact p x)⟩

private theorem local_zero_iff (p x : J.space)
    (hp : traceUnit J.space p = 1) (hx : x ∈ sectionCone J.space) :
    comparison (sectionCone J.space) (traceUnit J.space) p x = 0 ↔
      ∃ g : J.space →ₗ[ℝ] ℝ, confirms (sectionCone J.space) (traceUnit J.space) p g ∧
        g x = 0 := by
  rw [← J.comparison_exact]
  rw [comparison_zero_iff J.L J.identity_mem (J.inclusion p) (J.inclusion x) hp hx]
  constructor
  · rintro ⟨f, hf, hfx⟩
    exact ⟨f.comp J.inclusion, ⟨J.restrict_proper f hf.1, hf.2⟩, hfx⟩
  · rintro ⟨g, hg, hgx⟩
    refine ⟨g.comp J.retraction, ⟨(J.effect_extension g hg.1).1, ?_⟩, ?_⟩
    · change g (J.retraction (J.inclusion p)) = 1
      rw [J.retraction_fixes, hg.2]
    · change g (J.retraction (J.inclusion x)) = 0
      rw [J.retraction_fixes, hgx]

/-- The native all-pure midpoint law is inherited by the entire supported side,
with the original trace and the full proper interval on both carriers. -/
private theorem native_G2_inherits (hG : nativeG2 J.L) : nativeG2 J.space := by
  intro p q r hp hq hr hpq hpr
  have h := hG (J.inclusion p) (J.inclusion q) (J.inclusion r)
    (J.pure_inclusion p hp) (J.pure_inclusion q hq) (J.pure_inclusion r hr)
    ((J.comparison_exact p q).trans hpq) ((J.comparison_exact p r).trans hpr)
  rw [← J.comparison_exact]
  simpa using h


/-- The whole supported-side conclusion, on the unchanged matrix and trace
carriers. All effects and all pure and mixed matrices are quantified here. -/
def SideConclusion : Prop :=
  (∀ X : HermitianMat ι ℝ, X ∈ J.cone ↔ X ∈ J.L ∧ 0 ≤ X ∧ X.support ≤ J.U) ∧
  (∀ X : HermitianMat ι ℝ, X ∈ J.cone ↔ X ∈ J.space ∧ 0 ≤ X) ∧
  ROG J.space ∧
  (SectionROGFrame.base J.space).extremePoints ℝ = pureRanks J.space ∧
  (∀ p : J.space, p.val ∈ pureRanks J.space →
    (J.inclusion p).val ∈ pureRanks J.L) ∧
  (∃ R : J.L →ₗ[ℝ] J.space,
    (∀ X : J.L, (R X).val = X.val.conj J.matrix) ∧
    (∀ X : J.space, R (J.inclusion X) = X) ∧
    (∀ X : J.L, X ∈ sectionCone J.L →
      R X ∈ sectionCone J.space ∧ traceUnit J.space (R X) ≤ traceUnit J.L X) ∧
    (∀ g : J.space →ₗ[ℝ] ℝ, proper (sectionCone J.space) (traceUnit J.space) g →
      proper (sectionCone J.L) (traceUnit J.L) (g.comp R) ∧
      (g.comp R).comp J.inclusion = g)) ∧
  (∀ g : J.space →ₗ[ℝ] ℝ, proper (sectionCone J.space) (traceUnit J.space) g →
    ∃ f : J.L →ₗ[ℝ] ℝ, proper (sectionCone J.L) (traceUnit J.L) f ∧
      f.comp J.inclusion = g) ∧
  (∀ p x : J.space,
    comparison (sectionCone J.L) (traceUnit J.L) (J.inclusion p) (J.inclusion x) =
      comparison (sectionCone J.space) (traceUnit J.space) p x) ∧
  (∀ p x : J.space, traceUnit J.space p = 1 → x ∈ sectionCone J.space →
    ∃ g : J.space →ₗ[ℝ] ℝ, confirms (sectionCone J.space) (traceUnit J.space) p g ∧
      g x = comparison (sectionCone J.space) (traceUnit J.space) p x) ∧
  (∀ p x : J.space, traceUnit J.space p = 1 → x ∈ sectionCone J.space →
    (comparison (sectionCone J.space) (traceUnit J.space) p x = 0 ↔
      ∃ g : J.space →ₗ[ℝ] ℝ, confirms (sectionCone J.space) (traceUnit J.space) p g ∧
        g x = 0)) ∧
  (nativeG2 J.L → nativeG2 J.space)

private theorem side_conclusion : J.SideConclusion := by
  refine ⟨J.supported_cone, J.section_cone, J.side_rog,
    whole_pure_carrier J.space J.side_rog, J.pure_inclusion, ?_,
    J.effect_onto, J.comparison_exact, J.local_attainment, J.local_zero_iff,
    J.native_G2_inherits⟩
  refine ⟨J.retraction, fun _ => rfl, J.retraction_fixes, ?_, J.effect_extension⟩
  intro X hX
  have h := J.congruence_positive_subunit X.val X.property hX
  exact ⟨(J.section_cone _).mp h.1 |>.2, h.2⟩

/-- Both supported real ROG sides of the original projective join admit the
actual congruence retractions, full effect restriction, attained exact comparison
and the native G2 inheritance, with no additional map or certificate hypotheses. -/
theorem real_join_retractions (J : RealJoin ι) :
    J.SideConclusion ∧ J.swap.SideConclusion :=
  ⟨J.side_conclusion, J.swap.side_conclusion⟩

end RealJoin
end D5.S3.Quantum.Foundation.LinearJoinRetraction
