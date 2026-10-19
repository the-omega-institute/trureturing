/- GID: D5/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/BeamColimits/CountedMatrixBeamColimit
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Actual counted beam images and right-row colimit transport with the exact inverse cut. -/
import D5.S3.ConceptDynamics.Coding.BeamColimits.CountedMatrixBeamDiagram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.CountedMatrixBeamColimit
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.CountedMatrixBeamDiagram
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
open D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
open D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
open D5.S3.ConceptDynamics.Coding.StandardTaggedBeams
open D5.S3.ConceptDynamics.Coding.StandardBeamIdentification
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy (stationaryTransition)
open scoped BigOperators Matrix

private def rightRow {n m : ℕ} (R : CountMat n m) : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ) :=
  (integerCounts R).toLinearMapRight'

private theorem rightRow_step {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (z : Fin n → ℤ) :
    rightRow R (rowTransition (countedGraph (R * S)) z) =
      rowTransition (countedGraph (S * R)) (rightRow R z) := by
  change (z ᵥ* adjacency (countedGraph (R * S))) ᵥ* integerCounts R =
    (z ᵥ* integerCounts R) ᵥ* adjacency (countedGraph (S * R))
  rw [adjacency_counted, adjacency_counted, integerCounts_mul, integerCounts_mul,
    Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

private theorem rightRow_power {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (r : ℕ) (z : Fin n → ℤ) :
    rightRow R (((rowTransition (countedGraph (R * S))) ^ r) z) =
      ((rowTransition (countedGraph (S * R))) ^ r) (rightRow R z) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, rightRow_step, ih]
    rw [pow_succ', Module.End.mul_apply]

/-- Constructed by Module.DirectLimit.map from AR=RB in the right-row
orientation; no geometric diagram is taken as a premise. -/
def rowMap {n m : ℕ} (R : CountMat n m) (S : CountMat m n) :
    RowLimit (countedGraph (R * S)) →ₗ[ℤ] RowLimit (countedGraph (S * R)) :=
  Module.DirectLimit.map (fun _ : ℕ => rightRow R) (by
    intro i j hij
    apply LinearMap.ext
    intro z
    exact rightRow_power R S (j - i) z)

@[simp] theorem rowMap_stage {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (N : ℕ) (z : Fin n → ℤ) :
    rowMap R S (stage (rowTransition (countedGraph (R * S))) N z) =
      stage (rowTransition (countedGraph (S * R))) N (z ᵥ* integerCounts R) := by
  simp only [rowMap, stage, Module.DirectLimit.map_apply_of, rightRow,
    Matrix.toLinearMapRight'_apply]

/-- Exact signed-stage formula, including negative integer cuts. -/
theorem rowMap_intStage {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (N : ℤ) (z : Fin n → ℤ) :
    rowMap R S (intStage (rowTransition (countedGraph (R * S))) N z) =
      intStage (rowTransition (countedGraph (S * R))) N (z ᵥ* integerCounts R) := by
  change rowMap R S
      (stage (rowTransition (countedGraph (R * S))) N.toNat
        (((rowTransition (countedGraph (R * S))) ^ (-N).toNat) z)) =
    stage (rowTransition (countedGraph (S * R))) N.toNat
      (((rowTransition (countedGraph (S * R))) ^ (-N).toNat) (rightRow R z))
  rw [rowMap_stage]
  exact congrArg (stage (rowTransition (countedGraph (S * R))) N.toNat)
    (rightRow_power R S (-N).toNat z)

private theorem rightRow_product {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (z : Fin n → ℤ) :
    rightRow S (rightRow R z) = rowTransition (countedGraph (R * S)) z := by
  change (z ᵥ* integerCounts R) ᵥ* integerCounts S =
    z ᵥ* adjacency (countedGraph (R * S))
  rw [adjacency_counted, integerCounts_mul, Matrix.vecMul_vecMul]

private theorem stage_succ_transition {n : ℕ} (M : CountMat n n) (N : ℕ) (z : Fin n → ℤ) :
    stage (rowTransition (countedGraph M)) (N + 1) (rowTransition (countedGraph M) z) =
      stage (rowTransition (countedGraph M)) N z := by
  have he := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ) (G := fun _ : ℕ => Fin n → ℤ)
    (f := stationaryTransition (rowTransition (countedGraph M)))
    (i := N) (j := N + 1) (hij := by omega) (x := z)
  simpa only [stationaryTransition, Nat.add_sub_cancel_left, pow_one, stage] using he

/-- The actual inverse is right multiplication by S AT THE NEXT CUT. -/
def rowInverse {n m : ℕ} (R : CountMat n m) (S : CountMat m n) :
    RowLimit (countedGraph (S * R)) →ₗ[ℤ] RowLimit (countedGraph (R * S)) :=
  Module.DirectLimit.lift ℤ ℕ (fun _ : ℕ => Fin m → ℤ)
    (stationaryTransition (rowTransition (countedGraph (S * R))))
    (fun N => (stage (rowTransition (countedGraph (R * S))) (N + 1)).comp (rightRow S))
    (by
      intro i j hij w
      change stage (rowTransition (countedGraph (R * S))) (j + 1)
          (rightRow S (((rowTransition (countedGraph (S * R))) ^ (j - i)) w)) =
        stage (rowTransition (countedGraph (R * S))) (i + 1) (rightRow S w)
      rw [rightRow_power S R]
      have he := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ) (G := fun _ : ℕ => Fin n → ℤ)
        (f := stationaryTransition (rowTransition (countedGraph (R * S))))
        (i := i + 1) (j := j + 1) (hij := by omega) (x := rightRow S w)
      simpa only [stationaryTransition, Nat.add_sub_add_right, stage] using he)

@[simp] theorem rowInverse_stage {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (N : ℕ) (w : Fin m → ℤ) :
    rowInverse R S (stage (rowTransition (countedGraph (S * R))) N w) =
      stage (rowTransition (countedGraph (R * S))) (N + 1) (w ᵥ* integerCounts S) := by
  simp only [rowInverse, stage, Module.DirectLimit.lift_of, LinearMap.comp_apply,
    rightRow, Matrix.toLinearMapRight'_apply]


theorem rowInverse_left {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (x : RowLimit (countedGraph (R * S))) : rowInverse R S (rowMap R S x) = x := by
  obtain ⟨N, z, hz⟩ := Module.DirectLimit.exists_of x
  change stage (rowTransition (countedGraph (R * S))) N z = x at hz
  rw [← hz, rowMap_stage, rowInverse_stage]
  change stage (rowTransition (countedGraph (R * S))) (N + 1) (rightRow S (rightRow R z)) = _
  rw [rightRow_product]
  exact stage_succ_transition (R * S) N z

theorem rowInverse_right {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (x : RowLimit (countedGraph (S * R))) : rowMap R S (rowInverse R S x) = x := by
  obtain ⟨N, w, hw⟩ := Module.DirectLimit.exists_of x
  change stage (rowTransition (countedGraph (S * R))) N w = x at hw
  rw [← hw, rowInverse_stage, rowMap_stage]
  change stage (rowTransition (countedGraph (S * R))) (N + 1) (rightRow R (rightRow S w)) = _
  rw [rightRow_product]
  exact stage_succ_transition (S * R) N w

def rowEquiv {n m : ℕ} (R : CountMat n m) (S : CountMat m n) :
    RowLimit (countedGraph (R * S)) ≃ₗ[ℤ] RowLimit (countedGraph (S * R)) where
  toFun := rowMap R S
  invFun := rowInverse R S
  map_add' := (rowMap R S).map_add
  map_smul' := (rowMap R S).map_smul
  left_inv := rowInverse_left R S
  right_inv := rowInverse_right R S



section ActualBeams
variable {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
variable (hA : Essential (countedGraph (R * S))) (hB : Essential (countedGraph (S * R)))

/-- The original ray Set.image is the mathematical bridge at every signed
generator, before invoking group completion or a change of coordinates. -/
theorem actual_ray_coordinate (alpha : Path (R * S)) (N : ℤ) :
    coordinateAt (countedGraph (S * R))
      (elementaryHomeomorph R S '' ray (countedGraph (R * S)) alpha N) N
      (image_ray_atCut R S hB alpha N) =
    rowMap R S (intStage (rowTransition (countedGraph (R * S))) N
      (Pi.single (endpoint (countedGraph (R * S)) alpha N) 1)) := by
  unfold coordinateAt
  rw [endpointRow_image_ray R S hB alpha N, rowMap_intStage]

include hA in
/-- Cross-graph compatibility for every actual beam follows by disjoint
intrinsic ray partitions; FullAut's same-graph pushforward is never coerced. -/
theorem actual_beam_coordinate (U : Beam (countedGraph (R * S))) :
    beamCoordinate (countedGraph (S * R)) (elementaryImageBeam R S hB U) =
      rowMap R S (beamCoordinate (countedGraph (R * S)) U) := by
  obtain ⟨N, hN⟩ := U.property
  rw [beamCoordinate_at _ hB _ N (image_atCut R S hB hN), beamCoordinate_at _ hA U N hN]
  unfold coordinateAt
  exact (congrArg (intStage (rowTransition (countedGraph (S * R))) N)
    (endpointRow_image R S hB hN)).trans (rowMap_intStage R S N _).symm

def elementaryImageObject (A : Object (countedGraph (R * S))) : Object (countedGraph (S * R)) :=
  ⟨A.Tag, A.finiteTag, fun i => elementaryImageBeam R S hB (A.beam i)⟩

include hA in
theorem actual_object_coordinate (A : Object (countedGraph (R * S))) :
    objectValue (countedGraph (S * R)) (elementaryImageObject R S hB A) =
      rowMap R S (objectValue (countedGraph (R * S)) A) := by
  unfold objectValue
  change (∑ i : A.Tag, beamCoordinate (countedGraph (S * R))
      (elementaryImageBeam R S hB (A.beam i))) = _
  simp_rw [actual_beam_coordinate R S hA hB]
  exact (map_sum _ _ _).symm

/-- The existing real beam group and existing beamRowEquiv are reused.
The theorem below proves this map is literal Set.image on every object. -/
def elementaryBeamEquiv :
    BeamGroup (countedGraph (R * S)) hA ≃ₗ[ℤ] BeamGroup (countedGraph (S * R)) hB :=
  (beamRowEquiv _ hA).trans ((rowEquiv R S).trans (beamRowEquiv _ hB).symm)

theorem elementaryBeamEquiv_coordinate (x : BeamGroup (countedGraph (R * S)) hA) :
    F (countedGraph (S * R)) hB (elementaryBeamEquiv R S hA hB x) =
      rowMap R S (F (countedGraph (R * S)) hA x) := by
  change (beamRowEquiv _ hB)
      ((beamRowEquiv _ hB).symm (rowEquiv R S ((beamRowEquiv _ hA) x))) = _
  exact (beamRowEquiv _ hB).apply_symm_apply _

/-- Concrete generator formula for EVERY tagged object: each output beam is
the actual Set.image of its input subset under elementaryHomeomorph R S. -/
theorem elementaryBeamEquiv_object (A : Object (countedGraph (R * S))) :
    elementaryBeamEquiv R S hA hB (objectGroup (countedGraph (R * S)) hA A) =
      objectGroup (countedGraph (S * R)) hB (elementaryImageObject R S hB A) := by
  apply F_injective _ hB
  rw [elementaryBeamEquiv_coordinate, F_objectGroup, F_objectGroup,
    actual_object_coordinate R S hA hB]




end ActualBeams
end D5.S3.ConceptDynamics.Coding.CountedMatrixBeamColimit
