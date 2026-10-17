/- SOURCE ONLY. UNCOMPILED. Functorial transport of the existing dependent
positive Word on actual beams and the native integer row colimits.
Intended owner: D5/S3/ConceptDynamics/Coding/PositiveWordBeamTransport.lean -/
import D5.S3.ConceptDynamics.Coding.FiniteRelabelBeamTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.PositiveWordBeamTransport
open EssentialWordRealization TwoSidedFiniteInduction TypedPositiveSplitWord
open ZeroWindowRelabeling (Relabel)
open CountedMatrixOverlap (CountMat elementaryHomeomorph)
open StandardBeamGeometry StandardBeamEndpointRows StandardBeamCoordinates
open StandardBeamColimitCuts StandardTaggedBeams StandardBeamIdentification
open scoped BigOperators Matrix

private def relabeledEssential {F : Presentation} {n : ℕ} (M : CountMat n n)
    (old : Relabel (SplitTowerTranslation.counted M) F.graph) :
    Essential (CountedMatrixBeamDiagram.countedGraph M) :=
  FiniteRelabelBeamTransport.essential old.symm F.essential

/-- The stage-zero row expression retains the actual endpoint numberings.
The rectangular right-row map is the existing matrix API, with no transpose. -/
def endpointMap : ∀ {F H : Presentation}, Word F H → (F.V → ℤ) →ₗ[ℤ] (H.V → ℤ)
  | _, _, .relabel r => FiniteRelabelBeamTransport.reindex r
  | _, _, .positive R S old next =>
      (FiniteRelabelBeamTransport.reindex next).comp
        (((CountedMatrixBeamDiagram.integerCounts R).toLinearMapRight').comp
          (FiniteRelabelBeamTransport.reindex old.symm))
  | _, _, .comp first second => (endpointMap second).comp (endpointMap first)

/-- Exactly the existing relabel and elementary colimit equivalences. -/
def rowEquiv : ∀ {F H : Presentation}, Word F H → RowLimit F.graph ≃ₗ[ℤ] RowLimit H.graph
  | _, _, .relabel r => FiniteRelabelBeamTransport.rowEquiv r
  | _, _, .positive R S old next =>
      (FiniteRelabelBeamTransport.rowEquiv old).symm.trans
        ((CountedMatrixBeamColimit.rowEquiv R S).trans
          (FiniteRelabelBeamTransport.rowEquiv next))
  | _, _, .comp first second => (rowEquiv first).trans (rowEquiv second)

/-- All signed stages, before any choice of beam representatives. -/
theorem rowEquiv_intStage : ∀ {F H : Presentation} (w : Word F H)
    (N : ℤ) (z : F.V → ℤ),
    rowEquiv w (intStage (rowTransition F.graph) N z) =
      intStage (rowTransition H.graph) N (endpointMap w z)
  | _, _, .relabel r, N, z => FiniteRelabelBeamTransport.rowMap_intStage r N z
  | _, _, .positive R S old next, N, z => by
      change FiniteRelabelBeamTransport.rowMap next
        (CountedMatrixBeamColimit.rowMap R S
          (FiniteRelabelBeamTransport.rowMap old.symm
            (intStage (rowTransition _) N z))) = _
      rw [FiniteRelabelBeamTransport.rowMap_intStage,
        CountedMatrixBeamColimit.rowMap_intStage,
        FiniteRelabelBeamTransport.rowMap_intStage]
      rfl
  | _, _, .comp first second, N, z => by
      change rowEquiv second (rowEquiv first (intStage (rowTransition _) N z)) = _
      rw [rowEquiv_intStage first, rowEquiv_intStage second]
      rfl

/-- Each constructor sends the actual input subset to an actual output beam.
Essentiality of each counted product is transported from its finite relabel. -/
def imageBeam : ∀ {F H : Presentation}, Word F H → Beam F.graph → Beam H.graph
  | _, _, .relabel r, U => FiniteRelabelBeamTransport.imageBeam r U
  | _, _, .positive R S old next, U =>
      FiniteRelabelBeamTransport.imageBeam next
        (CountedMatrixBeamDiagram.elementaryImageBeam R S (relabeledEssential (S*R) next)
          (FiniteRelabelBeamTransport.imageBeam old.symm U))
  | _, _, .comp first second, U => imageBeam second (imageBeam first U)

theorem imageBeam_val : ∀ {F H : Presentation} (w : Word F H) (U : Beam F.graph),
    (imageBeam w U).val = w.eval '' U.val
  | _, _, .relabel _, _ => rfl
  | _, _, .positive R S old next, U => by
      change next.homeomorph '' (elementaryHomeomorph R S ''
        (old.homeomorph.symm '' U.val)) = _
      rw [Set.image_image, Set.image_image]
      rfl
  | _, _, .comp first second, U => by
      change (imageBeam second (imageBeam first U)).val = _
      rw [imageBeam_val second, imageBeam_val first, Set.image_image]
      rfl

/-- No positive letter changes the cut of its finite disjoint image partition. -/
theorem image_atCut : ∀ {F H : Presentation} (w : Word F H)
    {U : Set (Hist F)} {N : ℤ}, AtCut F.graph U N → AtCut H.graph (w.eval '' U) N
  | _, _, .relabel r, _, _, hU => FiniteRelabelBeamTransport.image_atCut r hU
  | _, _, .positive R S old next, U, N, hU => by
      have hA := FiniteRelabelBeamTransport.image_atCut old.symm hU
      have hB := CountedMatrixBeamDiagram.image_atCut R S (relabeledEssential (S*R) next) hA
      have hC := FiniteRelabelBeamTransport.image_atCut next hB
      simpa only [Set.image_image] using hC
  | _, _, .comp first second, U, N, hU => by
      have hC := image_atCut second (image_atCut first hU)
      simpa only [Set.image_image] using hC

/-- Actual endpoint rows, not merely their potentially noninjective colimit
classes, compose by the stated finite row expression. -/
theorem endpointRow_image : ∀ {F H : Presentation} (w : Word F H)
    {U : Set (Hist F)} {N : ℤ} (hU : AtCut F.graph U N),
    letI : Finite (Parts F.graph U N) := hU.1
    letI : Finite (Parts H.graph (w.eval '' U) N) := (image_atCut w hU).1
    endpointRow H.graph (w.eval '' U) N = endpointMap w (endpointRow F.graph U N)
  | _, _, .relabel r, _, _, hU => FiniteRelabelBeamTransport.endpointRow_image r hU
  | _, _, .positive R S old next, U, N, hU => by
      have hA := FiniteRelabelBeamTransport.image_atCut old.symm hU
      have hB := CountedMatrixBeamDiagram.image_atCut R S (relabeledEssential (S*R) next) hA
      letI : Finite (Parts _ U N) := hU.1
      letI : Finite (Parts _ (old.homeomorph.symm '' U) N) := hA.1
      letI : Finite (Parts _ (elementaryHomeomorph R S ''
        (old.homeomorph.symm '' U)) N) := hB.1
      letI : Finite (Parts _ (next.homeomorph '' (elementaryHomeomorph R S ''
        (old.homeomorph.symm '' U))) N) :=
        (FiniteRelabelBeamTransport.image_atCut next hB).1
      have he : (Word.positive R S old next).eval '' U =
          next.homeomorph '' (elementaryHomeomorph R S '' (old.homeomorph.symm '' U)) := by
        rw [Set.image_image, Set.image_image]
        rfl
      rw [he, FiniteRelabelBeamTransport.endpointRow_image next hB,
        CountedMatrixBeamDiagram.endpointRow_image R S (relabeledEssential (S*R) next) hA,
        FiniteRelabelBeamTransport.endpointRow_image old.symm hU]
      rfl
  | _, _, .comp first second, U, N, hU => by
      have hA := image_atCut first hU
      letI : Finite (Parts _ U N) := hU.1
      letI : Finite (Parts _ (first.eval '' U) N) := hA.1
      letI : Finite (Parts _ (second.eval '' (first.eval '' U)) N) :=
        (image_atCut second hA).1
      have he : (Word.comp first second).eval '' U = second.eval '' (first.eval '' U) := by
        rw [Set.image_image]
        rfl
      rw [he, endpointRow_image second hA, endpointRow_image first hU]
      rfl

theorem beam_coordinate {F H : Presentation} (w : Word F H) (U : Beam F.graph) :
    beamCoordinate H.graph (imageBeam w U) = rowEquiv w (beamCoordinate F.graph U) := by
  obtain ⟨N, hN⟩ := U.property
  have hI : AtCut H.graph (imageBeam w U).val N := by
    rw [imageBeam_val]
    exact image_atCut w hN
  rw [beamCoordinate_at H.graph H.essential _ N hI,
    beamCoordinate_at F.graph F.essential U N hN]
  unfold coordinateAt
  rw [imageBeam_val, endpointRow_image w hN, rowEquiv_intStage]

def imageObject {F H : Presentation} (w : Word F H) (A : Object F.graph) : Object H.graph :=
  ⟨A.Tag, A.finiteTag, fun i => imageBeam w (A.beam i)⟩

theorem object_coordinate {F H : Presentation} (w : Word F H) (A : Object F.graph) :
    objectValue H.graph (imageObject w A) = rowEquiv w (objectValue F.graph A) := by
  unfold objectValue
  change (∑ i : A.Tag, beamCoordinate H.graph (imageBeam w (A.beam i))) = _
  simp_rw [beam_coordinate]
  exact (map_sum _ _ _).symm

def beamEquiv {F H : Presentation} (w : Word F H) :
    BeamGroup F.graph F.essential ≃ₗ[ℤ] BeamGroup H.graph H.essential :=
  (beamRowEquiv F.graph F.essential).trans
    ((rowEquiv w).trans (beamRowEquiv H.graph H.essential).symm)

theorem beamEquiv_coordinate {F H : Presentation} (w : Word F H)
    (x : BeamGroup F.graph F.essential) :
    StandardTaggedBeams.F H.graph H.essential (beamEquiv w x) =
      rowEquiv w (StandardTaggedBeams.F F.graph F.essential x) := by
  exact (beamRowEquiv H.graph H.essential).apply_symm_apply _

theorem beamEquiv_object {F H : Presentation} (w : Word F H) (A : Object F.graph) :
    beamEquiv w (objectGroup F.graph F.essential A) =
      objectGroup H.graph H.essential (imageObject w A) := by
  apply F_injective H.graph H.essential
  rw [beamEquiv_coordinate, F_objectGroup, F_objectGroup, object_coordinate]

/-- Every signed-cut ray of every actual word has its same-cut finite row. -/
theorem ray_coordinate {F H : Presentation} (w : Word F H) (alpha : Hist F) (N : ℤ) :
    let U : Beam F.graph := ⟨ray F.graph alpha N, N, ray_atCut _ F.essential alpha N⟩
    beamCoordinate H.graph (imageBeam w U) =
      intStage (rowTransition H.graph) N
        (endpointMap w (Pi.single (endpoint F.graph alpha N) 1)) := by
  dsimp only
  rw [beam_coordinate, beamCoordinate_at _ F.essential _ N (ray_atCut _ F.essential alpha N),
    coordinateAt_ray _ F.essential, rowEquiv_intStage]

end D5.S3.ConceptDynamics.Coding.PositiveWordBeamTransport
