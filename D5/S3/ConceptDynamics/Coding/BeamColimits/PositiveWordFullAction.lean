/- GID: D5/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordFullAction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/BeamColimits/PositiveWordFullAction
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Literal positive-word decompositions determine the full native beam-group action. -/
import D5.S3.ConceptDynamics.Coding.BeamColimits.SignedBeamCutTranslation
import D5.S3.ConceptDynamics.Coding.StandardBeamPushforward

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.PositiveWordFullAction
open EssentialWordRealization TwoSidedFiniteInduction TypedPositiveSplitWord
open StandardBeamGeometry StandardBeamCoordinates StandardBeamColimitCuts
open StandardBeamHomeomorphisms StandardTaggedBeams StandardBeamIdentification
open StandardBeamPushforward
open scoped BigOperators

/-- A literal all-history equality supplies the geometric input; no beam,
matrix, colimit or representation comparison is assumed. In the original-h
application this equality is constructed by OriginalPositiveWordAssembly.
The conclusion concerns the existing fullBeamRepresentation on its WHOLE
Grothendieck group, including every formal difference of actual beams. -/
theorem full_action_coordinate (P : Presentation)
    [TopologicalSpace P.V] [DiscreteTopology P.V] (h : FullAut P.graph)
    (w : Word P P) (s : ℤ)
    (he : ∀ x : Hist P, h.val x = translate P.graph s (w.eval x))
    (x : BeamGroup P.graph P.essential) :
    F P.graph P.essential (fullBeamRepresentation P.graph P.essential h x) =
      SignedBeamCutTranslation.cutShift (rowTransition P.graph) s
        (PositiveWordBeamTransport.rowEquiv w (F P.graph P.essential x)) := by
  classical
  have hbeam (U : Beam P.graph) :
      beamCoordinate P.graph (StandardBeamHomeomorphisms.imageBeam P.graph P.essential h U) =
        SignedBeamCutTranslation.cutShift (rowTransition P.graph) s
          (PositiveWordBeamTransport.rowEquiv w (beamCoordinate P.graph U)) := by
    have himage : StandardBeamHomeomorphisms.imageBeam P.graph P.essential h U =
        SignedBeamCutTranslation.imageBeam P.graph s
          (PositiveWordBeamTransport.imageBeam w U) := by
      apply Subtype.ext
      change h.val '' U.val = SignedBeamCutTranslation.timeHomeomorph P.graph s ''
        (PositiveWordBeamTransport.imageBeam w U).val
      rw [PositiveWordBeamTransport.imageBeam_val, Set.image_image]
      exact congrArg (fun f : Hist P → Hist P => f '' U.val) (funext he)
    rw [himage, SignedBeamCutTranslation.beam_coordinate P.graph P.essential,
      PositiveWordBeamTransport.beam_coordinate]
  have hobject (A : Object P.graph) :
      F P.graph P.essential
          (fullBeamRepresentation P.graph P.essential h (objectGroup P.graph P.essential A)) =
        SignedBeamCutTranslation.cutShift (rowTransition P.graph) s
          (PositiveWordBeamTransport.rowEquiv w
            (F P.graph P.essential (objectGroup P.graph P.essential A))) := by
    rw [fullBeamRepresentation_object, F_objectGroup, F_objectGroup]
    unfold objectValue
    change (∑ i : A.Tag, beamCoordinate P.graph
      (StandardBeamHomeomorphisms.imageBeam P.graph P.essential h (A.beam i))) = _
    simp_rw [hbeam]
    rw [map_sum, map_sum]
  let L : RowLimit P.graph →ₗ[ℤ] RowLimit P.graph :=
    (F P.graph P.essential).toIntLinearMap.comp
      ((fullBeamRepresentation P.graph P.essential h).toLinearMap.comp (J P.graph P.essential))
  let R : RowLimit P.graph →ₗ[ℤ] RowLimit P.graph :=
    (SignedBeamCutTranslation.cutShift (rowTransition P.graph) s).comp
      (PositiveWordBeamTransport.rowEquiv w).toLinearMap
  have hLR : L = R := by
    apply Module.DirectLimit.hom_ext
    intro N
    apply (Pi.basisFun ℤ P.V).ext
    intro v
    have hg := hobject (singleton P.graph (chosenRay P.graph P.essential v N))
    change F P.graph P.essential
        (fullBeamRepresentation P.graph P.essential h (chosenClass P.graph P.essential v N)) =
      SignedBeamCutTranslation.cutShift (rowTransition P.graph) s
        (PositiveWordBeamTransport.rowEquiv w
          (F P.graph P.essential (chosenClass P.graph P.essential v N))) at hg
    rw [F_chosenClass] at hg
    change F P.graph P.essential
        (fullBeamRepresentation P.graph P.essential h
          (J P.graph P.essential (stage (rowTransition P.graph) N
            ((Pi.basisFun ℤ P.V) v)))) =
      SignedBeamCutTranslation.cutShift (rowTransition P.graph) s
        (PositiveWordBeamTransport.rowEquiv w (stage (rowTransition P.graph) N
          ((Pi.basisFun ℤ P.V) v)))
    rw [Pi.basisFun_apply]
    have hjv : J P.graph P.essential
        (stage (rowTransition P.graph) N (Pi.single v 1)) =
          chosenClass P.graph P.essential v N := by
      rw [J_stage]
      simp [JStage, Pi.single_apply, eq_comm]
    rw [hjv]
    exact hg
  have hx := LinearMap.congr_fun hLR (F P.graph P.essential x)
  change F P.graph P.essential
      (fullBeamRepresentation P.graph P.essential h
        (J P.graph P.essential (F P.graph P.essential x))) = _ at hx
  have hj : J P.graph P.essential (F P.graph P.essential x) = x :=
    LinearMap.congr_fun (JF P.graph P.essential) x
  rw [hj] at hx
  exact hx

end D5.S3.ConceptDynamics.Coding.PositiveWordFullAction
