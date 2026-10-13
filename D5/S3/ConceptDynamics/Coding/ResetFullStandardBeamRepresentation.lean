/- GID: D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: The full original unit-shift representation contains identity plus transition exactly at even order. -/
import D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
import D5.S3.ConceptDynamics.Coding.StandardBeamIdentification
import D5.S3.ConceptDynamics.Coding.ResetNativeOddObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
open D5.S3.ConceptDynamics.Coding.StandardBeamCoordinates
open D5.S3.ConceptDynamics.Coding.StandardBeamColimitCuts
open D5.S3.ConceptDynamics.Coding.StandardTaggedBeams
open D5.S3.ConceptDynamics.Coding.StandardBeamIdentification
open D5.S3.ConceptDynamics.Coding.StandardBeamPushforward
open D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
  (DimensionGroup VertexModule transition vertex vertexBasis stationaryTransition)
open scoped BigOperators Matrix

/- The frozen native transition uses the original integer module on its
   additive group. Reuse that instance at this boundary. -/
local instance originalNativeIntModule (q : ℕ) : Module ℤ (DimensionGroup (resetMatrix q)) :=
  AddCommGroup.toIntModule _

/-- F followed by literal two-coefficient same-stage native transport. -/
def nativeEquiv (q : ℕ) (hq : 0 < q) :
    BeamGroup (ResetGraph q) (Alternating.reset_expanded_essential q hq) ≃ₗ[ℤ]
      DimensionGroup (resetMatrix q) :=
  ((beamRowEquiv (ResetGraph q) (Alternating.reset_expanded_essential q hq)).toAddEquiv.trans
    (resetRowLimitEquiv q).toAddEquiv).toIntLinearEquiv

def nativeStage (q N : ℕ) : VertexModule Sign q →ₗ[ℤ] DimensionGroup (resetMatrix q) :=
  (stage (transition (resetMatrix q)) N).toAddMonoidHom.toIntLinearMap

theorem nativeStage_apply (q N : ℕ) (z : VertexModule Sign q) :
    nativeStage q N z = stage (transition (resetMatrix q)) N z := rfl

theorem native_hom_ext (q : ℕ) {f g : Module.End ℤ (DimensionGroup (resetMatrix q))}
    (h : ∀ N : ℕ, f.comp (nativeStage q N) = g.comp (nativeStage q N)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨N, z, hx⟩ := Module.DirectLimit.exists_of x
  rw [← hx]
  simpa only [LinearMap.comp_apply, nativeStage_apply, stage] using LinearMap.congr_fun (h N) z

/-- The representation is conjugation of ACTUAL set pushforward through the
proved geometric integer-group equivalence. No independently supplied End. -/
def rho (q : ℕ) (hq : 0 < q) :
    ResetFullAut q →* (DimensionGroup (resetMatrix q) ≃ₗ[ℤ] DimensionGroup (resetMatrix q)) where
  toFun h := (nativeEquiv q hq).symm.trans
    ((resetFullBeamRepresentation q hq h).trans (nativeEquiv q hq))
  map_one' := by
    ext x
    simp [LinearEquiv.trans_apply, (resetFullBeamRepresentation q hq).map_one]
  map_mul' g h := by
    ext x
    simp [LinearEquiv.trans_apply, (resetFullBeamRepresentation q hq).map_mul]

@[simp] theorem rho_nativeEquiv (q : ℕ) (hq : 0 < q) (h : ResetFullAut q)
    (x : BeamGroup (ResetGraph q) (Alternating.reset_expanded_essential q hq)) :
    rho q hq h (nativeEquiv q hq x) =
      nativeEquiv q hq (resetFullBeamRepresentation q hq h x) := by
  simp [rho, LinearEquiv.trans_apply]

@[simp] theorem nativeEquiv_chosenClass (q : ℕ) (hq : 0 < q) (p : Fin q × Sign) (N : ℕ) :
    nativeEquiv q hq (chosenClass (ResetGraph q) (Alternating.reset_expanded_essential q hq) p N) =
      stage (transition (resetMatrix q)) N (vertex p.1 p.2) := by
  change resetRowLimitEquiv q
    (F (ResetGraph q) (Alternating.reset_expanded_essential q hq)
      (chosenClass (ResetGraph q) (Alternating.reset_expanded_essential q hq) p N)) = _
  rw [F_chosenClass, resetRowLimitEquiv_stage]
  congr 1
  change NativeIntegralRowTransport.basisEquiv q
    (NativeIntegralRowTransport.rowVertex p.1 p.2) = _
  rw [← NativeIntegralRowTransport.decode_vertex]
  exact NativeIntegralRowTransport.encode_decode _

/-- The native even action on every ACTUAL chosen ray generator. -/
@[simp] theorem nativeEquiv_singleton (q : ℕ) (hq : 0 < q) (U : Beam (ResetGraph q)) :
    nativeEquiv q hq
      (objectGroup (ResetGraph q) (Alternating.reset_expanded_essential q hq)
        (singleton (ResetGraph q) U)) = resetBeamCoordinate q U := by
  change resetRowLimitEquiv q
    (F (ResetGraph q) (Alternating.reset_expanded_essential q hq)
      (objectGroup (ResetGraph q) (Alternating.reset_expanded_essential q hq)
        (singleton (ResetGraph q) U))) = _
  rw [F_objectGroup]
  change resetRowLimitEquiv q (objectValue (ResetGraph q) (singleton (ResetGraph q) U)) =
    resetRowLimitEquiv q (beamCoordinate (ResetGraph q) U)
  congr 1
  unfold objectValue
  letI : Fintype (StandardTaggedBeams.singleton (ResetGraph q) U).Tag := Fintype.ofFinite _
  letI : Subsingleton (StandardTaggedBeams.singleton (ResetGraph q) U).Tag :=
    inferInstanceAs (Subsingleton PUnit)
  rw [Fintype.sum_subsingleton
    (fun i : (StandardTaggedBeams.singleton (ResetGraph q) U).Tag =>
      beamCoordinate (ResetGraph q) ((StandardTaggedBeams.singleton (ResetGraph q) U).beam i))
    (PUnit.unit : (StandardTaggedBeams.singleton (ResetGraph q) U).Tag)]
  rfl

/-- Native action is literal Set.image on EVERY actual beam class. -/
theorem rho_beam_image (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) (U : Beam (ResetGraph q)) :
    rho q hq h (resetBeamCoordinate q U) =
      resetBeamCoordinate q (resetImageBeam q hq h U) := by
  rw [← nativeEquiv_singleton q hq U, rho_nativeEquiv, resetFullBeamRepresentation,
    fullBeamRepresentation_object]
  exact nativeEquiv_singleton q hq (resetImageBeam q hq h U)

/-- The actual unit shift is represented by TRUE stationary transition,
on the whole native integer group and at the original row orientation. -/
theorem rho_unitShift (q : ℕ) (hq : 0 < q) :
    (rho q hq (unitShift (ResetGraph q))).toLinearMap = resetTheta q := by
  apply native_hom_ext q
  intro N
  apply (vertexBasis (H := Sign) (n := q)).ext
  intro p
  rcases p with ⟨i, h⟩
  simp only [LinearMap.comp_apply, nativeStage_apply, LinearEquiv.coe_toLinearMap,
    vertexBasis, Pi.basis_apply, MonoidAlgebra.basis_apply]
  let alpha := resetBasisHistory q hq (i, h) (N : ℤ)
  have hray : resetBeamCoordinate q (resetRayBeam q hq alpha (N : ℤ)) =
      stage (transition (resetMatrix q)) N (vertex i h) := by
    rw [resetBeamCoordinate_ray, intStage_nat]
    simp [alpha, resetBasisHistory]
  have him : resetBeamCoordinate q
      (resetImageBeam q hq (unitShift (ResetGraph q)) (resetRayBeam q hq alpha (N : ℤ))) =
      resetTheta q (resetBeamCoordinate q (resetRayBeam q hq alpha (N : ℤ))) := by
    exact reset_actual_shift_ray_coordinate q hq alpha (N : ℤ)
  have he := (rho_beam_image q hq (unitShift (ResetGraph q))
    (resetRayBeam q hq alpha (N : ℤ))).trans him
  rw [hray] at he
  change rho q hq (unitShift (ResetGraph q)) (stage (transition (resetMatrix q)) N (vertex i h)) =
    resetTheta q (stage (transition (resetMatrix q)) N (vertex i h))
  exact he

/-- The native even action on every ACTUAL chosen ray generator. -/
theorem rho_even_basis (q : ℕ) (hq : 0 < q) (he : Even q) (p : Fin q × Sign) (N : ℕ) :
    rho q hq (evenAut q hq he) (stage (transition (resetMatrix q)) N (vertex p.1 p.2)) =
      ((LinearMap.id : Module.End ℤ (DimensionGroup (resetMatrix q))) + resetTheta q)
        (stage (transition (resetMatrix q)) N (vertex p.1 p.2)) := by
  rw [← nativeEquiv_chosenClass q hq p N, rho_nativeEquiv]
  simp only [nativeEquiv_chosenClass]
  change resetRowLimitEquiv q
    (F (ResetGraph q) (Alternating.reset_expanded_essential q hq)
      (resetFullBeamRepresentation q hq (evenAut q hq he)
        (chosenClass (ResetGraph q) (Alternating.reset_expanded_essential q hq) p N))) =
    stage (transition (resetMatrix q)) N (vertex p.1 p.2) +
      resetTheta q (stage (transition (resetMatrix q)) N (vertex p.1 p.2))
  have ht := reset_fullBeam_even_stage q hq he (resetBasisHistory q hq p (N : ℤ)) N
  simp only [chosenClass, chosenRay, resetRayBeam, resetBasisHistory, vertexHistory_endpoint,
    LinearMap.add_apply, LinearMap.id_apply, resetTheta, Theta] at ht
  exact ht

/-- Exact equality of the genuine full representation with id+Theta on the
ENTIRE original integer DimensionGroup, via every native stage and basis. -/
theorem rho_even (q : ℕ) (hq : 0 < q) (he : Even q) :
    (rho q hq (evenAut q hq he)).toLinearMap = LinearMap.id + resetTheta q := by
  apply native_hom_ext q
  intro N
  apply (vertexBasis (H := Sign) (n := q)).ext
  intro p
  rcases p with ⟨i, h⟩
  simp only [LinearMap.comp_apply, nativeStage_apply, LinearEquiv.coe_toLinearMap,
    vertexBasis, Pi.basis_apply, MonoidAlgebra.basis_apply]
  change rho q hq (evenAut q hq he) (stage (transition (resetMatrix q)) N (vertex i h)) =
    ((LinearMap.id : Module.End ℤ (DimensionGroup (resetMatrix q))) + resetTheta q)
      (stage (transition (resetMatrix q)) N (vertex i h))
  exact rho_even_basis q hq he (i, h) N

/-- Odd q is excluded by the strongest original native obstruction;
no transition injectivity, torsion-free premise, or shift power is used. -/
theorem rho_odd_excluded (q : ℕ) (hq : 0 < q) (ho : Odd q) (h : ResetFullAut q) :
    (rho q hq h).toLinearMap ≠ LinearMap.id + resetTheta q := by
  intro he
  obtain ⟨hnonzero, hkilled⟩ := reset_odd_killed_class q hq ho
  apply hnonzero
  apply (rho q hq h).injective
  change (rho q hq h).toLinearMap (resetOddClass q) =
    (rho q hq h).toLinearMap 0
  rw [he, map_zero]
  exact hkilled

/-- Original exact membership statement, for EVERY positive q. The existential
domain is the full actual unit-shift history automorphism group. -/
theorem reset_full_standard_representation_iff (q : ℕ) (hq : 0 < q) :
    (∃ h : ResetFullAut q, (rho q hq h).toLinearMap = LinearMap.id + resetTheta q) ↔ Even q := by
  constructor
  · rintro ⟨h, he⟩
    by_contra hne
    exact rho_odd_excluded q hq (Nat.not_even_iff_odd.mp hne) h he
  · intro he
    exact ⟨evenAut q hq he, rho_even q hq he⟩

end D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
