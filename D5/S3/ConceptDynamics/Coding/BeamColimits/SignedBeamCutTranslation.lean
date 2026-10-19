/- GID: D5/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/BeamColimits/SignedBeamCutTranslation
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Signed time transports actual beam cuts by subtraction on the existing row colimit. -/
import D5.S3.ConceptDynamics.Coding.BeamColimits.PositiveWordBeamTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.SignedBeamCutTranslation
open EssentialWordRealization StandardBeamGeometry StandardBeamEndpointRows
open StandardBeamCoordinates StandardBeamColimitCuts StandardBeamHomeomorphisms
open InertGroupBlockConjugacy (StationaryModule stationaryTransition)
open scoped BigOperators

section Colimit
variable {M : Type*} [AddCommGroup M] [Module ℤ M] (T : Module.End ℤ M)

/-- Integer cut displacement on the EXISTING stationary module, without
assuming T injective or invertible on the original stage module. -/
def cutShift (s : ℤ) : StationaryModule T →ₗ[ℤ] StationaryModule T :=
  Module.DirectLimit.lift ℤ ℕ (fun _ : ℕ => M) (stationaryTransition T)
    (fun N => intStage T ((N : ℤ)-s)) (by
      intro i j hij z
      have h := intStage_refine T ((i : ℤ)-s) (j-i) z
      have hc : (i : ℤ)-s+((j-i : ℕ) : ℤ) = (j : ℤ)-s := by omega
      rw [hc] at h
      exact h.symm)

@[simp] theorem cutShift_stage (s : ℤ) (N : ℕ) (z : M) :
    cutShift T s (stage T N z) = intStage T ((N : ℤ)-s) z := by
  unfold cutShift stage
  exact Module.DirectLimit.lift_of (R := ℤ) (ι := ℕ) (G := fun _ : ℕ => M) _ _ z

theorem cutShift_intStage (s N : ℤ) (z : M) :
    cutShift T s (intStage T N z) = intStage T (N-s) z := by
  change cutShift T s (stage T N.toNat ((T ^ (-N).toNat) z)) = _
  rw [cutShift_stage]
  have h := intStage_refine T (N-s) (-N).toNat z
  have hc : N-s+((-N).toNat : ℤ) = (N.toNat : ℤ)-s := by omega
  rw [hc] at h
  exact h.symm

theorem cutShift_inverse (s : ℤ) (x : StationaryModule T) :
    cutShift T (-s) (cutShift T s x) = x := by
  obtain ⟨N, z, hz⟩ := Module.DirectLimit.exists_of x
  change stage T N z = x at hz
  rw [← hz, cutShift_stage, cutShift_intStage]
  have hc : (N : ℤ)-s-(-s) = (N : ℤ) := by omega
  rw [hc, intStage_nat]

def cutEquiv (s : ℤ) : StationaryModule T ≃ₗ[ℤ] StationaryModule T where
  toFun := cutShift T s
  invFun := cutShift T (-s)
  map_add' := (cutShift T s).map_add
  map_smul' := (cutShift T s).map_smul
  left_inv := cutShift_inverse T s
  right_inv x := by
    have h := cutShift_inverse T (-s) x
    simpa only [neg_neg] using h

end Colimit

universe u v
variable {V : Type u} {E : Type v} (G : DirectedMultigraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V]
variable [TopologicalSpace E] [DiscreteTopology E]

/-- This is the existing translate function with its explicit continuous inverse.
It is NOT an additional leaf of the supplied positive Word syntax. -/
def timeHomeomorph (s : ℤ) : History G ≃ₜ History G where
  toFun := translate G s
  invFun := translate G (-s)
  left_inv x := by
    apply Subtype.ext
    funext k
    exact congrArg x.val (by omega)
  right_inv x := by
    apply Subtype.ext
    funext k
    exact congrArg x.val (by omega)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    exact (continuous_apply (k+s)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    exact (continuous_apply (k+(-s))).comp continuous_subtype_val

theorem image_ray (s : ℤ) (alpha : History G) (N : ℤ) :
    timeHomeomorph G s '' ray G alpha N = ray G (translate G s alpha) (N-s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ k hk
    exact hx (k+s) (by omega)
  · intro hy
    refine ⟨(timeHomeomorph G s).symm y, ?_, (timeHomeomorph G s).apply_symm_apply y⟩
    intro k hk
    have h := hy (k-s) (by omega)
    change y.val (k+(-s)) = alpha.val k
    change y.val (k-s) = alpha.val (k-s+s) at h
    simpa only [sub_eq_add_neg, neg_add_cancel_right] using h

theorem image_endpoint (s : ℤ) (alpha : History G) (N : ℤ) :
    endpoint G (translate G s alpha) (N-s) = endpoint G alpha N := by
  change G.target (alpha.val (N-s+s)) = G.target (alpha.val N)
  rw [sub_add_cancel]

def partsEquiv (s : ℤ) (U : Set (History G)) (N : ℤ) :
    Parts G U N ≃ Parts G (timeHomeomorph G s '' U) (N-s) where
  toFun P := ⟨⟨timeHomeomorph G s '' P.val.val,
    translate G s (RayAt.representative G P.val), by
      rw [RayAt.set_eq G P.val, image_ray]⟩, Set.image_mono P.property⟩
  invFun Q := ⟨⟨(timeHomeomorph G s).symm '' Q.val.val,
    translate G (-s) (RayAt.representative G Q.val), by
      rw [RayAt.set_eq G Q.val]
      have h := image_ray G (-s) (RayAt.representative G Q.val) (N-s)
      have hc : N-s-(-s) = N := by omega
      change timeHomeomorph G (-s) '' _ = _
      simpa only [hc] using h⟩, by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, he⟩ := Q.property hy
    simpa only [← he, Homeomorph.symm_apply_apply] using hz⟩
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    change (timeHomeomorph G s).symm '' (timeHomeomorph G s '' P.val.val) = P.val.val
    simp only [Set.image_image, Function.comp_def, Homeomorph.symm_apply_apply,
      Set.image_id']
  right_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    change timeHomeomorph G s '' ((timeHomeomorph G s).symm '' Q.val.val) = Q.val.val
    simp only [Set.image_image, Function.comp_def, Homeomorph.apply_symm_apply,
      Set.image_id']

theorem parts_endpoint (s : ℤ) (U : Set (History G)) (N : ℤ) (P : Parts G U N) :
    RayAt.endpoint G ((partsEquiv G s U N P).val) = RayAt.endpoint G P.val := by
  let x := RayAt.representative G P.val
  have hx : x ∈ P.val.val := by rw [RayAt.set_eq G P.val]; exact self_mem_ray G x N
  exact (RayAt.endpoint_of_mem G (partsEquiv G s U N P).val (translate G s x) ⟨x, hx, rfl⟩).trans
    (image_endpoint G s x N)

theorem image_atCut (s : ℤ) {U : Set (History G)} {N : ℤ} (hU : AtCut G U N) :
    AtCut G (timeHomeomorph G s '' U) (N-s) := by
  letI : Finite (Parts G U N) := hU.1
  haveI : Finite (Parts G (timeHomeomorph G s '' U) (N-s)) :=
    Finite.of_equiv _ (partsEquiv G s U N)
  refine ⟨inferInstance, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  change ray G (translate G s x) (N-s) ⊆ _
  rw [← image_ray]
  exact Set.image_mono (hU.2 x hx)

theorem endpointRow_image (s : ℤ) {U : Set (History G)} {N : ℤ} (hU : AtCut G U N) :
    letI : Finite (Parts G U N) := hU.1
    letI : Finite (Parts G (timeHomeomorph G s '' U) (N-s)) := (image_atCut G s hU).1
    endpointRow G (timeHomeomorph G s '' U) (N-s) = endpointRow G U N := by
  letI : Finite (Parts G U N) := hU.1
  letI : Finite (Parts G (timeHomeomorph G s '' U) (N-s)) := (image_atCut G s hU).1
  letI : Fintype (Parts G U N) := Fintype.ofFinite _
  letI : Fintype (Parts G (timeHomeomorph G s '' U) (N-s)) := Fintype.ofFinite _
  unfold endpointRow
  symm
  apply Fintype.sum_equiv (partsEquiv G s U N)
  intro P
  rw [parts_endpoint]

def imageBeam (s : ℤ) (U : Beam G) : Beam G :=
  ⟨timeHomeomorph G s '' U.val, by
    obtain ⟨N, hN⟩ := U.property
    exact ⟨N-s, image_atCut G s hN⟩⟩

/-- Actual time on every beam equals the signed cut map on the row colimit. -/
theorem beam_coordinate (hG : Essential G) (s : ℤ) (U : Beam G) :
    beamCoordinate G (imageBeam G s U) =
      cutShift (rowTransition G) s (beamCoordinate G U) := by
  obtain ⟨N, hN⟩ := U.property
  rw [beamCoordinate_at G hG _ (N-s) (image_atCut G s hN),
    beamCoordinate_at G hG U N hN]
  unfold coordinateAt
  letI : Finite (Parts G U.val N) := hN.1
  letI : Finite (Parts G (timeHomeomorph G s '' U.val) (N-s)) := (image_atCut G s hN).1
  change intStage (rowTransition G) (N-s)
    (endpointRow G (timeHomeomorph G s '' U.val) (N-s)) = _
  exact (congrArg (intStage (rowTransition G) (N-s)) (endpointRow_image G s hN)).trans
    (cutShift_intStage (rowTransition G) s N (endpointRow G U.val N)).symm

end D5.S3.ConceptDynamics.Coding.SignedBeamCutTranslation
