import CFMPGenericSectorCoordinates1236Transient
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceNeighborhoodCoordinatesCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing Occurrence)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceEndpointCandidate
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate
open D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate
open D5.S3.Geometry.Gluing.RawFaceSectorCoordinatesCandidate
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (Sector)
open private dominant_unique from D5.S3.Geometry.Gluing.ActualLinkAffineFan
variable {T : Type*}

def rawPhi (P : RawFacePairing T) (r : Occurrence T → Bool) (d0 : OrderedEnd T)
    (z : Component P d0 × Sector) : Raw T :=
  (z.1.val.val.1,beta r z.1.val z.2.val)

private theorem rawPhi_mem (P : RawFacePairing T) (r : Occurrence T → Bool)
    (d0 : OrderedEnd T) (z : Component P d0 × Sector) :
    rawPhi P r d0 z ∈ Carrier P (label P d0.val.1) := by
  have h := beta_actual_simplex r z.1.val z.2
  have hd := (dart_chain_flags P (label P d0.val.1) z.1.property).mp
    ⟨d0.property,rfl⟩
  exact ⟨(beta_actual_values r z.1.val z.2.val).1,h.1,h.2.1,hd.2⟩

def Phi (P : RawFacePairing T) (r : Occurrence T → Bool) (d0 : OrderedEnd T)
    (z : Component P d0 × Sector) :
    ↥(Neighborhood P (ν := label P d0.val.1) d0.val) :=
  ⟨⟨rawPhi P r d0 z,rawPhi_mem P r d0 z⟩,
    z.1.val.val.2,(beta_actual_simplex r z.1.val z.2).2.2,z.1.property⟩

theorem actual_component_strict_coordinates (P : RawFacePairing T)
    (r : Occurrence T → Bool) (d0 : OrderedEnd T) :
    Function.Bijective (Phi P r d0) := by
  constructor
  · rintro ⟨i,p⟩ ⟨j,q⟩ h
    have hr := congrArg (fun z => z.val.val) h
    have hc := congrArg Prod.fst hr
    have hb := congrArg Prod.snd hr
    change beta r i.val p.val = beta r j.val q.val at hb
    have hp := beta_actual_simplex r i.val p
    have hq := beta_actual_simplex r j.val q
    have hk : i.val.val.2 = j.val.val.2 := by
      apply dominant_unique _ hp.1 hp.2.1 hp.2.2
      rw [hb]
      exact hq.2.2
    have hij : i = j := Subtype.ext (Subtype.ext (Prod.ext hc hk))
    subst j
    have hi := beta_actual_values r i.val p.val
    have hj := beta_actual_values r i.val q.val
    have ha := congrFun hb
      (D5.S3.Geometry.Hyperideal.EdgeStarTransitions.incomingFace r (occ i.val.val))
    have hz := congrFun hb
      (D5.S3.Geometry.Hyperideal.EdgeStarTransitions.outgoingFace r (occ i.val.val))
    rw [hi.2.2.1,hj.2.2.1] at ha
    rw [hi.2.2.2,hj.2.2.2] at hz
    have hpq : p = q := Subtype.ext (Prod.ext (by linarith) (by linarith))
    subst q
    rfl
  · intro y
    obtain ⟨k,hk,hd⟩ := y.property
    have hjk : y.val.val.1.2 ≠ k := by
      intro he
      rw [← he,y.val.property.1] at hk
      norm_num at hk
    let d : OrderedEnd T := ⟨(y.val.val.1,k),hjk⟩
    let i : Component P d0 := ⟨d,hd⟩
    have hy := y.val.property
    obtain ⟨hab,hbeta⟩ := actual_inverse_sector r d y.val.val.2
      hy.1 hy.2.1 hy.2.2.1 hk
    let p : Sector := ⟨(2*y.val.val.2
      (D5.S3.Geometry.Hyperideal.EdgeStarTransitions.incomingFace r (occ d.val)),
      2*y.val.val.2
      (D5.S3.Geometry.Hyperideal.EdgeStarTransitions.outgoingFace r (occ d.val))),hab⟩
    refine ⟨(i,p),?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl hbeta

def coordinateEquiv (P : RawFacePairing T) (r : Occurrence T → Bool)
    (d0 : OrderedEnd T) :=
  Equiv.ofBijective (Phi P r d0) (actual_component_strict_coordinates P r d0)

end D5.S3.Geometry.Gluing.RawFaceNeighborhoodCoordinatesCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceNeighborhoodCoordinatesCandidate.actual_component_strict_coordinates,
      ``D5.S3.Geometry.Gluing.RawFaceNeighborhoodCoordinatesCandidate.coordinateEquiv] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1244 target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1244 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1244 CHECKED {name} axioms={axioms}"
