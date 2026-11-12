import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
import Reg.Support.PfaffianSourceReadouts

/-! Source-bound audits of the graph and weighted Pfaffian unit. -/

namespace Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
open _root_.D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open _root_.D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian
open _root_.D5.S3.Combinatorics.PerfectMatchings.CanonicalPairListing
open _root_.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PfaffianSourceReadouts LeanInformationAudit

noncomputable section
universe u

namespace MateAdj
def evidence : Registration arena.{u} (type_of% @matchingMate_adj.{u}) where
  actual := adjacencyActual.{u}
  bridge := bridge
  variation := ⟨actual_law, adjacencyRejected.{u}, mateAdjBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ mateAdjBad
  dependence := adjacencyDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matchingMate_adj.{u}) (Realization adjacencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MateAdj.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MateAdj.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize adjacencySignature.{u}
    (fun _ p x y => p.2.Adj x y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end MateAdj

namespace MateIff
def evidence : Registration arena.{u} (type_of% @matchingMate_eq_iff.{u}) where
  actual := adjacencyActual.{u}
  bridge := bridge
  variation := ⟨actual_law, adjacencyRejected.{u}, mateIffBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ mateIffBad
  dependence := adjacencyDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matchingMate_eq_iff.{u}) (Realization adjacencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MateIff.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MateIff.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize adjacencySignature.{u}
    (fun _ p x y => p.2.Adj x y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end MateIff

namespace MateInvolutive
def evidence : Registration arena.{u} (type_of% @matchingMate_involutive.{u}) where
  actual := predicateActual.{u}
  bridge := bridge
  variation := ⟨actual_law, predicateRejected.{u}, mateInvolutiveBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ mateInvolutiveBad
  dependence := predicateDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matchingMate_involutive.{u}) (Realization predicateSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MateInvolutive.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MateInvolutive.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize predicateSignature.{u} predicateActual.{u}.readout predicateActual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end MateInvolutive

namespace MateNe
def evidence : Registration arena.{u} (type_of% @matchingMate_ne.{u}) where
  actual := vertexRejected.{u}
  bridge := bridge
  variation := ⟨actual_law, vertexActual.{u}, mateNeBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ mateNeBad
  dependence := vertexNeDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matchingMate_ne.{u}) (Realization vertexSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MateNe.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MateNe.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize vertexSignature.{u} (fun _ _ x y => x ≠ y)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end MateNe

namespace PairingPerfect
def evidence : Registration arena (type_of% @pairingGraph_perfect) where
  actual := perfectActual
  bridge := bridge
  variation := ⟨actual_law, perfectRejected, pairingPerfectBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ pairingPerfectBad
  dependence := perfectDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairingGraph_perfect) (Realization perfectSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.PairingPerfect.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.PairingPerfect.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize perfectSignature perfectActual.readout perfectActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PairingPerfect

namespace PairingInverse
def evidence : Registration arena (type_of% @pairing_matching_inverse) where
  actual := pairingActual
  bridge := bridge
  variation := ⟨actual_law, pairingRejected, pairingInverseBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ pairingInverseBad
  dependence := pairingDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pairing_matching_inverse) (Realization pairingSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.PairingInverse.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.PairingInverse.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairingSignature pairingActual.readout pairingActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PairingInverse

namespace MatchingInverse
def evidence : Registration arena (type_of% @matching_pairing_inverse) where
  actual := matchingActual
  bridge := bridge
  variation := ⟨actual_law, matchingRejected, matchingInverseBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ matchingInverseBad
  dependence := matchingDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matching_pairing_inverse) (Realization matchingSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MatchingInverse.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MatchingInverse.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matchingSignature matchingActual.readout matchingActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end MatchingInverse

namespace Flip
def evidence : Registration arena.{u} (type_of% @alternating_cycle_flip.{u}) where
  actual := graphPerfectActual.{u}
  bridge := bridge
  variation := ⟨actual_law, graphPerfectRejected.{u}, flipBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ flipBad
  dependence := graphPerfectDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@alternating_cycle_flip.{u}) (Realization graphPerfectSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.Flip.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.Flip.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize graphPerfectSignature.{u} graphPerfectActual.{u}.readout graphPerfectActual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Flip

namespace MatchingPairingAdj
def evidence : Registration arena.{u} (type_of% @matchingPairing_adj.{u}) where
  actual := finActual
  bridge := bridge
  variation := ⟨actual_law, finRejected, matchingPairingAdjBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ matchingPairingAdjBad
  dependence := finDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matchingPairing_adj.{u}) (Realization finSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MatchingPairingAdj.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.MatchingPairingAdj.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finSignature finActual.readout finActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end MatchingPairingAdj

namespace CanonicalAdj
def evidence : Registration arena.{u} (type_of% @canonical_adj.{u}) where
  actual := matchingAdjActual.{u}
  bridge := bridge
  variation := ⟨actual_law, matchingAdjRejected.{u}, canonicalAdjBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ canonicalAdjBad
  dependence := matchingAdjDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_adj.{u}) (Realization matchingAdjSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.CanonicalAdj.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.CanonicalAdj.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matchingAdjSignature.{u}
    (fun _ p x y => p.2.2.val.Adj x y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CanonicalAdj

namespace Transport
def evidence : Registration arena.{u} (type_of% @alternating_cycle_transport.{u}) where
  actual := unitActual
  bridge := bridge
  variation := ⟨actual_law, unitRejected, transportBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ transportBad
  dependence := unitDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@alternating_cycle_transport.{u}) (Realization unitSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.Transport.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.Transport.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize unitSignature unitActual.readout unitActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Transport

namespace Uniformity
def evidence : Registration arena.{u} (type_of% @niceOdd_matching_tau_eq.{u}) where
  actual := unitActual
  bridge := bridge
  variation := ⟨actual_law, unitRejected, uniformityBad⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ uniformityBad
  dependence := unitDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@niceOdd_matching_tau_eq.{u}) (Realization unitSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.Uniformity.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian.Uniformity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize unitSignature unitActual.readout unitActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Uniformity

end
end Reg.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian


namespace Reg.D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching
open _root_.D5.S0.Certificates.IshikawaKoutschanMotzkinPfaffianRefutation
open _root_.D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
open _root_.D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.PfaffianSourceReadouts LeanInformationAudit

noncomputable section
universe u v

abbrev signature : Signature where
  Params := Type v
  State R := R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ R := R → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{v} :=
  realize _ (fun _ _ x y => x ≠ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law r := ∀ {V : Type u} {G : SimpleGraph V} {n : ℕ} [Fintype V]
    {R : Type v} [CommRing R] (label : V ≃ Fin (2*n))
    {epsilon : G.Dart → ZMod 2} (he : Reverses epsilon) (ho : NiceOdd epsilon)
    (w : G.edgeSet → R),
    r.readout () R (pfaffian (orientedMatrix label epsilon w))
      (((orientationUnit label epsilon : ℤ) : R) * partitionFunction w)

theorem actual_law : arena.{u,v}.Law actual :=
  @_root_.D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching.weighted_pfaffian_identity.{u,v}
theorem bridge :
    (type_of% @_root_.D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching.weighted_pfaffian_identity.{u,v}) ↔
    arena.{u,v}.Law actual := Iff.rfl

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let V := ULift.{u} (Fin (2*0))
  let G : SimpleGraph V := ⊤
  letI : Fintype V := Fintype.ofEquiv (Fin (2*0)) Equiv.ulift.symm
  let label : V ≃ Fin (2*0) := Equiv.ulift
  let epsilon : G.Dart → ZMod 2 := fun d => Fin.elim0 d.fst.down
  have he : Reverses epsilon := fun d => Fin.elim0 d.fst.down
  have ho : NiceOdd epsilon := fun x => Fin.elim0 x.down
  exact h (R := ULift.{v} ℤ) label he ho (fun _ => 1)
    (_root_.D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching.weighted_pfaffian_identity
      label he ho (fun _ => (1 : ULift.{v} ℤ)))

theorem dependence : ObservationalDependence signature.{v} actual := by
  intro i
  refine ⟨ULift.{v} ℤ, 0, 1, ?_⟩
  intro h
  have he : (0 : ULift.{v} ℤ) = 1 := (congrFun h 1).mpr rfl
  exact zero_ne_one he

def source : Registration arena.{u,v}
    (type_of% @_root_.D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching.weighted_pfaffian_identity.{u,v}) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching.weighted_pfaffian_identity.{u,v})
    (Realization signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching.unit
  realizationName := `Reg.D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.AlternatingCyclePfaffian
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.PerfectMatchings.WeightedPfaffianMatching
