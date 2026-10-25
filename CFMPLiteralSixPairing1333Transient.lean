import CFMPGenericOccurrence1163Transient

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section

namespace D5.S3.Geometry.Gluing.LiteralSixPairingCandidate

open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Hyperideal.S4OppositePairAction (edgeIndex)
open D5.S3.Geometry.Gluing.ActualLinkCornerChains (Dart)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate (sigma)
open D5.S3.Geometry.Gluing.RawFaceEndpointCandidate (dartMove DartStep DartRelated)
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate (OrderedEnd swap LocalNoEdgeReversal)

abbrev Face := Fin 6 × Fin 4

/-- All twenty-four directed faces of the twelve literal rows. -/
def paired (x : Face) : Face :=
  (![![(2,0), (1,2), (1,0), (2,3)],
      ![(0,2), (2,2), (0,1), (4,3)],
      ![(0,0), (3,2), (1,1), (0,3)],
      ![(5,0), (4,2), (2,1), (5,3)],
      ![(5,1), (5,2), (3,1), (1,3)],
      ![(3,0), (4,0), (4,1), (3,3)]] : Fin 6 → Fin 4 → Face) x.1 x.2

theorem paired_involutive : ∀ x : Face, paired (paired x) = x := by decide

theorem paired_fixedFree : ∀ x : Face, paired x ≠ x := by decide

def faceEquiv : Equiv.Perm Face where
  toFun := paired
  invFun := paired
  left_inv := paired_involutive
  right_inv := paired_involutive

/-- Actual three-edge-slot images, in the original faceEdge slot convention. -/
def slotTable (x : Face) : Fin 3 → Fin 3 :=
  (![![![1,0,2], ![0,1,2], ![2,0,1], ![0,2,1]],
      ![![1,2,0], ![0,1,2], ![0,1,2], ![1,0,2]],
      ![![1,0,2], ![0,1,2], ![0,1,2], ![0,2,1]],
      ![![1,0,2], ![0,1,2], ![0,1,2], ![0,2,1]],
      ![![2,1,0], ![0,1,2], ![0,1,2], ![1,0,2]],
      ![![1,0,2], ![2,1,0], ![0,1,2], ![0,2,1]]] :
      Fin 6 → Fin 4 → Fin 3 → Fin 3) x.1 x.2

theorem slot_inverse : ∀ (x : Face) (j : Fin 3),
    slotTable (paired x) (slotTable x j) = j := by decide

def slotEquiv (x : Face) : Fin 3 ≃ Fin 3 where
  toFun := slotTable x
  invFun := slotTable (paired x)
  left_inv := slot_inverse x
  right_inv := by
    intro j
    simpa only [paired_involutive] using slot_inverse (paired x) j

def literalPairing : RawFacePairing (Fin 6) where
  facePair := faceEquiv
  faceMap := slotEquiv
  pairInvolutive := by
    apply Equiv.ext
    intro x
    exact paired_involutive x
  pairFixedFree := paired_fixedFree
  mapInverse := slot_inverse

/-- Independent transcription of the twelve source faces, in source order. -/
def rowSource : Fin 12 → Face :=
  ![(0,0), (0,1), (0,2), (0,3), (1,1), (1,3),
    (2,1), (3,0), (3,1), (3,3), (4,0), (4,1)]

def rowTarget : Fin 12 → Face :=
  ![(2,0), (1,2), (1,0), (2,3), (2,2), (4,3),
    (3,2), (5,0), (4,2), (5,3), (5,1), (5,2)]

/-- Four-position images, not permutations of an increasing face-vertex list. -/
def rowSigma : Fin 12 → Fin 4 → Fin 4 :=
  ![![0,2,1,3], ![0,2,1,3], ![2,1,0,3], ![1,0,2,3],
    ![0,2,1,3], ![0,2,1,3], ![0,2,1,3], ![0,2,1,3],
    ![0,2,1,3], ![1,0,2,3], ![1,0,2,3], ![0,2,1,3]]

/-- Checks the sigma derived by the existing actual frame, for every position. -/
theorem literal_rows : ∀ r : Fin 12,
    literalPairing.facePair (rowSource r) = rowTarget r ∧
      ∀ v : Fin 4, sigma literalPairing (rowSource r) v = rowSigma r v := by decide

/-- Reverse rows use the inverse of the same original four-position map. -/
theorem literal_inverse_rows : ∀ r : Fin 12,
    literalPairing.facePair (rowTarget r) = rowSource r ∧
      ∀ v : Fin 4, sigma literalPairing (rowTarget r) (rowSigma r v) = v := by decide

/-- Exactly the designated endpoint table, in slots 01,02,03,23,13,12. -/
def chosenEndpoint : Fin 6 → Fin 6 → Fin 4 :=
  ![![0,0,0,2,1,2],
    ![0,2,0,2,1,2],
    ![1,2,0,2,1,1],
    ![1,2,0,2,1,1],
    ![1,0,0,2,1,1],
    ![0,0,0,2,1,2]]

/-- The degenerate-dart value only makes the label total; roots remain unequal. -/
def endpointLabel (d : Dart (Fin 6)) : Bool :=
  if d.1.2 = d.2 then false
  else decide (d.1.2 = chosenEndpoint d.1.1 (edgeIndex d.1.2 d.2))

/-- Finite certificate on the original dartMove, including all face choices. -/
theorem endpoint_transport : ∀ (t : Fin 6) (v w f : Fin 4),
    f ≠ v → f ≠ w →
      endpointLabel (dartMove literalPairing f ((t,v),w)) =
        endpointLabel ((t,v),w) := by decide

/-- Finite certificate that the designated endpoint distinguishes the two ends. -/
theorem endpoint_swap : ∀ (t : Fin 6) (v w : Fin 4), v ≠ w →
    endpointLabel (swap ((t,v),w)) = !(endpointLabel ((t,v),w)) := by decide

theorem endpoint_step {d e : Dart (Fin 6)} (h : DartStep literalPairing d e) :
    endpointLabel d = endpointLabel e := by
  obtain ⟨f,hfv,hfw,rfl⟩ := h
  exact (endpoint_transport d.1.1 d.1.2 d.2 f hfv hfw).symm

/-- The invariant uses the complete original generated relation. -/
theorem endpoint_related {d e : Dart (Fin 6)} (h : DartRelated literalPairing d e) :
    endpointLabel d = endpointLabel e := by
  induction h with
  | rel d e h => exact endpoint_step h
  | refl d => rfl
  | symm d e _ ih => exact ih.symm
  | trans d e a _ _ hde hea => exact hde.trans hea

theorem localNoEdgeReversal (d0 : OrderedEnd (Fin 6)) :
    LocalNoEdgeReversal literalPairing d0 := by
  intro h
  have heq : endpointLabel d0.val = !(endpointLabel d0.val) :=
    (endpoint_related h).trans
      (endpoint_swap d0.val.1.1 d0.val.1.2 d0.val.2 d0.property)
  have hne : ∀ b : Bool, b ≠ !b := by decide
  exact hne _ heq

end D5.S3.Geometry.Gluing.LiteralSixPairingCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.paired_involutive,
      ``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.paired_fixedFree,
      ``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.slot_inverse,
      ``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.literalPairing,
      ``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.literal_rows,
      ``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.literal_inverse_rows,
      ``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.endpoint_transport,
      ``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.endpoint_swap,
      ``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.endpoint_step,
      ``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.endpoint_related,
      ``D5.S3.Geometry.Gluing.LiteralSixPairingCandidate.localNoEdgeReversal] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1333 literal six-pairing target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1333 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1333 CHECKED {name} axioms={axioms}"
