import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber

abbrev cardinalitySignature : Signature where
  Params := Unit
  State _ := CoarseHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def cardinalityActual : Realization cardinalitySignature :=
  realize cardinalitySignature (fun _ _ g => Fintype.card (CompatCache g))
    (fun e => nomatch e)

def cardinalityRejected : Realization cardinalitySignature :=
  realize cardinalitySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev cardinalityArena : Arena where
  signature := cardinalitySignature
  Law R := ∀ g : CoarseHistory, R.readout () () g = 2 ^ noneCount g

theorem cardinality_actual_law : cardinalityArena.Law cardinalityActual :=
  compatible_cache_card

theorem cardinality_rejected_law : ¬ cardinalityArena.Law cardinalityRejected := by
  intro h
  have impossible := h []
  change 0 = 1 at impossible
  cases impossible

def cardinalityProof : Registration cardinalityArena
    (∀ g : CoarseHistory, Fintype.card (CompatCache g) = 2 ^ noneCount g) where
  actual := cardinalityActual
  bridge := Iff.rfl
  variation := ⟨cardinality_actual_law, cardinalityRejected, cardinality_rejected_law⟩
  sensitivity := ⟨fun i => ⟨cardinalityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cardinality_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), [], [⟨[], none⟩], ?_⟩
    change Fintype.card (CompatCache []) ≠ Fintype.card (CompatCache [⟨[], none⟩])
    rw [compatible_cache_card, compatible_cache_card]
    decide

def compatible_cache_card_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber.compatible_cache_card)
    (Realization cardinalitySignature) (Type) (Unit) where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber.compatible_cache_card
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber.cardinalityProof
  realizationSource := none
  generated := false
  arena := .source ⟨cardinalityArena⟩
  objectArena := .source ⟨cardinalityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cardinalityArena ⟨cardinalityProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cardinalitySignature
    (fun _ _ g => Fintype.card (CompatCache g)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev projectionSignature : Signature where
  Params := Unit
  State _ := D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination.RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CoarseHistory
  Anchor := Empty
  finiteAnchor := inferInstance

def projectionActual : Realization projectionSignature :=
  realize projectionSignature
    (fun _ _ h => D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory.kappa_hist h)
    (fun e => nomatch e)

def projectionRejected : Realization projectionSignature :=
  realize projectionSignature (fun _ _ _ => []) (fun e => nomatch e)

abbrev projectionArena : Arena where
  signature := projectionSignature
  Law R := ∀ (g : CoarseHistory) (c : CompatCache g), R.readout () () (decode g c) = g

private theorem projection_rejected_law : ¬ projectionArena.Law projectionRejected := by
  intro h
  have impossible := h [⟨[], none⟩] (⟨.branch, rfl⟩, PUnit.unit)
  cases impossible

def projectionProof : Registration projectionArena
    (∀ (g : CoarseHistory) (c : CompatCache g),
      D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory.kappa_hist (decode g c) = g) where
  actual := projectionActual
  bridge := Iff.rfl
  variation := ⟨decode_projection, projectionRejected, projection_rejected_law⟩
  sensitivity := ⟨fun i => ⟨projectionRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, projection_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), [], [⟨[], .alpha⟩], ?_⟩
    intro impossible
    cases impossible

def decode_projection_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber.decode_projection)
    (Realization projectionSignature) (Type) (Unit) where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber.decode_projection
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber.projectionProof
  realizationSource := none
  generated := false
  arena := .source ⟨projectionArena⟩
  objectArena := .source ⟨projectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source projectionArena ⟨projectionProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectionSignature projectionActual.readout projectionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev decoderSignature : Signature where
  Params := CoarseHistory
  State g := CompatCache g
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination.RawHistory
  Anchor := Empty
  finiteAnchor := inferInstance

def decoderActual : Realization decoderSignature :=
  realize decoderSignature (fun _ g c => decode g c) (fun e => nomatch e)

abbrev injectivityArena : Arena where
  signature := decoderSignature
  Law R := ∀ g, Function.Injective (R.readout () g)

abbrev surjectivityArena : Arena where
  signature := decoderSignature
  Law R := ∀ g h, D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory.kappa_hist h = g →
    ∃ c, R.readout () g c = h

abbrev packingArena : Arena where
  signature := decoderSignature
  Law R := ∀ g h (equal : D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory.kappa_hist h = g),
    R.readout () g (pack g h equal) = h

abbrev addressesArena : Arena where
  signature := decoderSignature
  Law R := ∀ g c, (R.readout () g c).map Sigma.fst = g.map Sigma.fst

theorem injectivity_bridge : (type_of% (@decode_injective)) ↔ injectivityArena.Law decoderActual := Iff.rfl
theorem surjectivity_bridge : (type_of% (@decode_surjective)) ↔ surjectivityArena.Law decoderActual := Iff.rfl
theorem packing_bridge : (type_of% (@decode_pack)) ↔ packingArena.Law decoderActual := Iff.rfl
theorem addresses_bridge : (type_of% (@decode_addresses)) ↔ addressesArena.Law decoderActual := Iff.rfl

theorem injectivity_actual_law : injectivityArena.Law decoderActual := decode_injective
theorem surjectivity_actual_law : surjectivityArena.Law decoderActual := decode_surjective
theorem packing_actual_law : packingArena.Law decoderActual := decode_pack
theorem addresses_actual_law : addressesArena.Law decoderActual := decode_addresses

def decoderRejected : Realization decoderSignature :=
  realize decoderSignature (fun _ _ _ => []) (fun e => nomatch e)

theorem injectivity_rejected_law : ¬ injectivityArena.Law decoderRejected := by
  intro h
  let g : CoarseHistory := [⟨[], none⟩]
  let branchCache : CompatCache g := (⟨.branch, rfl⟩, PUnit.unit)
  let absentCache : CompatCache g := (⟨.absent, rfl⟩, PUnit.unit)
  have caches_ne : branchCache ≠ absentCache := by
    intro equality
    have replies := congrArg (fun c : CompatCache g => c.1.val) equality
    cases replies
  exact caches_ne (h g (by rfl))

def injectivityProof : Registration injectivityArena
    (∀ g, Function.Injective (decoderActual.readout () g)) where
  actual := decoderActual
  bridge := Iff.rfl
  variation := ⟨injectivity_actual_law, decoderRejected, injectivity_rejected_law⟩
  sensitivity := ⟨fun i => ⟨decoderRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, injectivity_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    let g : CoarseHistory := [⟨[], none⟩]
    let branchCache : CompatCache g := (⟨.branch, rfl⟩, PUnit.unit)
    let absentCache : CompatCache g := (⟨.absent, rfl⟩, PUnit.unit)
    refine ⟨g, branchCache, absentCache, ?_⟩
    intro equality
    have heads := List.cons.inj equality
    exact (show branchCache.1.val ≠ absentCache.1.val by decide)
      (congrArg (fun a => a.2) heads.1)

noncomputable def decode_injective_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber.decode_injective)
    (Realization decoderSignature) (Type) (Unit) where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber.decode_injective
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber.injectivityProof
  realizationSource := none
  generated := false
  arena := .source ⟨injectivityArena⟩
  objectArena := .source ⟨injectivityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source injectivityArena ⟨injectivityProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize decoderSignature
    (fun _ g c => decode g c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms injectivity_bridge
#print axioms surjectivity_bridge
#print axioms packing_bridge
#print axioms addresses_bridge

#print axioms projectionProof
#print axioms decode_projection_registration
#print axioms cardinalityProof
#print axioms compatible_cache_card_registration
#print axioms injectivityProof
#print axioms decode_injective_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber
