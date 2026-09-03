/- GID: D5/S3/ObserverMemory/Refinement/ProductCoordinateTransversality
   generality: G
   mirror-B: none(waiver:new-observer-library-node)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Product coordinates have transverse fibers and commuting independent updates. -/

import D5.S3.ObserverMemory.Refinement.JointReadoutSupremum
import Mathlib.Data.Set.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Refinement.ProductCoordinateTransversality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ObserverMemory.Refinement.JointReadoutSupremum

universe u v

/-- A carrier with independent local-channel and layer coordinates. -/
abbrev ProductCoordinate (Local : Type u) (Layer : Type v) := Local × Layer

/-- States lying over one local channel. -/
def localFiber {Local : Type u} {Layer : Type v} (local : Local) :
    Set (ProductCoordinate Local Layer) :=
  {state | state.1 = local}

/-- States lying in one layer. -/
def layerFiber {Local : Type u} {Layer : Type v} (layer : Layer) :
    Set (ProductCoordinate Local Layer) :=
  {state | state.2 = layer}

/-- A local fiber and a layer fiber meet in exactly one coordinate pair. -/
theorem local_fiber_inter_layer_fiber
    {Local : Type u} {Layer : Type v}
    (local : Local) (layer : Layer) :
    localFiber (Layer := Layer) local ∩
        layerFiber (Local := Local) layer =
      {(local, layer)} := by
  ext state
  constructor
  · intro hstate
    apply Set.mem_singleton_iff.mpr
    exact Prod.ext hstate.1 hstate.2
  · intro hstate
    rcases Set.mem_singleton_iff.mp hstate with rfl
    exact ⟨rfl, rfl⟩

/-- Update only the local coordinate. -/
def localMove {Local : Type u} {Layer : Type v}
    (update : Local → Local) :
    ProductCoordinate Local Layer → ProductCoordinate Local Layer :=
  fun state => (update state.1, state.2)

/-- Update only the layer coordinate. -/
def layerMove {Local : Type u} {Layer : Type v}
    (update : Layer → Layer) :
    ProductCoordinate Local Layer → ProductCoordinate Local Layer :=
  fun state => (state.1, update state.2)

/-- Independent local and layer updates commute. -/
theorem local_move_layer_move_commute
    {Local : Type u} {Layer : Type v}
    (localUpdate : Local → Local) (layerUpdate : Layer → Layer) :
    Function.Commute (localMove (Layer := Layer) localUpdate)
      (layerMove (Local := Local) layerUpdate) := by
  intro state
  rfl

/-- Read only the local coordinate. -/
def localReadout {Local : Type u} {Layer : Type v} :
    Concept (ProductCoordinate Local Layer) Local :=
  Prod.fst

/-- Read only the layer coordinate. -/
def layerReadout {Local : Type u} {Layer : Type v} :
    Concept (ProductCoordinate Local Layer) Layer :=
  Prod.snd

/-- Read both transverse coordinates jointly using the repository's canonical
pair-readout construction. -/
def coordinateReadout {Local : Type u} {Layer : Type v} :
    Concept (ProductCoordinate Local Layer) (Local × Layer) :=
  pairReadout localReadout layerReadout

/-- The joint coordinate readout is the identity representation. -/
theorem coordinate_readout_eq_id
    {Local : Type u} {Layer : Type v} :
    coordinateReadout (Local := Local) (Layer := Layer) = id := by
  rfl

/-- Its kernel is the intersection of the two coordinate kernels. -/
theorem coordinate_readout_kernel
    {Local : Type u} {Layer : Type v} :
    Setoid.ker (coordinateReadout (Local := Local) (Layer := Layer)) =
      Setoid.ker (localReadout (Local := Local) (Layer := Layer)) ⊓
        Setoid.ker (layerReadout (Local := Local) (Layer := Layer)) := by
  exact pair_readout_kernel
    (localReadout (Local := Local) (Layer := Layer))
    (layerReadout (Local := Local) (Layer := Layer))

/-- Reading both coordinates is faithful. -/
theorem coordinate_readout_injective
    {Local : Type u} {Layer : Type v} :
    Function.Injective
      (coordinateReadout (Local := Local) (Layer := Layer)) := by
  rw [coordinate_readout_eq_id]
  exact Function.injective_id

/-- Moving locally is invisible to the layer-only observer. -/
@[simp] theorem layer_readout_local_move
    {Local : Type u} {Layer : Type v}
    (update : Local → Local) (state : ProductCoordinate Local Layer) :
    layerReadout (localMove update state) = layerReadout state :=
  rfl

/-- Moving between layers is invisible to the local-only observer. -/
@[simp] theorem local_readout_layer_move
    {Local : Type u} {Layer : Type v}
    (update : Layer → Layer) (state : ProductCoordinate Local Layer) :
    localReadout (layerMove update state) = localReadout state :=
  rfl

/-- A genuine local move is detected by the joint observer. -/
theorem local_move_detected_by_joint
    {Local : Type u} {Layer : Type v}
    (update : Local → Local) (state : ProductCoordinate Local Layer)
    (hchange : update state.1 ≠ state.1) :
    coordinateReadout (localMove update state) ≠ coordinateReadout state := by
  intro hsame
  exact hchange (congrArg Prod.fst hsame)

/-- A genuine layer move is detected by the joint observer. -/
theorem layer_move_detected_by_joint
    {Local : Type u} {Layer : Type v}
    (update : Layer → Layer) (state : ProductCoordinate Local Layer)
    (hchange : update state.2 ≠ state.2) :
    coordinateReadout (layerMove update state) ≠ coordinateReadout state := by
  intro hsame
  exact hchange (congrArg Prod.snd hsame)

#print axioms local_fiber_inter_layer_fiber
#print axioms local_move_layer_move_commute
#print axioms coordinate_readout_kernel
#print axioms coordinate_readout_injective
#print axioms local_move_detected_by_joint
#print axioms layer_move_detected_by_joint

end D5.S3.ObserverMemory.Refinement.ProductCoordinateTransversality
