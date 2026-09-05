# Product Coordinate Transversality

## Abstract

Independent local and layer coordinates have singleton cross-fibers, commuting coordinate updates, and a faithful paired observer.

**Theorem 1.1 (A local fiber and a layer fiber meet in one state).**

$$\operatorname{intersection}(\operatorname{localFiber}(local), \operatorname{layerFiber}(layer)) = \{(local, layer)\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/ProductCoordinateTransversality.local_fiber_inter_layer_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixing both independent coordinates identifies exactly one product state.

This is the set-theoretic transversality used for local-channel and golden-layer addresses; no metric or inner-product orthogonality is asserted.

**Theorem 1.2 (Independent coordinate moves commute).**

$$\operatorname{localMove} \circ \operatorname{layerMove} = \operatorname{layerMove} \circ \operatorname{localMove}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/ProductCoordinateTransversality.local_move_layer_move_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An update confined to the local coordinate commutes with an update confined to the layer coordinate.

The paired repository readout is faithful and each single-coordinate readout remains blind to motion in the other direction.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/ProductCoordinateTransversality.local_fiber_inter_layer_fiber`
- Truth anchor: `D5/S3/ObserverMemory/Refinement/ProductCoordinateTransversality.local_move_layer_move_commute`
- Dependency: [D5/S3/ObserverMemory/Refinement/JointReadoutSupremum](JointReadoutSupremum.md)
