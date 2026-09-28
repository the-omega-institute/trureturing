# Propagation of balanced face signatures

## Abstract

Face pairings preserve low opposite-edge counts along balanced dual paths.

Let each local edge of a tetrahedron carry an actual global edge label, and color the global labels low or high. Opposite balance means the two members of each local opposite-edge pair have the same color. The low-pair count reads one edge from each of the three pairs.

A compatible dual adjacency pairs one face of each tetrahedron. A permutation of the three face edges identifies their global labels. The tetrahedra and the global edge-label set need not be finite.

**Theorem 1.1 (The low-pair count is constant along balanced dual paths).**

$$\forall T \in Type, E \in Type, G \in SimpleGraph\left(T\right), edge \in T \to \left(Fin\left(6\right) \to E\right), low \in E \to Bool, s \in T, t \in T,\; faceGluingCompatible\left(G, edge\right) \Rightarrow \left(Reachable\left(balancedGraph\left(G, edge, low\right), s, t\right) \Rightarrow lowPairCount\left(edge, low, s\right) = lowPairCount\left(edge, low, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FaceSignaturePropagation.lowPairCount_eq_of_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For label-preserving face pairings, any two tetrahedra connected by a finite dual path through balanced tetrahedra have the same low-pair count. In particular, a tetrahedron with one low opposite pair cannot be connected to one with two low opposite pairs through balanced tetrahedra alone.

Each face contains one edge from each opposite pair, so its low-edge count equals the local low-pair count. A face pairing preserves this count because it only permutes three equal-colored global labels. Equality then propagates along the dual path.

The statement concerns colored edge incidence and face pairings; it assumes no lengths, angles, curvature bounds, or pre-existing geometric realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FaceSignaturePropagation.lowPairCount_eq_of_reachable`
- Dependency: [D5/S3/Geometry/Hyperideal/FaceSignatureBalance](FaceSignatureBalance.md)
