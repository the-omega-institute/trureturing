# Actual facial boundaries and face-odd orientations

## Abstract

Exact actual-dart facial boundaries and face-odd orientations of even-order signed-Euler-two rotations.

Let V be an arbitrary finite vertex type with decidable equality, and G a connected simple graph on V with decidable adjacency and at least one actual dart. Rotation G consists of a permutation rho of G.Dart whose SameCycle classes are precisely the darts with a common first vertex. Reversal alpha sends a dart to its symm. The facial successor phi first reverses a dart and then applies rho. Face is the quotient by SameCycle phi, using integer powers and retaining every orbit, including singleton orbits. The edge type E is G.edgeSet, the subtype of actual unordered edges. No side, surface realization or parity property is included in Rotation.

The boundary linear map B takes a face function x with values in ZMod 2 to the edge function whose value is the sum of the two facial shore values. Its definition chooses an actual representative dart of each unordered edge. Its evaluation theorem proves that the sum is independent of that choice. Every cardinality in the Euler hypothesis is cast to the integers before subtraction: card(V) minus card(E) plus card(Face) equals two.

**Theorem 1.1 (The face boundary map is exact onto the actual cycle space).**

Lean statement: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.face_cycle_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.face_cycle_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

For every finite V, G and Rotation satisfying the stated connectedness, actual-dart nonemptiness and signed integer Euler equation, three conclusions hold together. For every face function x and actual dart d, B(x) on the unordered edge of d is x(face d) plus x(face alpha(d)). For every x, B(x) is zero if and only if there exists c in ZMod 2 such that x is the constant function with value c. The linear range of B equals SimpleGraphCycleSpace.simpleCycleSpace G, the existing span of indicators of actual simple cycles.

Zero boundary equates opposite shore values. Facial succession then equates values after a rotor step, and an actual graph walk propagates this equality between all faces. Reindexing a dart sum along phi proves that every facial boundary annihilates the vertex-to-edge differential. The existing finite_graph_cycle_space theorem identifies these relations with the existing cycle space. Rank-nullity, the one-dimensional constant kernel and the signed Euler equation establish equality of the two subspaces. Generic cycle rank and linear algebra are reused; geometric separation is not assumed.

**Theorem 1.2 (Facial succession preserves its actual face).**

Lean statement: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.face_step`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.face_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

For every actual dart d, face(facePerm d) equals face d, since Face is the complete SameCycle quotient of the actual facial successor.

**Theorem 1.3 (The boundary is independent of the chosen representative).**

Lean statement: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.boundary_dart`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.boundary_dart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

For every actual dart d and every binary facial labelling x, boundary x on the unordered edge of d equals x(face d) plus x(face d.symm). The two representatives of an unordered edge differ at most by reversal.

**Theorem 1.4 (Every facial boundary annihilates the vertex differential).**

Lean statement: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.boundary_relation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.boundary_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

For a finite vertex type with decidable graph adjacency, every facial labelling has boundary in BinaryCharacterCodeDuality.characterRelationSpace of the actual endpointCharacters G. Reindexing the complete dart sum by the facial successor cancels the endpoint contributions in ZMod 2.

**Theorem 1.5 (The facial boundary kernel consists of constants).**

Lean statement: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.boundary_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.boundary_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

For a connected graph on a finite vertex type with decidable adjacency, boundary x is zero if and only if there exists c in ZMod 2 with x equal to the constant function c. The statement includes the case with no actual darts or faces and uses neither Euler nor geometric assumptions.

**Theorem 1.6 (Unordered edge pairs enumerate all actual darts).**

Lean statement: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.sum_darts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.sum_darts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

For every additive commutative monoid K and every f from actual darts to K, the sum over actual unordered edges of f on the chosen representative and on its reverse equals the sum of f over all actual darts. The vertex type is finite and adjacency decidable; no rotation hypothesis is needed.

**Theorem 1.7 (Face-odd orientations exist for even vertex order).**

Lean statement: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.exists_face_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.exists_face_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

For every connected finite simple graph with decidable equality and adjacency, a nonempty actual dart type, a Rotation and signed integer Euler expression card(V) minus card(E) plus card(Face) equal to two, even card(V) implies existence of epsilon on actual darts with epsilon(d.symm) equal to one plus epsilon(d) and faceOpposition epsilon f equal to one for every complete face orbit. The proof solves the face defects through the dual of boundary, using the constant kernel and even total defect. This construction is consumed by the nice-cycle theorem in RotationFaces.

The faceOpposition definition counts every actual dart in its complete face orbit. The face-odd construction, facial kernel, dart evaluation and dart summation are used by the actual regional Euler and nice-cycle consumer in RotationFaces. These are finite combinatorial results; geometric realization, matching-sign transport, Pfaffian identities and complexity bounds remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.boundary_dart`
- Truth anchor: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.boundary_eq_zero_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.boundary_relation`
- Truth anchor: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.exists_face_odd`
- Truth anchor: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.face_cycle_exact`
- Truth anchor: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.face_step`
- Truth anchor: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary.sum_darts`
- Dependency: [D5/S3/Combinatorics/Graph/Brooks/ColoringExtension](../Brooks/ColoringExtension.md)
- Dependency: [D5/S3/Fourier/CharacterSelection/SimpleGraphCycleSpace](../../../Fourier/CharacterSelection/SimpleGraphCycleSpace.md)
