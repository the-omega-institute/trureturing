# Hilbert clique phase reversal

## Abstract

The order of the Hilbert and real L1 reconstruction coefficients on finite chordal graphs reverses between clique cutoffs four and five. Scalar projection and averaging also give bounds in Euclidean dimensions two and three.

**Theorem 1.1 (Hilbert bound at clique number four).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_cliqueFour_hilbert_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_cliqueFour_hilbert_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite chordal graph whose cliques have at most four vertices, let skew gains in a real inner product space have triangle defects of norm at most a nonnegative budget. One potential bounds every edge residual by 259 over 200 times that budget.

Eliminate a simplicial vertex and put it back using the enclosing center of the earlier candidates. Center the three old residuals and the three triangle defects by their opposite means. Their sum gives the candidate edge energy. Contact weights control the variance using the total candidate energy and, when needed, a single short edge. Two rational polynomial certificates preserve the triangle invariant 23 over 5 while the new edge residuals stay below the stated bound.

**Theorem 1.2 (A single-interval Hilbert bound at clique number four).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_cliqueFour_hilbert_gain_potential_zeroSplit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_cliqueFour_hilbert_gain_potential_zeroSplit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same chordal graphs and real inner-product targets admit an edge error at most 13 over 10 times the triangle-defect budget.

Use the same three-candidate center with triangle invariant 93 over 20. The numerator and quartic are nonnegative combinations of products of powers of the squared defect and its complement on the full unit interval.

**Theorem 1.3 (Hilbert bound at clique number five).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_cliqueFive_hilbert_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_cliqueFive_hilbert_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite chordal graph with cliques of size at most five, skew gains in any real inner product space with triangle defects of norm at most a nonnegative budget admit a potential with every edge residual bounded by the square root of 10275 over 4576 times that budget.

Along reverse simplicial elimination, maintain triangle energy at most 329 over 50 and tetrahedron energy at most 621 over 50 after normalizing the budget. On a four-neighbor clique, the cycle projection has energy equal to one quarter of the total squared face holonomy. Removing that cycle component bounds the candidate diameter energy. The contact-weight estimate then improves the enclosing radius. For each new tetrahedron, the old triangle energy and the candidate face estimate preserve the invariant. A candidate inside the ball is included by adjusting the squared distances by its slack. Budget zero uses exact reconstruction.

**Theorem 1.4 (The clique-four comparison).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.hilbert_cliqueFour_phase_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.hilbert_cliqueFour_phase_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform Hilbert coefficient is at least two over the square root of three and at most 259 over 200. These bounds lie strictly above one and below four thirds, respectively. The uniform Banach coefficient is at least four thirds.

The lower estimate uses the regular-simplex family on chordal powers of finite paths of width three. The Hilbert upper estimate supplies an admissible uniform bound. The existing Banach lower estimate uses the same width. The exact coefficient one for nonzero real L1 at this cutoff is the previously frozen l1_clique_four_exact theorem.

**Theorem 1.5 (The clique-five comparison).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.hilbert_cliqueFive_phase_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.hilbert_cliqueFive_phase_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform Hilbert coefficient is at most the square root of 10275 over 4576, strictly below 2997 over 2000 and three halves. Every coefficient uniform over finite real L1 targets on this graph class is at least three halves.

All finite powers of paths of width four meet the clique cutoff. Apply the existing even-width real L1 obstruction to the balanced-cut coordinate space on this family. The Hilbert upper bound gives the opposite order from the clique-four comparison.

**Theorem 1.6 (The Hilbert and real L1 coefficient reversal).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.realL1_hilbert_banach_phase_reversal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.realL1_hilbert_banach_phase_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At clique number four, the real L1 coefficient is one and the Hilbert coefficient is strictly larger. At clique number five, the Hilbert coefficient is strictly less than three halves, and three halves is a lower bound for the real L1 coefficient, which is at most the Banach coefficient.

Every finite real L1 coordinate space is isometric to the L1 space of its counting measure, so the width-four lower bound survives in the uniform real L1 class. Real L1 spaces are Banach spaces. The clique-five group reconstruction gives a finite uniform upper bound for both classes.

**Theorem 1.7 (The Euclidean plane bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_euclideanPlane_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_euclideanPlane_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite chordal graph and every skew Euclidean-plane gain with triangle defects bounded by a nonnegative budget, one potential bounds every edge residual by four over pi times that budget. For n at least three vertices the factor improves by (n minus two) over n.

For each scalar direction, the triangle estimate bounds each simple cycle by its length minus two. Shortest directed walk costs then give a scalar potential. Removing nonnegative closed subwalks reduces the minimum to finitely many paths, so the scalar potentials depend continuously on the direction. Averaging them with a rotationally invariant Gaussian weight recovers the vector gain in the plane and yields four over pi from the radial and absolute coordinate moments.

**Theorem 1.8 (The three-dimensional Euclidean bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_euclideanSpaceThree_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_euclideanSpaceThree_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite chordal graphs and three-dimensional Euclidean gains under the same defect assumptions, the corresponding uniform factor is three halves with the finite-order improvement (n minus two) over n when n is at least three.

The same continuous scalar potentials and rotational averaging reduce the estimate to the Gaussian radial and absolute coordinate moments in dimension three. Graphs on fewer than three vertices have exact reconstruction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_cliqueFive_hilbert_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_cliqueFour_hilbert_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_cliqueFour_hilbert_gain_potential_zeroSplit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_euclideanPlane_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.exists_euclideanSpaceThree_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.hilbert_cliqueFive_phase_separation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.hilbert_cliqueFour_phase_separation`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal.realL1_hilbert_banach_phase_reversal`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata](ChordalBanachExactStrata.md)
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds](../ThreeTreeBanachSharpBounds.md)
