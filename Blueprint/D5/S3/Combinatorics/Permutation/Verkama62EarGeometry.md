# Geometry of an anchored two-vertex ear

## Abstract

Geometry of an anchored two-vertex ear.

**Definition 1.1 (An induced three-edge ear).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62EarGeometry.PairEar`

*Formalization.* `D5/S3/Combinatorics/Permutation/Verkama62EarGeometry.PairEar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

The new positions u < v have pi(v) < pi(u). They have distinct old attachments x,y, respectively, and no other neighbours in S. Both new positions lie outside S.

**Theorem 1.2 (The northeast orientation).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62EarGeometry.to_double`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62EarGeometry.to_double` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

Let S contain at least three points and the original leftmost point. Suppose the induced old stage remains connected after deleting each of its points. Every induced two-vertex ear has the northeast double-ear geometry, with its two new positions unchanged. Deleting an attachment puts all remaining old points on one common side of the corresponding new point. A common old point rules out opposite side choices. The southwest placement of the old points gives the required inequalities; the northeast placement contradicts the leftmost anchor. No pattern avoidance or triangle-freeness is assumed.

**Theorem 1.3 (Extension of every proper anchored stage).**

Lean statement: `D5/S3/Combinatorics/Permutation/Verkama62EarGeometry.anchored_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/Verkama62EarGeometry.anchored_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Emil Verkama (2026). *Permutation patterns and higher connectivity in inversion graphs*. DOI: [10.48550/arXiv.2611.17237](https://doi.org/10.48550/arXiv.2611.17237). URL: <https://arxiv.org/html/2611.17237v1>.

*Commentary.*

Assume the ambient value graph is connected after each single deletion and is connected. Let S contain at least three points, the original leftmost point z, and the original bottommost point b, with z distinct from b. Assume each old-point deletion leaves the induced old stage connected. If S is proper, there is an outside singleton with at least two old neighbours or a northeast double ear. If no singleton is available, every boundary point has a unique old attachment. Connectivity and connectivity after deleting that attachment give two distinct attachments. The two anchors force all other old points southwest of either boundary point. The two attachment inversions then have opposite orientations and form a two-vertex ear.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62EarGeometry.PairEar`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62EarGeometry.anchored_extension`
- Truth anchor: `D5/S3/Combinatorics/Permutation/Verkama62EarGeometry.to_double`
- Dependency: [D5/S3/Combinatorics/Permutation/Verkama62Graph](Verkama62Graph.md)
