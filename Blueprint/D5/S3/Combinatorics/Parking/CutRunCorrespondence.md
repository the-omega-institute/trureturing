# Cut-Run Correspondence

## Abstract

Cut and uncut coordinates identify the circular first-free process with the classical linear parking run.

**Definition 1.1 (Cut the circle at a vacancy).**

Lean statement: `D5/S3/Combinatorics/Parking/CutRunCorrespondence.cutSpot`

*Formalization.* `D5/S3/Combinatorics/Parking/CutRunCorrespondence.cutSpot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

The linear coordinate of x relative to vacancy j is the canonical natural value of x-j, ranging from zero through n.

**Definition 1.2 (Restore a cut coordinate).**

Lean statement: `D5/S3/Combinatorics/Parking/CutRunCorrespondence.uncutSpot`

*Formalization.* `D5/S3/Combinatorics/Parking/CutRunCorrespondence.uncutSpot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

A natural linear coordinate p is placed back on the circle as j+p.

**Theorem 1.3 (Cutting identifies the two scanners).**

Lean statement: `D5/S3/Combinatorics/Parking/CutRunCorrespondence.firstFree_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/CutRunCorrespondence.firstFree_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Assume the occupied list has no duplicates, its length is at most n, j is unoccupied, and the circular scanner does not land at j. Cutting at j sends the circular first-free result to the supplier's linear parkStep. The proof rotates j to zero, orders every skipped offset before the cut, and applies the supplier's vacancy and skipped-position specification.

**Theorem 1.4 (The reverse scanner does not cross the vacancy).**

Lean statement: `D5/S3/Combinatorics/Parking/CutRunCorrespondence.firstFree_ne_vacancy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/CutRunCorrespondence.firstFree_ne_vacancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Let 1 <= p <= q <= n and suppose uncutSpot j q is free. The first circular free spot from uncutSpot j p cannot be j: the free offset q-p occurs strictly before the offset n+1-p that returns to the cut.

**Theorem 1.5 (Cutting simulates the complete one-choice run).**

Lean statement: `D5/S3/Combinatorics/Parking/CutRunCorrespondence.cut_run`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Parking/CutRunCorrespondence.cut_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Asma Recioui, Hacène Belbachir, Abdelhakim Ait-Zai (2026). *Circular s-choice parking functions: an exact closed formula via rotational symmetry*. DOI: [10.48550/arXiv.2609.23607](https://doi.org/10.48550/arXiv.2609.23607). URL: <https://arxiv.org/html/2609.23607v1>.

*Commentary.*

Assume a duplicate-free occupied state, enough remaining capacity, an unoccupied cut j, and a future one-choice run that never lands at j. Then supplier parkFrom on the cut occupied list and cut anchors equals the cut circular landing list. The same induction also proves that every input anchor differs from j.

## References

- Truth anchor: `D5/S3/Combinatorics/Parking/CutRunCorrespondence.cutSpot`
- Truth anchor: `D5/S3/Combinatorics/Parking/CutRunCorrespondence.cut_run`
- Truth anchor: `D5/S3/Combinatorics/Parking/CutRunCorrespondence.firstFree_cut`
- Truth anchor: `D5/S3/Combinatorics/Parking/CutRunCorrespondence.firstFree_ne_vacancy`
- Truth anchor: `D5/S3/Combinatorics/Parking/CutRunCorrespondence.uncutSpot`
- Dependency: [D5/S3/Combinatorics/Parking/OperationalDynamics](OperationalDynamics.md)
