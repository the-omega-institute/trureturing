# Coherent coordinates, discard and record relabeling

## Abstract

Trace-preserving PSD order coordinates give first-pair discard and all six label permutations on the actual triple.

**Definition 1.1 (Coordinates on the fixed pair and triple).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.CoherentCoordinates`

*Formalization.* `D5/S3/Quantum/Foundation/TripleMatrixRecords.CoherentCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The singleton coordinates are the identity. The pair and triple equivalences preserve trace and preserve PSD in both directions. In (30) they identify the given M with the tensor product and the given L(q,z) with the tensor of the coordinated q and z for every Hermitian pair vector q and every singleton z, including entangled pair inputs.

**Definition 1.2 (Construct the coordinates from the two actual pair readbacks).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.coherentCoordinates`

*Formalization.* `D5/S3/Quantum/Foundation/TripleMatrixRecords.coherentCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The two whole-PSD pair readbacks, both real spans and both exact unitary tensor forms give the coordinates. The scalar case n = 1 uses trivial transposition. The normalized forms are the explicit external proof inputs attributed to Xu, Zheng and Fošner, Main Theorem (1.1)–(1.2) and the one-factor Proposition 2.1. Equation numbers outside that citation refer to the Barnum–Hilgert Library note. https://doi.org/10.1017/S1446788714000603

**Theorem 1.3 (First-pair discard is positive on the entire actual triple).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

Transport the ordinary partial trace through the actual triple and pair equivalences.

**Theorem 1.4 (First-pair discard preserves the canonical trace).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_tp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_tp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The two coordinate changes and the partial trace preserve the trace.

**Theorem 1.5 (Read back the whole first pair).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_read`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

On the given L(q,z), the constructed map returns tr(z) times q for all q and z.

**Theorem 1.6 (Spanning makes the first-pair discard unique).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

Every real-linear map with this all-vector law equals the constructed map by Spans L. This identifies any p12 supplied in TripleMarginals through coherentCoordinatesOfTriple_marginal12.

**Theorem 1.7 (Permute the actual preparation labels).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_prep`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_prep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

Each of the six permutations σ of Fin 3 acts on the fixed triple. In target slot i the output preparation uses input f(σ i). At n = 1 every label permutation acts trivially.

**Theorem 1.8 (Each relabeling preserves PSD in both directions).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_psd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The map is the ordinary factor permutation conjugated by the triple coordinate equivalence.

**Theorem 1.9 (Each relabeling preserves trace).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_tp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_tp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

Reindexing rows and columns by the same permutation preserves the diagonal sum in coherent coordinates.

**Theorem 1.10 (Distinct permutations give distinct maps in an active sector).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_faithful`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_faithful` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

When n is at least two, diagonal Hermitian matrices distinguish coordinate permutations, and two singleton coordinates suffice to detect each slot label. Thus the action is faithful as well as positive and trace preserving.

**Theorem 1.11 (The relabelings compose on the whole triple).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_comp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

With the target-slot convention, applying σ and then τ gives the label map i ↦ σ(τ(i)). The two spans extend composition on actual nested preparations to every triple vector.

**Theorem 1.12 (Identify the supplied first-pair marginal).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.coherentCoordinatesOfTriple_marginal12`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.coherentCoordinatesOfTriple_marginal12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

Instantiating the construction with the actual TripleMarginals data identifies its supplied p12 by the all-vector readback and Spans L.

**Theorem 1.13 (Identify the actual retained-pair readbacks).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.retained_eq_marginal12_relabel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.retained_eq_marginal12_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The all-vector preparation law and the two spans identify each retained-pair map with the corresponding relabeling followed by first-pair discard.

**Theorem 1.14 (The retained readback is positive and trace preserving).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixRecords.retained_pair_psd_tp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixRecords.retained_pair_psd_tp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

In coherent coordinates the retained readback law determines both properties on the whole actual triple, by the positive trace-preserving relabeling and the first-pair discard.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.CoherentCoordinates`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.coherentCoordinates`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.coherentCoordinatesOfTriple_marginal12`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_psd`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_read`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_tp`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.marginal12_unique`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_comp`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_faithful`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_prep`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_psd`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.recordRelabel_tp`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.retained_eq_marginal12_relabel`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixRecords.retained_pair_psd_tp`
- Dependency: [D5/S3/Quantum/Foundation/PositiveMarginalMatrixTriple](PositiveMarginalMatrixTriple.md)
- Dependency: [D5/S3/Quantum/Foundation/TripleMatrixOrientation](TripleMatrixOrientation.md)
