---
bibkey: koljancic2026nssp
authors: Sara Koljančić and Polona Oblak
year: 2026
title: Combinatorial aspects of the non-symmetric Strong Spectral Property for graphs
doi: 10.48550/arXiv.2604.21552
url: https://arxiv.org/abs/2604.21552v1
claim: Question 5.11 asks whether every even double path with a nonempty loop set allows the nSSP.
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath
license: CC-BY-SA-4.0
triage: anchor
---

## Source correspondence

The primary source is arXiv:2604.21552v1. Definition 1.1 says that a real matrix A has nSSP if the only real X satisfying entrywise A times X equal to zero and the commutator of A with the transpose of X equal to zero is X equal to zero. There is no additional diagonal annihilation condition, symmetry condition or restriction on X.

Definition 1.3 distinguishes requiring nSSP, a universal statement over matrices of a pattern, from allowing nSSP, an existential statement. Definition 1.5 supplies the double-path loop notation. The zero–nonzero pattern is exact: an entry is nonzero if and only if its ordered pair is an arc.

Question 5.11 asks whether an even double path with a nonempty loop set allows nSSP. In the formal statement, the vertices are Fin n, both orientations of every consecutive path edge occur, and the remaining arcs are exactly the specified loops. The source's vertex i corresponds to Fin n value i minus one. The existential witness is unrestricted real.

Lemma 1.2, the Superpattern Lemma, supplies an nSSP witness on every superpattern of a pattern that admits an nSSP witness; its conclusion also preserves similarity. This published lemma is a mathematical input requiring a Lean proof or an admissible compiled supplier before it can discharge the formal event.

The later Electronic Journal of Linear Algebra publication, volume 42, pages 755–779, still states the question on PDF page 22, printed page 776. This locator is bounded source-qualification evidence; it is not a claim of exhaustive worldwide nonresolution or priority.

## License boundary

The arXiv source is licensed CC BY-SA 4.0. The publisher-specific license is unverified. No author code, source archive or publisher license is incorporated into the formal module. The Lean definitions and proofs are repository-authored, with the source correspondence given above.

## Formal boundary

The declaration `weighted_path_charpoly` identifies every zero-diagonal weighted branch characteristic polynomial with its squared-weight continuant. The declaration `continuant_linearization` identifies the constant and first-order coefficients of the simultaneous polynomial perturbation with the original continuant and its formal variation. The declaration `branch_variation_injective` recovers all internal edge variations from two consecutive zero variations at nonzero edge parameters.

The declaration `coprime_positive_branches` constructs strictly positive squared-edge sequences with coprime continuants for every pair of opposite-parity branch lengths, including empty branches. The declaration `joined_variation_injective` proves injectivity of the simultaneous algebraic joined perturbation coefficient at a nonzero central loop and nonzero edge parameters, conditional on coprime branches and an odd sum of branch lengths. It retains all six product-rule contributions and consumes the branch linearization and reverse-recovery results.

These relations do not yet prove the actual central-loop matrix characteristic identity, its support-tangent correspondence, the unrestricted commutant/trace pairing or exact support enlargement. They therefore do not construct an nSSP witness for Question 5.11. The full event remains the separate proposition `KoljancicOblakEvenPath.claim`.
