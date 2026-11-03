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
  - D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPathNSSP
license: CC-BY-SA-4.0
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2604.21552

Source: https://arxiv.org/abs/2604.21552v1

## Source correspondence

The primary source is arXiv:2604.21552v1. Definition 1.1 says that a real matrix A has nSSP if the only real X satisfying entrywise A times X equal to zero and the commutator of A with the transpose of X equal to zero is X equal to zero. There is no additional diagonal annihilation condition, symmetry condition or restriction on X.

Definition 1.3 distinguishes requiring nSSP, a universal statement over matrices of a pattern, from allowing nSSP, an existential statement. Definition 1.5 supplies the double-path loop notation. The zero–nonzero pattern is exact: an entry is nonzero if and only if its ordered pair is an arc.

Question 5.11 asks whether an even double path with a nonempty loop set allows nSSP. In the formal statement, the vertices are Fin n, both orientations of every consecutive path edge occur, and the remaining arcs are exactly the specified loops. The source's vertex i corresponds to Fin n value i minus one. The existential witness is unrestricted real.

Lemma 1.2, the Superpattern Lemma, supplies an nSSP witness on every superpattern of a pattern that admits an nSSP witness; its conclusion also preserves similarity. This published lemma is a mathematical input requiring a Lean proof or an admissible compiled supplier before it can discharge the formal event.

The later Electronic Journal of Linear Algebra publication, volume 42 (2026), pages 755–779, DOI [10.13001/ela.2026.10523](https://doi.org/10.13001/ela.2026.10523), still states the question on PDF page 22, printed page 776. The [publisher article page](https://journals.uwyo.edu/index.php/ela/article/view/10523) identifies the authors, title, DOI, volume and page range. The primary arXiv version remains DOI [10.48550/arXiv.2604.21552](https://doi.org/10.48550/arXiv.2604.21552), version 1 as linked above. This locator is bounded source-qualification evidence; it is not a claim of exhaustive worldwide nonresolution or priority.

## License boundary

The arXiv source is licensed CC BY-SA 4.0. The publisher article page records copyright in the names of Sara Koljančić and Polona Oblak. The [journal submission agreement](https://journals.uwyo.edu/index.php/ela/about/submissions) leaves copyright with the authors and grants the journal a worldwide, irrevocable, non-exclusive, royalty-free publication and distribution license. That grant does not establish a public reuse license for the publisher edition; its separate reuse license remains unverified, and the arXiv license is not attributed to it. No author code, source archive or publisher license is incorporated into the formal module. The Lean definitions and proofs are repository-authored, with the source correspondence given above.

## Formal boundary

The declaration `weighted_path_charpoly` identifies every zero-diagonal weighted branch characteristic polynomial with its squared-weight continuant. The declaration `continuant_linearization` identifies the constant and first-order coefficients of the simultaneous polynomial perturbation with the original continuant and its formal variation. The declaration `branch_variation_injective` recovers all internal edge variations from two consecutive zero variations at nonzero edge parameters.

The declaration `coprime_positive_branches` constructs strictly positive squared-edge sequences with coprime continuants for every pair of opposite-parity branch lengths, including empty branches. The declaration `joined_variation_injective` proves injectivity of the simultaneous algebraic joined perturbation coefficient at a nonzero central loop and nonzero edge parameters, conditional on coprime branches and an odd sum of branch lengths. It retains all six product-rule contributions and consumes the branch linearization and reverse-recovery results.

The declaration `joined_path_charpoly` identifies the actual one-loop weighted-path characteristic polynomial with P_left(r+1) P_right(s) + P_left(r) P_right(s+1) - (X+C(a)) P_left(r) P_right(s), with squared real edge weights. Its matrix carrier `joinedPath` places the loop at vertex r in Fin(s+1+r); all real weights and every pair of branch lengths are included, without nonzero, parity or spectral hypotheses. Empty branches and endpoint loops are covered. This expression equals the algebraic joined expression used in `joined_variation_injective`.

The declaration `joined_path_charpoly_derivative` gives the actual derivative at perturbation parameter zero of every real spectral evaluation of the characteristic polynomial, along arbitrary real edge variations and the central-loop variation. It identifies the squared-edge variations with twice the edge weight times its variation and the derivative with the evaluated complete `joinedVariation`.

The companion `KoljancicOblakEvenPathNSSP.result` has the exact type `KoljancicOblakEvenPath.claim`. Positive square roots supply real edge weights with the required squared parameters. The original `GibbsStochasticSimpleSpectrum.jacobi_simple` supplier, whose statement and proof are unchanged, supplies simple spectrum for this actual nonzero weighted Jacobi matrix. The Hermitian spectral theorem and the roots/eigenvalues correspondence give the required real orthogonal diagonalization with distinct spectral entries.

The support-tangent spectral readout is injective by the evaluated characteristic derivative and complete joined recovery, hence surjective in equal finite dimensions. An arbitrary real commuting test matrix becomes diagonal in this basis. Entrywise annihilation makes it trace-orthogonal to all support tangents, and pairing with its own diagonal readout gives a sum of squares, forcing the test matrix to vanish. No symmetry of the test matrix is assumed.

For every nonempty loop set, the proof chooses one of its vertices for this singleton construction. The nSSP condition is injectivity of the finite-dimensional linear test map sending X to its entrywise product with A and its transpose commutator with A. This family is continuous in A, and injectivity is open. A sufficiently small positive addition at exactly the other specified diagonal entries gives exact support for the entire loop set and preserves nSSP. This proves the existential event without using the stronger similarity conclusion in the published Superpattern Lemma. The algebraic source and final synthesis are frozen. The seven G recurrence, recovery, positive-coprime and matrix relations have content proofs and `escape-witness` admission. The I result is a bind-only synthesis relative to those relations and pinned/frozen suppliers, with `open-problem-resolution#25129` admission for the unchanged full event. The public consumed helper `joined_linearization` is bind-only and supplies no independent admission basis. All nine new public theorem/lemma audits remain unfinished: eight compiled attempts have unresolved verdicts, and `joined_linearization` has no attempt, record or template verdict. The [problem dossier](../../Problems/koljancic-oblak-2026-question-5-11-even-loop-path.md) names all nine and their evidence; the CLAUDE.md §3.9 disclosure is https://github.com/the-omega-institute/trureturing/issues/25129#issuecomment-6558078579 . No global priority claim is made.
