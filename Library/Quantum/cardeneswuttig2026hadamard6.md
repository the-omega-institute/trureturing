---
bibkey: cardeneswuttig2026hadamard6
authors: Mateo Cárdenes Wuttig, Joseph Tindall
year: 2026
title: A Complete Classification of Complex Hadamard Matrices of Order Six
doi: 10.48550/arXiv.2608.18053
claim: Every order-six complex Hadamard equivalence class is claimed to admit a dephased finite-corner witness; the public Lean audit exposes a paper-facing completeness and soundness theorem, while MUB use still requires a joint gauge-compatible extension certificate.
strata_touched:
  - D5/S3/Quantum/Tomography/MUBHadamardCompatibility
  - D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes
  - D5/S3/Quantum/Tomography/RankOneContextCommutator
license: citation-only
triage: anchor
---

# A Complete Classification of Complex Hadamard Matrices of Order Six

The August 2026 preprint proposes an exact finite-incidence classification of
complex Hadamard matrices of order six. The matrix is dephased and partitioned
around a `3 x 3` corner. The proof searches the finitely many positional
corners, reconstructs candidate completions by algebraic fibres, and proves a
routing statement: failure to obtain a finite-corner witness forces the matrix
onto the Karlsson locus or the Tao orbit. Separate exact certificates give
finite-corner witnesses on both exceptional loci. Completeness and soundness
then identify the retained output with all order-six complex Hadamard matrices,
first at matrix level and then at equivalence-class level.

The phrase "complete classification" therefore refers to an exact generating
and incidence framework. It should not be read as a short finite list of all
continuous equivalence classes. This distinction matters for the MUB problem,
which depends on simultaneous relative gauges among several matrices.

## Public Lean audit

The authors publish a Lean 4 repository named
`mateocardeneswuttig/all_hadamard_matrices_in_dimension_six`. This note pins the
inspection target to commit
`57b03025ecbe259e474281f49e201ea7cb474e34` from 2026-08-31.

The public theorem spine in `Hadamard6/PaperTheorem.lean` contains:

- `paper_failed_corner_search_forces_karlsson_or_tao`;
- `paper_karlsson_has_finite_corner`;
- `paper_tao_has_finite_corner`;
- `paper_finite_corner_theorem`;
- `paper_finite_corner_completeness` and
  `paper_finite_corner_soundness`;
- `paper_total_output_corollary` and
  `paper_classification_corollary`.

At the pinned commit, GitHub Actions run `33350075705` completed successfully.
Its build job ran Lean Action CI and then the repository's paper-facing theorem
boundary audit. This is reproducible upstream CI evidence. It is not a local
rebuild inside trureturing, and this note does not elevate a recent preprint to
an independently peer-reviewed theorem.

The upstream toolchain is Lean `v4.33.0-rc2`; trureturing currently uses Lean
`v4.33.0`. No source module is copied or imported in the present lane. The new
trureturing theorem instead accepts an explicit `IsExactHadamardAtlas`
hypothesis, so the external classification can only be consumed after its
interface is translated and verified on the repository's own carriers.

## MUB consumption boundary

A set of four MUBs in dimension six can be normalized by fixing one basis to
the coordinate basis. The other three bases become order-six complex Hadamard
matrices `H_1,H_2,H_3`, with every cross transition `H_rᴴ H_s` entry having
squared norm six.

Single-matrix standard equivalence permits independent left row monomials and
right column monomials. Pairwise MUB compatibility only tolerates a common
ambient left gauge, together with independent right basis gauges. Consequently
one cannot select one arbitrary representative from each classified Hadamard
class and test those representatives directly. The equivalence witnesses must
remain variables in the joint compatibility problem.

`MUBHadamardCompatibility.lean` formalizes this distinction as
`HasLiftedFourMUBWitness` and proves that every exact atlas reduces the problem
to that lifted triple search. It also gives an exact order-two counterexample
showing that independent Hadamard equivalence does not preserve pairwise
mutual unbiasedness.

## Verification status

- The preprint statement and proof architecture were checked against
  arXiv:2608.18053v1.
- The public Lean theorem spine was inspected at the pinned commit.
- The upstream successful GitHub Actions build and theorem-boundary audit were
  checked.
- No local byte-for-byte rebuild of the upstream project was performed in this
  lane.
- The order-six classification is not assumed by any Lean declaration added in
  this lane.

## Verified locators

- arXiv: https://arxiv.org/abs/2608.18053
- arXiv DOI: https://doi.org/10.48550/arXiv.2608.18053
- public Lean audit: https://github.com/mateocardeneswuttig/all_hadamard_matrices_in_dimension_six
- pinned commit: https://github.com/mateocardeneswuttig/all_hadamard_matrices_in_dimension_six/commit/57b03025ecbe259e474281f49e201ea7cb474e34
- successful upstream CI: https://github.com/mateocardeneswuttig/all_hadamard_matrices_in_dimension_six/actions/runs/33350075705
