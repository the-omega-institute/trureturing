# The actual extreme Khovanov row of an eleven-crossing four-braid

## Abstract

The actual extreme Khovanov row of an eleven-crossing four-braid

Przytycki and Silvero formulate the link-level graded constraint in Section 9.1 of arXiv:2305.18648v1. The diagram is the closure of the braid with signed generator indices (1, 2, 1, 1, -3, 2, 2, -3, 2, 1, 2).

**Theorem 1.1 (A four-strand presentation with the forbidden graded row).**

Lean statement: `D5/S3/Topology/FourBraidKhovanovCounterexample.fourBraid_integral_extreme_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FourBraidKhovanovCounterexample.fourBraid_integral_extreme_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Józef H. Przytycki; Marithania Silvero (2024). *Khovanov homology, wedges of spheres and complexity*. DOI: [10.1007/s13398-024-01594-z](https://doi.org/10.1007/s13398-024-01594-z). URL: <https://arxiv.org/abs/2305.18648v1>.

*Commentary.*

The signed cube has empty bases in all higher rows other than quantum degrees 21 and 19, which are acyclic. The nonzero row at degree 17 corresponds to framed quantum degree -13. Its rank-two group lies in framed degree -3 above the singleton in degree -5. This order violates the graded alternatives in Corollary 1.6 and supplies a counterexample to the link-level conjecture of Section 9.1.

**Theorem 1.2 (Refutation of the Section 9.1 graded constraint).**

Lean statement: `D5/S3/Topology/FourBraidKhovanovCounterexample.gradedExtremeClaim_refuted`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FourBraidKhovanovCounterexample.gradedExtremeClaim_refuted` (`✓ std3`). ∎

*Resolves.* `Problems/przytycki-silvero-2024-four-braid-extreme-khovanov` (refuted) by `D5/S3/Topology/FourBraidKhovanovCounterexample.gradedExtremeClaim_refuted`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"przytycki-silvero-2024-four-braid-extreme-khovanov","declaration_gid":"D5/S3/Topology/FourBraidKhovanovCounterexample.gradedExtremeClaim_refuted","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Józef H. Przytycki; Marithania Silvero (2024). *Khovanov homology, wedges of spheres and complexity*. DOI: [10.1007/s13398-024-01594-z](https://doi.org/10.1007/s13398-024-01594-z). URL: <https://arxiv.org/abs/2305.18648v1>.

*Commentary.*

Every link presented as a four-strand braid has braid index at most four. The proposed list must therefore contain the actual extreme row of this closure if the conjecture holds. The computed row violates that necessary consequence.

## References

- Truth anchor: `D5/S3/Topology/FourBraidKhovanovCounterexample.fourBraid_integral_extreme_counterexample`
- Truth anchor: `D5/S3/Topology/FourBraidKhovanovCounterexample.gradedExtremeClaim_refuted`
- Dependency: [D5/S3/Topology/FourBraidKhovanovQuantum17](FourBraidKhovanovQuantum17.md)
- Dependency: [D5/S3/Topology/FourBraidKhovanovQuantum19](FourBraidKhovanovQuantum19.md)
- Dependency: [D5/S3/Topology/FourBraidKhovanovQuantum21](FourBraidKhovanovQuantum21.md)
