# Good Datum Exists

## Abstract

Good Datum Exists

Constant terms of the chain's finite data are admissible sums with controlled denominators. An invariant admissible combination yields a good datum computing the definite chain.

**Theorem 1.1 (exists_isGoodDatum_of_invariant).**

Lean statement: `D5/S3/Zeros/GRH/New/Seesaw/GoodDatumExists.exists_isGoodDatum_of_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Seesaw/GoodDatumExists.exists_isGoodDatum_of_invariant` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For a twist ϑ, q = ∏_Q Nv, let w be an admissible combination of the Data.reducedVacuum t, t in Data.admissibleTranslations q (denominator 1, size ≤ Data.cutBound^{3m} if Q = ∅), fixed by ∏ K_j with last component 1. Then for some good datum Ψ the chain of paired lifts with datum w equals ∑_t Ψ(t)·(chain with data Data.translateDatum t) on all smooth forms on X₀.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Seesaw/GoodDatumExists.exists_isGoodDatum_of_invariant`
- Dependency: [D5/S3/Zeros/GRH/New/Seesaw/AdmissibleEvaluation](AdmissibleEvaluation.md)
- Dependency: [D5/S3/Zeros/GRH/New/Seesaw/PairTensorData](PairTensorData.md)
