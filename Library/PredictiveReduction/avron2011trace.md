---
bibkey: avron2011trace
authors: Haim Avron; Sivan Toledo
year: 2011
title: Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix
doi: 10.1145/1944345.1944349
url: https://research.ibm.com/publications/randomized-algorithms-for-estimating-the-trace-of-an-implicit-symmetric-positive-semi-definite-matrix
claim: Randomized quadratic-form probes estimate a positive matrix trace with probabilistic relative-error sample guarantees.
strata_touched:
  - D5/S3/ObserverMemory/Trajectories/FibonacciNearReturn
license: citation-only
triage: anchor
---

# Random probes as a separately budgeted validation experiment

Journal of the ACM 58(2), Article 8 (2011). The author/institutional publication record and IBM abstract were read. A readable full paper was not obtained, so this note does not claim to have checked the source's individual constants or proofs.

The Section 19 draft stacks dyadic-time intertwining errors into a matrix M and estimates trace(M* M) with independent complex Gaussian probes. The one-sided lower-tail bound used there is derived directly from exponential moment generating functions; it is not quoted as an unchecked theorem from this source. The underlying randomized trace-estimation method is prior art.

The map must be fixed before the independent validation probes are drawn, or additional uniform/adaptive-control arguments are required. Output error is included through a separate RMS budget. Drawing arbitrary Gaussian vectors in matrix space does not by itself define a physically available quantum state preparation, and access to matrix actions must be counted. The sample statement does not follow from or add a claim to the existing Fibonacci Lean theorem.
