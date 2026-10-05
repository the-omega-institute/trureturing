# Four-Exit Coarse Scan Attainment

## Abstract

Three real coarse scans and a rational tail law attain both orders of maximum cost.

**Theorem 1.1 (Simultaneous attainment by a finite rational law).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FourExitCoarseScanAttainment.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FourExitCoarseScanAttainment.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive k the evaluation family has one baseline and four exceptional rows per slot, each with n = 8k + 16 leaves. Branch and absent responses have one common coarse label. The retained slot, tail, and other slot scan kinds are chosen before execution. The scan coordinate at the retained slot is dummy; it is marginalized and has no effect, including when k=1.

The three scans place the second nonleaf request on A, Y, or Z. The three tails have excess vectors (1,0,1,2,1), (1,1,2,0,1), and (1,2,0,1,1) on the baseline and retained A, Y, H, Z rows. Every route selects its actual row. Complete leaf verification and full acquisition extend each route to a globally correct controller whose decisions depend only on coarse history.

On every evaluation row the set of addresses actually paid is exactly its leaf set together with the specified scan or tail nonleaf set. On the evaluation family each member has baseline excess one, maximum excess two, and total excess 5k. The cache merges repeated exact addresses from routing and verification.

For arbitrary nonnegative real tail weights (alpha,beta,gamma) and scan weights (dA,dY,dZ), each triple summing to one, the uniform retained-slot mixture is nonnegative and normalized. Expected costs are n+1 on the baseline, n+1+(-alpha+gamma+(k-1)dA)/k on A, n+1+(alpha-beta)/k on H, n+1+(beta-gamma+(k-1)dY)/k on Y, and n+1+(k-1)dZ/k on Z. The same controllers realize these identities for every such pair of triples.

The retained slot is uniform. Tail probabilities are (1/3,1/3,1/3) for k=1, (11/24,5/24,1/3) for k=2, ((k+3)/8,(5-k)/8,0) for 3<=k<=5, and (1,0,0) for k>=5. Scan probabilities are (3/8,3/8,1/4) for k=2, ((3k+1)/(8(k-1)),(3k-7)/(8(k-1)),1/4) for 3<=k<=5, and ((k+1)/(3(k-1)),(k-2)/(3(k-1)),(k-2)/(3(k-1))) for k>=5. The k=5 prescriptions agree; k=1 has no other slot.

This nonnegative normalized finite rational law has maximum expected cost n + max((5k-1)/(4k),(4k-2)/(3k)). On the evaluation family every selected controller has maximum cost n+2, so the same law has expected maximum cost n+2. The statement concerns actual address costs and does not impose an input prior. This result supplies attainment; the four-exit coarse lower bounds supply domination of other laws and, together with attainment, the unique nondominated pair.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FourExitCoarseScanAttainment.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion](ActualCoarseReadoutCompletion.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/FourExitRawDomination](FourExitRawDomination.md)
