# Sixth-order top pairing transfer fails

## Abstract

Sixth-order top pairing transfer is refuted by a positive finite mixture.

**Definition 1.1 (The proposed sixth-order implication).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.claim`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fixed constant C at least one, assume a sequence of finitely indexed families in real algebras with normalized linear functionals nonnegative on squares, with centered coordinates satisfying Y squared equals a Y plus b, one at most L at most H, absolute values of a and b at most C L, and index cardinality at most C H. Assume every coefficient family bounded by one has distinct-index moment at most C sqrt(H L) to its order at orders two through five. At order six require the distinct moment minus its perfect-pairing polynomial to have absolute value at most C (H L) cubed divided by H, uniformly in all bounded weights. The proposed implication says that L/H tending to zero forces the full sixth moment with unit weights minus its full-moment pairing polynomial, divided by (H L) cubed, to tend to zero.

**Theorem 1.2 (A symmetric mixture refutes the implication).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s contain exactly three indices. If both scalar families have absolute value at most a nonnegative B on s, and their pointwise differences have absolute value at most one, then the difference of their products has absolute value at most 3 B squared. A telescoping identity has three terms, each bounded by B squared.

For at least six available indices and six coefficient families bounded in absolute value by one, the arbitrary-order injective comparison bounds the omitted contribution by 15 N^5, and hence by the 36 N^5 bound used below. The injective assignments are counted by the sixth descending factorial, whereas the product of coefficient sums includes all assignments.

Let U be a finite label set with at most six elements, N a real number, and delta a real function on label subsets. Assume delta(V)=0 for every V contained in U with at most two elements. The sum over partial pairings P of U of N^card(P)*delta(U minus pairingSupport(P)) equals delta(U)+N times the sum of delta(U minus e) over all two-element subsets e of U. Disjointness gives card(pairingSupport(P))=2*card(P). Every pairing with at least two edges therefore leaves at most two labels and contributes zero. The empty pairing contributes delta(U); the singleton pairings correspond bijectively to two-element subsets. The identity is finite and requires no probabilistic assumptions.

For every real N>=100, sqrt(15)*N*(N-1)*(N-2)*(N-3)/N^2-3*(N-1)^2 is at least N^2/2. The falling product is at least N^4-6*N^3 and sqrt(15)>=15/4. This explicit inequality converts the four-label defect of the biased-cube model into a uniform positive quadratic contribution.

For real N>=1 and K<=sqrt(N), K*N^3*(sqrt(1/N)+1/N)<=2*N^3. Both K/sqrt(N) and K/N are at most one because sqrt(N)<=N. This bounds the transfer remainder after selecting a sufficiently large model size.

Let N>=1, C<=N, |delta6|<=C*N^2, delta4>=N^2/2, and |E|<=2*N^3. If V=delta6+15*N*delta4+E, then V>=N^3. The fifteen one-edge terms contribute at least (15/2)*N^3, while the sixth-order defect and remainder cost at most N^3 and 2*N^3 respectively.

Take L=1, H=N, a=0 and b=1. Sample Z with values plus or minus the fourth root of fifteen, each of mass one divided by twice the square root of fifteen, and zero with the remaining mass. Conditional on Z, sample N independent signs of mean Z/sqrt(N). For N at least four this is a probability distribution. Coordinate signs are centered and square to one. The mixing moments at orders zero through six are 1, 0, 1, 0, sqrt(15), 0 and 15. Products at distinct coordinates have moment m_r divided by sqrt(N) to the r, giving all lower moment bounds with constant four.

Write A_i for the sum of the i-th coefficient function. Removing noninjective sixth-order tuples changes the product of the A_i by at most 36 N to the fifth. Thus the sixth distinct moment differs from 15 times the product of the A_i divided by N cubed by at most 540 N squared. Every second distinct moment equals (A_i A_j minus the diagonal weight sum) divided by N. There are fifteen perfect pairings of six labels, and their rank-one terms have the same product. Perturbing their three factors costs at most 180 N squared in total. Consequently the uniform top distinct pairing defect is at most 720 N squared.

Apply quadratic_pairing_defect_transfer with unit weights and lower-moment constant four. Defects on at most two labels vanish, so only the empty partial pairing and the fifteen single-edge partial pairings remain. A four-label distinct defect is sqrt(15) times N(N-1)(N-2)(N-3)/N squared minus 3(N-1) squared. For N at least one hundred it is at least N squared divided by two. Each single-edge term multiplies it by N. Choose a fixed natural offset large enough that N=n+offset also dominates 720 and the square of the transfer-error constant. The empty-pairing defect then costs at most N cubed, the transfer error at most twice N cubed, and the full sixth defect is at least N cubed. Its normalized value is therefore always at least one, although L/H tends to zero.

This proves the top-order insufficiency assertion of Proposition 500.5 in FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II. The formal result uses an explicit positive lower bound rather than asserting the sharper numerical limit 15(sqrt(15)-3). The model is a finite probability counterexample; no assertion about prime correlations or the Riemann hypothesis follows.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.claim`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderTopPairingRefutation.result`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MixtureMomentLemmas](MixtureMomentLemmas.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion](PairingDefectInversion.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount](PerfectPairingCount.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticFourthExpansion](QuadraticFourthExpansion.md)
