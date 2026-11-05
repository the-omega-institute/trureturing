# Compact Flat Sector Optimum

## Abstract

Compact flat bipartite sector encodings admit a simultaneous optimal local splitting channel, with error determined by the distinct logarithms of the residual ranks.

**Theorem 1.1 (The exact optimum on the compact physical carriers).**

Lean statement: `D5/S3/Quantum/Entanglement/SectorChannels/FiniteFlatSectorOptimum.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SectorChannels/FiniteFlatSectorOptimum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sectors form any nonempty finite set. Source and target ranks are arbitrary positive integers in each sector. A flat bipartite source can produce the exact flat target on every logical basis sector by local completely positive trace-preserving maps exactly when each source rank is the target rank times a positive integer residual rank.

For feasible ranks, split a local source coordinate into a target coordinate a and a residual coordinate b using the little-endian index a plus the target rank times b. Embed each residual space in one common finite environment by its initial segment. The resulting placement matrix is an isometry. Its tensor square intertwines the complete coherent source encoding with the padded encoding on every logical matrix, including the coherences between different sectors.

The embedding induces an actual quantum channel. A completely positive trace-preserving retraction inverts it on its image and resets the unused orthogonal complement to a fixed state. Tensoring these channels gives physical realizations on all matrices. Restriction and extension through this pair identify both sets of errors of arbitrary product channels on the compact and padded carriers.

Use the same splitting on both sides and discard the residual coordinate. Its local action is the partial trace of the placed physical input matrix. The joint output on a logical matrix is the target encoding of its Schur product with the residual Gram kernel. Each Gram entry is the square root of the smaller residual rank divided by the larger, equivalently the exponential of minus one half of the absolute difference of their logarithms. Every logical basis sector has exactly the target pure output.

Order the distinct residual ranks increasingly and let the loss labels be their logarithms. The sector-to-label map is surjective, and recovers each original residual rank. Summing probabilities over its fibers preserves the kernel energy. A section lifts every probability vector on the distinct labels, so repetitions do not alter the minimum. The exponential kernel equilibrium has minimum energy equal to the reciprocal of one plus T, where T sums the hyperbolic tangents of one quarter of each consecutive loss gap.

The finite sector channel optimum and the exponential kernel minimum therefore give unhalved diamond error two T divided by one plus T. The diamond distance includes every finite passive reference and every joint density input. The splitting product attains this value, which is a least element of the error set for all local product channels and also of the set constrained to exact target outputs on all basis sectors. Consequently the same value is the infimum of the latter set.

For target ranks (3,3,3) and source ranks (3,12,48), the residual ranks are (1,4,16). Both exponential-kernel edges are 1/2. The normalizer is 5/3, the equilibrium probabilities are (2/5,1/5,2/5), the minimum kernel energy is 3/5, and the optimal unhalved diamond error is 4/5.

If there is only one distinct residual rank, the gap sum is empty and the error is zero. In particular, this includes a single logical sector and any number of sectors with a common residual rank. The construction uses local quantum channels and a discarded environment, with no communication, postselection or additional shared entanglement.

For a conditional momentum application, let b>0, Q=b+1/b and c=1+6Q^2. Define S(P)=4 sinh(2 pi b P) sinh(2 pi P/b), as in equation (1.3) of Lin's Virasoro modular-data preprint. Retain the actual positive integer ranks r(s)=d(s)m(s) and the common finite flat realization above. For arbitrary positive momenta, assume a common real constant C0 and eta>=0 satisfy abs(log(m(s))-log(S(P(s)))-C0)<=eta in every sector. Neither this match nor a CFT realization follows from the density formula.

For 0<x<=y, sinh(y)=sinh(x)cosh(y-x)+cosh(x)sinh(y-x), cosh(x)>=sinh(x), and sinh(y-x)>=0 imply sinh(y)>=exp(y-x)sinh(x). Positivity permits logarithms. Applying the estimate to both factors gives log S(Pmax)-log S(Pmin)>=2 pi Q(Pmax-Pmin). The two matching errors contribute at most 2 eta, so the logarithmic residual-rank span R is at least max(0,2 pi Q DeltaP-2 eta), where DeltaP=Pmax-Pmin.

The ordered exponential-kernel result bounds the actual optimum delta above from below by 1-exp(-R/2). Consequently delta>=1-exp(-max(0,pi Q DeltaP-eta)). This is the optimum over all independent local product channels on the original compact source and target spaces. Competitors may output wrong sectors, mixed states or other flags on basis inputs. Requiring exact basis outputs gives the same optimum; it is unnecessary for this lower bound. A singleton family, duplicate momenta, duplicate ranks and eta=0 are all included.

For any real epsilon with delta<=epsilon<1, positivity of 1-epsilon and monotonicity of logarithm give DeltaP<=(eta-log(1-epsilon))/(pi Q). Here pi Q>0 is derived from b>0. The exact central-charge relation is sqrt(c-1)=sqrt(6)Q. Thus the same upper bound is sqrt(6)(eta-log(1-epsilon))/(pi sqrt(c-1)), which explains the inverse-square-root large-c scale at fixed budgets.

Continuous Virasoro density is not an integer Hilbert-space dimension. The conclusion is conditional on the common finite realization, flat positive integer rank ratios, logarithmic matching and independent local operations. It establishes no conformal-block dominance, quasi-probability positivity, continuous gravity dictionary or original gravitational RT theorem.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SectorChannels/FiniteFlatSectorOptimum.result`
- Dependency: [D5/S3/Quantum/Entanglement/ExponentialSectorKernel](../ExponentialSectorKernel.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorChannelOptimality](../FiniteSectorChannelOptimality.md)
- Dependency: [D5/S3/Quantum/Reduction/CoherentFlagPort](../../Reduction/CoherentFlagPort.md)
