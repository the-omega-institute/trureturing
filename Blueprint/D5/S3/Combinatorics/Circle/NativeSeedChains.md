# Native positive-SMALL chain extraction

## Abstract

Every negative physical label in an actual positive-SMALL centered source starts a dyadic chain with exact seed transport.

**Theorem 1.1 (A dyadic chain from each negative occurrence).**

Lean statement: `D5/S3/Combinatorics/Circle/NativeSeedChains.native_chain_extraction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/NativeSeedChains.native_chain_extraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k>=3, t be any natural number, N=2^k-1, Q=2^(k-2), and w=SourceWidth.actualSource(k,t) on physical labels Fin(k). Assume every label with |w(i)|<Q has w(i)>0. For any negative label n, take its physical successor as the seed label and write a for that seed's value. A finite literal forward path of SMALL labels starts at that seed label and ends immediately before a positive LARGE root p. Its values are a,2a,...,p/2; the path may be empty. The chain, including its root and following negative label, has no repeated physical label and has length at most k. The following physical labels have values -B=2p-N and b=4p-N. The root satisfies Q<=p and 3p<=N; both seeds a and b are positive and congruent to 1 modulo 4.

Writing s for the SMALL mass and d=B-p, the chain has s=p-a, d>=0 and s-d=b-a. The construction selects positions along the full physical k-cycle, without a unit assumption, injectivity of values, a minimal numerical period, a phase restriction or a bound on the number of SMALL labels. Strict positivity of all SMALL labels itself excludes zero values. A positive maximum of the finite source proves 3w(i)<=N for every positive value: a maximum must be LARGE, and its second successor has value 4w(i)-N and cannot exceed that maximum. A positive SMALL step doubles; a well-founded deficit Q-w(i) therefore reaches a LARGE root.

The chain identity is the source-derived transport equation used by deferred-prefix queues. This statement extracts each chain; it does not yet assert that the extracted chains partition all physical labels, nor construct a complete queue word. A complete permutation with bound C+floor((A-mu)/2), where C=(N-1)/2 and mu,A are native seed extrema, requires those further global steps. The exact-C positive-SMALL conclusion and full Circle Conjecture 3.1 remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/NativeSeedChains.native_chain_extraction`
- Dependency: [D5/S3/Combinatorics/Circle/ExpandingSourcePath](ExpandingSourcePath.md)
