# Finite endpoint replay on one rational source

## Abstract

An exact original output forces an actual grid read on each accumulation endpoint.

The source is a positive rational. False denotes L(z)=z/(1+z), true denotes R(z)=z+1, and the head of a word acts first. At chronological prefix w the only read is the complete integer floor of 2^s times the attained response. The original prior is the union, for c=1/6 and c=2/3, of c and all c-1/n for integers n at least 12. Both endpoints are included.

A controller has a common initial local state and a deterministic source-independent instruction function. Instructions halt with a whole output, perform a local step, execute one forward letter on the same source, or request one dyadic floor report and continue from that integer. A Run is a finite derivation of these instructions; it retains the current chronological prefix at every actual read. The state type and instruction function are arbitrary, so the lower bound applies to a class containing every ordinary deterministic finite program. This extensional enlargement is used only for an impossibility result; it does not extract an executable program from an arbitrary function.

**Theorem 1.1 (Every successful endpoint branch reads a grid).**

$$\forall C,V,i, \operatorname{Correct}(C,V)\land \operatorname{InjOn}(V,P)\land \operatorname{Run}(C,c_{i},o,v,A)\longrightarrow \exists (w,s)\in A, 2^{s}f_{w}(c_{i})\in \mathbb{Z}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/RationalRouting/Source.endpoint_run_requires_grid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quantifiers range over every state type, output type, deterministic instruction function, common initial state, target injective on the entire prior, either endpoint, and every finite run ending there. Correctness requires both finite termination on every prior member and equality of every terminal output with its original target. The conclusion supplies a read that actually occurred on the endpoint branch, at its actual attained prefix and requested exponent, where the scaled response is an integer. Merely reaching a dyadic response without reading it is insufficient.

Each forward letter preserves positivity, order and the upper bound that a response difference is at most the original difference. Away from a dyadic grid, a floor report is constant on a sufficiently small left neighborhood. Induction on the complete finite run takes minima of these neighborhoods and replays local computation, action choices, requested scales, reports and the final output. A sufficiently late member c-1/n belongs to that neighborhood and is a different original. Its identical terminal output contradicts the target's injectivity. The argument uses no uniform bound on scale, work, read count or any resource on other runs.

The result concerns acquisition of an injective original output on this same rational prior. The attained-prefix classification, exact action minima, explicit acquiring programs and finite transports to the chronological word, named incidence path and indexed prefix table require additional statements.

## References

- Truth anchor: `D5/S3/Observer/RationalRouting/Source.endpoint_run_requires_grid`
- Dependency: [D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced](../../PrimeForms/SternBrocot/WordNodesAreReduced.md)
