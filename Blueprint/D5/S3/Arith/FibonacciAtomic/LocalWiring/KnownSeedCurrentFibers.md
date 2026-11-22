# Known-alpha current fibres and complete one-step predictions

## Abstract

Starting from the known alpha leaf, the current physical shape leaves precisely one free label bit at each cherry. The exact finite counts and the entire next presence map follow.

**Definition 1.1 (Read a complete next-step presence map).**

$$\operatorname{Next}\left(X, p\right)=1 \iff \operatorname{Present}\left(X, p\right)=1 \lor (p\neq \varepsilon \land \operatorname{BetaLeaf}\left(X, \operatorname{Parent}\left(p\right)\right)=1)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/LocalWiring/KnownSeedCurrentFibers.nextPresence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here epsilon is the empty physical word and Parent removes the final bit. The output is a Boolean for every finite word, not only the words present now. Old words persist and exactly the two children of each current beta leaf are added. At the empty word the parent term is disabled.

Each real next update has this same physical presence map. The orientation chosen by a newly splitting beta changes only the order of its two new leaf labels.

**Theorem 1.2 (The four Fibonacci counts and the complete current fibre).**

$$c=F_{n-1}\quad N_{fiber}=2^{c}\quad N_{shapes}=2^{F_{n}-1}\quad N_{labelled}=2^{F_{n+1}-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LocalWiring/KnownSeedCurrentFibers.exact_known_seed_fibres` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each attained horizon n≥2 and attained physical shape S, c is the number of physical cherry addresses. The labelled fibre is in bijection with all Boolean assignments on those addresses, where each bit says that the left leaf at its cherry is beta. The counts are of actual states of the known alpha seed under exactly n serial local steps.

The shape fixes the heavier child at each rank at least three by the two different Fibonacci leaf counts. At rank two the two physical orientations have the same cherry shape, but different labelled trees. Every assignment is realized jointly in one whole tree.

Write a for the physical left-child bit. At any current cherry address p, the next reply at p followed by aa is exactly that cherry's bit. Thus different labelled states in the same current shape fibre have different entire next maps, while the reconstructed labels determine all present and absent replies. No prediction of a future orientation is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LocalWiring/KnownSeedCurrentFibers.exact_known_seed_fibres`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LocalWiring/KnownSeedCurrentFibers.nextPresence`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LocalWiring/LocalTwoStepRecognizer](LocalTwoStepRecognizer.md)
