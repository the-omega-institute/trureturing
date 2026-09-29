# Actual Maximal-Block Descent

## Abstract

Every actual maximal block descends through literal BKS edges to one of finitely many bounded root forms.

This owner turns the one-step BKS predecessor/successor mechanism into a finite descent for actual intervals. One support-stabilizing power q is chosen once and returned with all of its fixed-word data. Every edge has a strictly smaller right endpoint, so the chain terminates without an assumed infinite extension.

**Theorem 1.1 (One power supports inverse and forward evolution).**

$$\operatorname{UniformFixed}\left(P, mu, w\right) \land 1 < P \Rightarrow \operatorname{existsPowerEvolution}\left(P, mu, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/MaximalBlockDescent.exists_uniform_power_bks11_bks12_evolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

For a finite alphabet, P>1, a P-uniform morphism, and its pointwise fixed word, choose q>0 and Q=P^q. The powered morphism g is Q-uniform, fixes the same word by Q-cells, and has stable two-step support. Whenever an actual block satisfies the three displayed late, long, and quotient-span bounds, the theorem constructs a unique nearby actual predecessor, proves its right endpoint is smaller, and identifies the original interval as the unique successor crossing the central image.

**Definition 1.2 (The literal word on a finite interval).**

$$\operatorname{intervalWord}\left(w, (i, j)\right) = \operatorname{ofFn}\left(t \mapsto \operatorname{w}\left(i + t\right), j + 1 - i\right)$$

*Formalization.* `D5/S1/Recurrence/Raney/MaximalBlockDescent.intervalWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

For endpoints (i,j), the list has natural length j+1-i and entry t equal to w(i+t). Natural subtraction totalizes reversed endpoints; every downstream use supplies an ordered actual maximal interval.

**Definition 1.3 (One actual inverse/image edge).**

$$\operatorname{IsBksDescentStep}\left(Q, Delta, w, parent, child\right) \iff (\operatorname{ActualMaximal}\left(Delta, w, parent\right) \land \operatorname{ActualMaximal}\left(Delta, w, child\right) \land \operatorname{quotientEndpointBounds}\left(Q, parent, child\right) \land \operatorname{snd}\left(child\right) < \operatorname{snd}\left(parent\right) \land \operatorname{centralImageInside}\left(Q, Delta, w, parent, child\right) \land \operatorname{leftContextLength}\left(Q, w, parent, child\right) \leq 2 \cdot Q^{2} \land \operatorname{rightContextLength}\left(Q, w, parent, child\right) \leq 2 \cdot Q^{2})$$

*Formalization.* `D5/S1/Recurrence/Raney/MaximalBlockDescent.IsBksDescentStep` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

A descent edge from parent to child requires both endpoints to be actual maximal Delta intervals. The child lies within Q of the quotient endpoints, remains late and longer than Q^2, and has a strictly smaller right endpoint. The central Q-image lies inside the parent. The left and right literal context words between the parent boundary and that central image each have length at most 2Q^2.

**Definition 1.4 (The exact stopping disjunction).**

$$\operatorname{IsBksRoot}\left(Q, (i, j)\right) \iff (\operatorname{div}\left(i, Q\right) < 2 \cdot Q \lor j + 1 - i \leq 2 \cdot Q^{2} \lor \operatorname{div}\left(j, Q\right) + 1 - \operatorname{div}\left(i, Q\right) \leq Q^{2} + 2 \cdot Q)$$

*Formalization.* `D5/S1/Recurrence/Raney/MaximalBlockDescent.IsBksRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

An interval is a root precisely when at least one hypothesis for the next conservative descent fails: its left quotient is below 2Q, its length is at most 2Q^2, or its quotient span is at most Q^2+2Q. These alternatives preserve short, early, and narrow cases rather than discarding them.

**Definition 1.5 (Finite chains of actual descent edges).**

$$\begin{aligned}\operatorname{ActualMaximal}\left(e\right) \land \operatorname{IsBksRoot}\left(Q, e\right) \Rightarrow \operatorname{IsBksDescentChain}\left(Q, e, e\right)\\\operatorname{IsBksDescentStep}\left(Q, p, c\right) \land \operatorname{IsBksDescentChain}\left(Q, c, r\right) \Rightarrow \operatorname{IsBksDescentChain}\left(Q, p, r\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Raney/MaximalBlockDescent.IsBksDescentChain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

The root constructor gives a zero-edge chain at an actual maximal root. The step constructor prepends one IsBksDescentStep to an existing finite tail. Thus every member of a chain is an actual interval, and no coinductive or occurrence-converse assumption enters.

**Definition 1.6 (Early roots retain actual endpoints).**

$$\operatorname{earlyBksRoots}\left(Q, Delta, w\right) = \operatorname{setOf}\left(e, \operatorname{ActualMaximal}\left(Delta, w, e\right) \land \operatorname{fst}\left(e\right) < 2 \cdot Q^{2}\right)$$

*Formalization.* `D5/S1/Recurrence/Raney/MaximalBlockDescent.earlyBksRoots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

This set contains exactly the actual maximal intervals whose first endpoint is below 2Q^2. Maximality makes an interval unique at a fixed first endpoint, which is later used to prove the set finite.

**Definition 1.7 (Bounded literal words of late roots).**

$$\operatorname{lateBksRootWords}\left(Q, Delta, w\right) = \operatorname{setOfRootWords}\left(e, \operatorname{intervalWord}\left(w, e\right), \operatorname{ActualMaximal}\left(Delta, w, e\right), \operatorname{IsBksRoot}\left(Q, e\right), 2 \cdot Q^{2} \leq \operatorname{fst}\left(e\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Raney/MaximalBlockDescent.lateBksRootWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

A list belongs when it is the literal intervalWord of an actual BKS root whose first endpoint is at least 2Q^2. Root failure then bounds the list length by Q(Q^2+2Q), so finite alphabet and bounded length give a finite set without imposing a false endpoint bound.

**Definition 1.8 (Literal left and right edge contexts).**

$$\operatorname{bksContextPairs}\left(Q, Delta, w\right) = \operatorname{setOfLiteralEdgeContexts}\left(Q, Delta, w\right)$$

*Formalization.* `D5/S1/Recurrence/Raney/MaximalBlockDescent.bksContextPairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

For every actual descent edge, the pair records the parent subword before the central image and the parent subword after it. The edge definition bounds both lengths by 2Q^2; pairing them retains the joint correction that later controls one actual realization.

**Theorem 1.9 (Every actual block reaches finite root data).**

$$\operatorname{UniformFixed}\left(P, mu, w\right) \land 1 < P \Rightarrow \operatorname{existsFiniteRootDescentData}\left(P, mu, w, \operatorname{earlyBksRoots}\left(Q, Delta, w\right), \operatorname{lateBksRootWords}\left(Q, Delta, w\right), \operatorname{bksContextPairs}\left(Q, Delta, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/MaximalBlockDescent.exists_bounded_root_descent_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

The theorem returns one q>0, Q=P^q, the powered uniform/fixed/support facts, finiteness of early roots, late root words, and context pairs, and a chain for every actual maximal interval. The chain is built by well-founded induction on the right endpoint using strict descent. At its terminal root, either the start is below 2Q^2 or the literal length is at most Q(Q^2+2Q). This is the finite-root input consumed by boundary transport and final assembly.

## References

- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockDescent.IsBksDescentChain`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockDescent.IsBksDescentStep`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockDescent.IsBksRoot`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockDescent.bksContextPairs`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockDescent.earlyBksRoots`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockDescent.exists_bounded_root_descent_chain`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockDescent.exists_uniform_power_bks11_bks12_evolution`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockDescent.intervalWord`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockDescent.lateBksRootWords`
- Dependency: [D5/S1/Recurrence/Raney/MaximalBlockEvolution](MaximalBlockEvolution.md)
