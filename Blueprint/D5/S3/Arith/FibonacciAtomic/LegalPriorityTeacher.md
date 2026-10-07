# Priority Teachers on the Legal Five-Window Language

## Abstract

Two ordered effective edges completely classify priority teachers on legal Fibonacci histories.

Fix a natural n. Input(n) is Fin(n) to Window, where Window consists of 000,100,010,101,001 written from low to high. Positions start at zero. The unit bit is zero, terminal zero windows are allowed, and there is no End query. Legal(x) is the existing flattened-bit Fibonacci legality predicate with false initial bit. In particular high(x(i)) and low(x(i+1)) cannot both be true. Null windows retain their positions.

**Theorem 1.1 (Legality at adjacent window boundaries).**

$$\forall \left(n: \mathbb{N}\right), \forall \left(x: \operatorname{Input}\left(n\right)\right), \operatorname{Legal}\left(x\right) \iff \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right)\right) \implies \neg \left(\operatorname{last}\left(\operatorname{apply}\left(x, i\right)\right) = true \land \operatorname{first}\left(\operatorname{apply}\left(x, j\right)\right) = true\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LegalPriorityTeacher.legal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the five windows has legal internal bits. With initial bit false, flattened legality therefore holds exactly when no window ends in one immediately before a window beginning in one.

Roles(n) consists of p,q,r in Fin(n) with p<q<r. The actual teacher first tests high(x(p)) and low(x(q)), returning 1 when both hold. Otherwise it tests high(x(q)) and low(x(r)), returning 2 when both hold, and 0 otherwise. The priority of the first test is part of the function.

edge(i,j) is Some(i,j) when i+1<j and None otherwise. signature(t) is the ordered pair (edge(p,q),edge(q,r)); the two absent entries remain distinct positions in that pair. Adjacency forces a gate to vanish on every legal history. An active edge is tested by putting 001 at its first position and 100 at its second position, with 000 everywhere else. This is a legal actual input. It activates precisely that position pair.

**Theorem 1.2 (Complete equivalence of the actual legal-domain functions).**

$$\forall \left(n: \mathbb{N}\right), \forall \left(t: \operatorname{Roles}\left(n\right)\right), \forall \left(u: \operatorname{Roles}\left(n\right)\right), \left(\forall \left(x: \operatorname{Input}\left(n\right)\right), \operatorname{Legal}\left(x\right) \implies \operatorname{teacher}\left(t, x\right) = \operatorname{teacher}\left(u, x\right)\right) \iff \operatorname{signature}\left(t\right) = \operatorname{signature}\left(u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LegalPriorityTeacher.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence holds for all n and all strict role triples. A first-edge probe returns 1, whereas a second-edge probe returns 2. The priority rule therefore prevents the other teacher's first edge from impersonating a second edge. A triple with both gaps at least two is determined by its legal-domain function. Triples with two adjacent gates all give zero. No sampling law, probability bound, or label-noise assumption is used.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LegalPriorityTeacher.legal_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LegalPriorityTeacher.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd](LiteralWindowEnd.md)
