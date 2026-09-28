# Finite Cutoff and First-Read Recursion

## Abstract

Exact identification before a finite deadline is characterized by the first read and the continuation on each actual response fiber.

Fix natural numbers p>=2 and P>=1, an initial block b in Fin(p), and a nonempty finite set A of original residues r with 0<=r<P. At elapsed time t the physical symbol is R(t,r)=((bP+r+t) mod (pP)) div P. Put Y(A,t)={R(t,r):r in A} and fiber(A,t,y)=A_y(t)={r in A:R(t,r)=y}. These fibers retain the same original residue throughout execution.

A protocol either stops with an original-residue label or waits a natural number of forward unit events, reads once, and selects its continuation from the observed symbol. The known initial block and clock determine the uncarried label (b+t div P) mod p. A read is encoded as zero when it equals this label and as one otherwise. Indeed its symbol is (b+t div P+c) mod p, where c is the decoded binary sensor, equal to zero for r<P-(t mod P) and one otherwise. Since p>=2, these two labels are distinct. Encoding and decoding therefore preserve every actual branch, query count, output, and completion time.

For arbitrary natural n, D, q with n<=D, F(q,A,n,D) means that some protocol with at most q further reads, begun at time n, outputs r and finishes by D for every r in A. The protocol is one common decision tree; its waits and continuations have no direct access to the unknown residue. Leaves can occur before the query budget is exhausted. Zero waiting and immediate rereading are allowed, since the current read need not have been acquired.

**Theorem 1.1 (Exact decomposition at every query budget).**

$$(\operatorname{F}\left(0, A, n, D\right) \iff \operatorname{card}\left(A\right) = 1) \land (\operatorname{F}\left(q+1, A, n, D\right) \iff \operatorname{card}\left(A\right) = 1 \lor (\exists t \in \mathbb{N}, n \leq t \land t \leq D \land (\forall y \in \operatorname{Y}\left(A, t\right), \operatorname{F}\left(q, \operatorname{fiber}\left(A, t, y\right), t, D\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/FiniteCutoffProtocolRecursion.finite_cutoff_branch_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A stopped controller returns the same label on all candidates, so zero-query success is equivalent to a singleton. For a successful query node, its first read time t is common to all candidates. Forward execution makes t no later than any completion time, hence t<=D. All candidates with the same physical response select the same continuation, which has one fewer available read.

Conversely, choose a successful continuation for every actual response fiber, wait t-n events, and attach these continuations to the corresponding observed bits. Unreachable branches may stop arbitrarily. Every original candidate follows its own fiber, is identified correctly, and meets the same deadline. The argument includes t=n, singleton fibers, and all nonempty finite candidate sets, without requiring an interval or a power-of-p block length.

## References

- Truth anchor: `D5/S3/Observer/Budget/FiniteCutoffProtocolRecursion.finite_cutoff_branch_recursion`
- Dependency: [D5/S3/Observer/Budget/DyadicForwardWaitingOptimality](DyadicForwardWaitingOptimality.md)
