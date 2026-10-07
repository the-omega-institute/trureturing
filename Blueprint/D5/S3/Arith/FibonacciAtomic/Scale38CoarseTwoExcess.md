# Coarse Nested Compensation

## Abstract

A coarse scan distinguishes the nested compensation family with at most two nonleaf requests.

**Theorem 1.1 (Actual scan and exact paid addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale38CoarseTwoExcess.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale38CoarseTwoExcess.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer k at least one, use the existing nested-compensation family: P_0, X_j for 1 <= j <= k, and Y_i for 0 <= i < k. Each source has n=3k+13 leaves. The existing primary query q_t is p_tLR, where p_t=LR^(t-1)L. The secondary query g_t is p_tLLLR. Lean uses zero-based t for both addresses.

The finite protocol requests q_1 through q_(k+1) in order while replies are alpha. The coarse quotient keeps alpha and beta and merges branch and absent into none. The first none at the initial slot selects X_1; at the last slot it selects Y_(k-1). At an interior slot t the surviving exceptional sources are exactly X_t and Y_(t-2). One actual g_t request separates them: it is an alpha leaf of X_t and is absent in Y_(t-2). All alpha replies select P_0. Every other response abandons selection. A selection starts complete labelled-leaf verification; an abandoned route or failed verification starts the existing complete acquisition procedure with its own logical history.

There is one deterministic strategy, initialized independently of the source, whose policy depends only on the coarse history. It terminates and decides third-substitution-image membership on every finite source. The exact address cache starts empty, contains only truthful reports actually requested in the same execution, and has no duplicate addresses.

Write L(U) for the source's leaves and J(U) for its distinct paid addresses. The executed route followed by complete verification gives J(P_0)=L(P_0), J(X_j)=L(X_j) union {q_j}, J(Y_i)=L(Y_i) union {q_(i+2),g_(i+2)} for i <= k-2, and J(Y_(k-1))=L(Y_(k-1)) union {q_(k+1)}. Every displayed extra address is an actual request and is not a leaf; the two extras are distinct. Consequently the costs are n, n+1, n+2 and n+1, respectively. For k at least three all family costs are bounded by n+2 and some family member attains n+2. At k=1 the interior secondary-query range is empty.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale38CoarseTwoExcess.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation](Scale38NestedCompensation.md)
