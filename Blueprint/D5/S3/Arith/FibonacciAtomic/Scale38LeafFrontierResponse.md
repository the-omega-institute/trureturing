# Complete Frontiers and Leaf Responses

## Abstract

The complete labelled leaf geometry of nested compensation trees determines every response at a target leaf.

**Theorem 1.1 (Disjoint frontiers and the thirteen response rows).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Scale38LeafFrontierResponse.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Scale38LeafFrontierResponse.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Addresses are finite words in L and R; labels are alpha and beta. The labelled frontier consists of exactly the addresses at which actual readout reports a leaf, paired with its label. Prefixing a block preserves its labels. Write A=((beta,alpha),beta), E=(beta,alpha), C=(A,E), and B=(C,A). Thus A has labelled leaves LL:beta, LR:alpha, R:beta; E has L:beta and R:alpha.

For every nonnegative r, H_r is the right comb of r A slots ending in C. Its frontier is the disjoint union of R^(t-1)L A for 1 <= t <= r+1 and R^(r+1) E. The frontier of B is LL A, LR E, and R A. For every k >= 1 and 1 <= j <= k, G_(k,j) has k left slots, with B at slot j and A elsewhere, and ends in C. Its frontier is the disjoint union of those prefixed slot frontiers and R^k C.

The members are P_0=(H_k,B), X_j=(G_(k,j),A), and Y_i=(H_i,(H_(k-i),A)) for 0 <= i < k. Their complete disjoint frontiers are respectively L H_k with R B; L G_(k,j) with R A; and L H_i with RL H_(k-i) and RR A. Every target leaf belongs to one of the following thirteen row types. Each row applies to every address in its whole block and every other family member. Any competitor omitted from a row matches the target's actual leaf label. An empty index range contributes no competitor.

P_0 left slot t (1 <= t <= k): X_t reports branch; Y_i with i <= t-2 report absent.

P_0 left terminal C: all Y_i report absent.

P_0 right B blocks LL A and R A: all X_j report absent.

P_0 right B block LR E: all Y_i report branch and all X_j report absent.

X_j left ordinary slot t != j: X_t reports branch; Y_i with i <= t-2 report absent.

X_j left exceptional B slot: every competitor reports absent.

X_j left terminal C: all Y_i report absent.

X_j right A: P_0 and all Y_i report branch.

Y_i left slot t (1 <= t <= i+1): X_t reports branch; Y_j with j <= t-2 report absent.

Y_i left terminal E: P_0, all X_j, and Y_j with j > i report branch; Y_j with j < i report absent.

Y_i right H_(k-i) slot h (1 <= h <= k-i+1): all X_j report absent, P_0 reports absent when h >= 2, and Y_j report absent when j >= k-h+2. No competitor reports branch.

Y_i right H_(k-i) terminal E: Y_j with j < i report branch; P_0, all X_j, and Y_j with j > i report absent.

Y_i right RR A: all X_j report absent.

The comparison of two combs accounts for these rows. A leaf in the t-th three-leaf group of H_r matches in H_s exactly when t <= s+1, and is absent otherwise. A terminal two-leaf address of H_r matches when s=r, reports branch when s>r, and is absent when s<r. Every leaf of A is a branch address in B, and every leaf of B is absent in A. The complete frontier decomposition extends these comparisons to all target leaves.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Scale38LeafFrontierResponse.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Scale38NestedCompensation](Scale38NestedCompensation.md)
