# Periodic Masks and an Exact Shifted Successor

## Abstract

Native periodic masks, their exchanges, and a contiguous-deletion obstruction.

Let A and B be distinct letters of an arbitrary alphabet and let T=ABA. The four natural numbers H,J,K,L represent the positive parameters h=H+1,j=J+1,k=K+1,l=L+1. Thus zero exterior powers and every boundary case with a positive parameter equal to one are included.

**Theorem 1.1 (The exact successor degree).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall A \in alpha,\; \forall B \in alpha,\; \forall H \in \operatorname{Nat}\left(\right),\; \forall J \in \operatorname{Nat}\left(\right),\; \forall K \in \operatorname{Nat}\left(\right),\; \forall L \in \operatorname{Nat}\left(\right),\; A \ne B \Rightarrow \operatorname{degree}\left(\operatorname{concat}\left(\operatorname{wordPower}\left(H, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B, A, B, A\right), \operatorname{wordPower}\left(J, \operatorname{List}\left(A, B, A\right)\right)\right), \operatorname{wordPower}\left(K + 1 + L + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{concat}\left(\operatorname{wordPower}\left(K, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B\right), \operatorname{wordPower}\left(H + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A\right), \operatorname{wordPower}\left(L + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(B, A\right), \operatorname{wordPower}\left(J, \operatorname{List}\left(A, B, A\right)\right)\right)\right) = 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesPeriodicRepair.shifted_successor_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered inserted source is T^H ABABA T^J and the base source is T^(K+L+2). The output is T^K AB T^(H+1) A T^(L+1) BA T^J. Its actual mask with blocks V^(3K+2), U^(3H+3), V^(3L+4), U^(3J+2) has two inserted runs.

A nonempty inserted source has degree one exactly when it can be deleted as one contiguous block, leaving the base source. Every cut of a power of ABA lies at a period boundary, after A, or after AB. Remove all entries equal to two from the actual A-gap sequence. Inserting the whole source at those cuts gives [1,1,1], [1,3,1,1,1], or [1,1,1,3,1], with the outer cut cases again giving [1,1,1]. The displayed output instead gives [1,1,3,1,1]. Hence no such deletion is possible. Every valid mask has at least two runs, and the explicit two-run mask attains this lower bound.

This statement computes the native degree of the displayed successor. It does not assert that the preceding output has degree three or classify its minimum masks.

For each choice of A,B,H,J,K,L in the next theorem, use the following word, mask, and cut abbreviations:

$u = \operatorname{concat}\left(\operatorname{wordPower}\left(H, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B, A, B, A\right), \operatorname{wordPower}\left(J, \operatorname{List}\left(A, B, A\right)\right)\right)$

$v = \operatorname{wordPower}\left(K + 1 + L + 1, \operatorname{List}\left(A, B, A\right)\right)$

$w = \operatorname{concat}\left(\operatorname{concat}\left(\operatorname{wordPower}\left(H, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B\right)\right), \operatorname{wordPower}\left(K + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A\right), \operatorname{wordPower}\left(L + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{concat}\left(\operatorname{List}\left(B, A\right), \operatorname{wordPower}\left(J, \operatorname{List}\left(A, B, A\right)\right)\right)\right)$

$M = \operatorname{fiveMask}\left(\operatorname{concat}\left(\operatorname{wordPower}\left(H, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B\right)\right), \operatorname{wordPower}\left(K + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A\right), \operatorname{wordPower}\left(L + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{concat}\left(\operatorname{List}\left(B, A\right), \operatorname{wordPower}\left(J, \operatorname{List}\left(A, B, A\right)\right)\right)\right)$

$N = \operatorname{fiveMask}\left(\operatorname{concat}\left(\operatorname{wordPower}\left(H, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B\right)\right), \operatorname{concat}\left(\operatorname{wordPower}\left(K, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B\right)\right), \operatorname{List}\left(A\right), \operatorname{concat}\left(\operatorname{List}\left(A\right), \operatorname{wordPower}\left(L + 1, \operatorname{List}\left(A, B, A\right)\right)\right), \operatorname{concat}\left(\operatorname{List}\left(B, A\right), \operatorname{wordPower}\left(J, \operatorname{List}\left(A, B, A\right)\right)\right)\right)$

$E = \operatorname{fourCuts}\left(\operatorname{concat}\left(\operatorname{wordPower}\left(H, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B\right)\right), \operatorname{concat}\left(\operatorname{wordPower}\left(K, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B\right)\right), \operatorname{List}\left(A\right), \operatorname{concat}\left(\operatorname{List}\left(A\right), \operatorname{wordPower}\left(L + 1, \operatorname{List}\left(A, B, A\right)\right)\right), \operatorname{concat}\left(\operatorname{List}\left(B, A\right), \operatorname{wordPower}\left(J, \operatorname{List}\left(A, B, A\right)\right)\right), 0\right)$

$Z = \operatorname{concat}\left(\operatorname{wordPower}\left(K, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B\right), \operatorname{wordPower}\left(H + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A\right), \operatorname{wordPower}\left(L + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(B, A\right), \operatorname{wordPower}\left(J, \operatorname{List}\left(A, B, A\right)\right)\right)$

$\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{C}\left(i\right) = \operatorname{fourCuts}\left(\operatorname{concat}\left(\operatorname{wordPower}\left(H, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A, B\right)\right), \operatorname{wordPower}\left(K + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{List}\left(A\right), \operatorname{wordPower}\left(L + 1, \operatorname{List}\left(A, B, A\right)\right), \operatorname{concat}\left(\operatorname{List}\left(B, A\right), \operatorname{wordPower}\left(J, \operatorname{List}\left(A, B, A\right)\right)\right), i\right)$

**Theorem 1.2 (The original and shifted native masks).**

$$\forall alpha \in \operatorname{Type}\left(\right),\; \forall A \in alpha,\; \forall B \in alpha,\; A \ne B \Rightarrow \left(\forall H \in \operatorname{Nat}\left(\right),\; \forall J \in \operatorname{Nat}\left(\right),\; \forall K \in \operatorname{Nat}\left(\right),\; \forall L \in \operatorname{Nat}\left(\right),\; \operatorname{ValidMask}\left(u, v, w, M\right) \land \left(\operatorname{rho}\left(M\right) = 3 \land \left(\left(\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{original}\left(\operatorname{C}\left(i\right)\right) = w \land \left(\operatorname{Admissible}\left(\operatorname{C}\left(i\right), M\right) \land \left(\operatorname{successor}\left(\operatorname{C}\left(i\right)\right) = \operatorname{ite}\left(i < 2, \operatorname{concat}\left(v, u\right), \operatorname{concat}\left(u, v\right)\right) \land \operatorname{degree}\left(u, v, \operatorname{successor}\left(\operatorname{C}\left(i\right)\right)\right) = 1\right)\right)\right) \land \left(\operatorname{ValidMask}\left(u, v, w, N\right) \land \left(\operatorname{rho}\left(N\right) = 3 \land \left(\operatorname{original}\left(E\right) = w \land \left(\operatorname{Admissible}\left(E, N\right) \land \left(\operatorname{successor}\left(E\right) = Z \land \left(\operatorname{degree}\left(u, v, \operatorname{successor}\left(E\right)\right) = 2 \land \left(\operatorname{degree}\left(u, v, w\right) = 3 \Rightarrow \left(\operatorname{IsMinimumMask}\left(u, v, w, M, 3\right) \land \operatorname{IsMinimumMask}\left(u, v, w, N, 3\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesPeriodicRepair.periodic_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put a=T^H AB, c=BA T^J, p=T^(K+1), q=T^(L+1), and x=T^K AB. The definitions fiveMask and fourCuts use actual letter lengths and literal contiguous cuts. Thus M has label blocks U^|a| V^|p| U V^|q| U^|c|, while N has blocks U^|a| V^|x| U V^(1+|q|) U^|c|. Both project to the same ordered sources u=aAc and v=pq in w=apAqc, and both have three U-runs.

The four cuts of M, indexed 0,1,2,3, are respectively (empty,a,p,Aqc), (a,p,A,qc), (ap,A,q,c), (apA,q,c,empty). All exchanged blocks are nonempty and satisfy the native maximal endpoint conditions. Their successor words are vu,vu,uv,uv and have native degree one. The first cut E of N is (empty,a,x,AAqc); it is admissible and its successor is the word Z above. The contiguous-deletion obstruction proves degree two.

If the original degree is three, M and N are both minimum masks; E therefore decreases the degree by exactly one. The theorem retains this hypothesis. It supplies neither a full classification of masks nor a proof that the original degree is three for all parameters. The twelve-mask subfamily, its first mask, arbitrary A-free block coding, and the common primitive-period argument with exterior contexts are outside these statements.

## References

- Truth anchor: `D5/S1/Words/HughesPeriodicRepair.periodic_repair`
- Truth anchor: `D5/S1/Words/HughesPeriodicRepair.shifted_successor_degree`
- Dependency: [D5/S1/Words/HughesUnaryInsertion](HughesUnaryInsertion.md)
