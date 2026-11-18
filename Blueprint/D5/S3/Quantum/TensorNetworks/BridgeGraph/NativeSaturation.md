# Native saturation at the three-halves threshold

## Abstract

A coordinate routing realizes the complete rectangular width-three native saturation family.

For every natural a and b and every positive natural q, suitable width-three families of complex a-by-b and (3q)-by-(2q) factors exist whose tensor sum has identity column Gram if and only if 2b is at most 3a. The family includes a=0 or b=0.

**Theorem 1.1 (Rectangular native saturation iff).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall q \in Nat,\; (0 < q) \Rightarrow ((\exists M \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; \exists N \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3 \cdot q\right), \operatorname{Fin}\left(2 \cdot q\right), Complex\right),\; \operatorname{conjTranspose}\left(\sum_{r:\operatorname{Fin}\left(3\right)} \operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right)\right) \cdot \sum_{r:\operatorname{Fin}\left(3\right)} \operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right) = (1: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(2 \cdot q\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(2 \cdot q\right)\right), Complex\right))) \Leftrightarrow (2 \cdot b \le 3 \cdot a))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeSaturation.native_saturation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a and b and every positive natural q, there exist three complex matrices M(r) of size a by b and three matrices N(r) of size 3q by 2q whose tensor sum has FᴴF equal to the identity on Fin b × Fin (2q), if and only if 2b ≤ 3a. No premise a<b is present or needed, and zero dimensions remain part of the statement.

Use zero-based coordinates and write [P] for 1 when P holds and 0 otherwise. The explicit left slices are M(0)(i,j)=[i=j], M(1)(i,j)=[a≤j and i=2(j-a)], and M(2)(i,j)=[a≤j and i=2(j-a)+1]. The right slices are N(0)(l,k)=[l=k], N(1)(l,k)=[k<q and l=2q+k], and N(2)(l,k)=[q≤k and l=q+k]. The differences j-a are natural subtraction and are used under a≤j.

When 2b≤3a, these slices route each input (j,k) to (j,k) if j<a, to (2(j-a),2q+k) if a≤j and k<q, and to (2(j-a)+1,q+k) otherwise. The threshold puts both residual first coordinates below a. The first branch has second coordinate below 2q and the other branches have it at least 2q. The two residual branches have even and odd first coordinates. Within each branch the output recovers j and k, proving injectivity. Entrywise expansion identifies the tensor sum with its coordinate matrix, so SequentialRegisterCircuit.coordinate_gram gives the identity column Gram.

For necessity, an identity column Gram has full column rank. The native matrix has 3aq rows and 2bq columns. Thus 2bq=rank(FᴴF)≤rank(F)≤3aq, and positivity of q gives 2b≤3a. If b=0 the column space is empty and the Gram equation is vacuous; if a=0, the threshold forces b=0.

This whole-parameter construction is a consequence of the native model with fixed right dimensions c=2q and d=3q. This saturation construction alone does not prove the separate universal implication that the scalar-Gram hypotheses and a<b force 3c≤2d for arbitrary c,d.

At a=2, b=3 and q=1 this recovers the permutation-coordinate example ex-bridge-two-three in the earlier book prose, Chapter 19 of trureturing-books/quantum-geometry, lines 106–140 at https://github.com/the-omega-institute/trureturing-books/blob/1f0a6b69198be9aee48c5902e1c60966cddece4d/books/quantum-geometry/zh/ch19-tensor-networks-and-holography.md#L106-L140. The supplier is a book prose example, not a frozen D5 theorem. Here (0,0),(0,1),(1,0),(1,1),(2,0),(2,1) route to (0,0),(0,1),(1,0),(1,1),(0,2),(1,2), respectively. This bijection gives the same six-coordinate permutation and is a reused instance.

A literature search found arXiv:1612.07616v1, whose introduction, Theorem 1.3, Definition 3.1 and Lemma 3.2 concern square local factors; they do not state this rectangular iff. This document makes no external novelty claim.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeSaturation.native_saturation_iff`
- Dependency: [D5/S3/Quantum/Entanglement/SequentialRegisterCircuit](../../Entanglement/SequentialRegisterCircuit.md)
