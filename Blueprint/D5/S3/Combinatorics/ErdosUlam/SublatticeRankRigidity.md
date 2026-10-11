# Rank rigidity from a sharp chain bound

## Abstract

A colouring attaining the trivial monochromatic chain bound in an odd Boolean lattice is constant on each rank, and its ranks split equally between the two colours.

**Theorem 1.1 (Equal-rank sets have equal colours).**

$$\forall n \in \mathrm{Nat},\; \operatorname{Odd}\left(n\right) \Rightarrow \left(\forall chi \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Bool},\; \left(\forall L \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{IsSublattice}\left(L\right) \Rightarrow \left(\operatorname{Monochromatic}\left(chi, L\right) \Rightarrow \operatorname{card}\left(L\right) \le \left\lfloor\frac{n + 1}{2}\right\rfloor\right)\right) \Rightarrow \left(\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall B \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{card}\left(A\right) = \operatorname{card}\left(B\right) \Rightarrow \operatorname{chi}\left(A\right) = \operatorname{chi}\left(B\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/SublatticeRankRigidity.rank_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every maximal chain has n plus one members. Its two colour classes are sublattices whenever nonempty, so the assumed upper bound forces each colour to occur exactly (n plus one) divided by two times. For a set C and distinct points x and y outside C, enumerate C first, then x and y, then the remaining points. Reversing x and y produces two maximal chains which differ only at rank |C| plus one. Balance forces C union {x} and C union {y} to have the same colour. For equal-size A and B, choose x in A outside B and y in B outside A and exchange them. The number of points of A outside B decreases by one. Induction connects A to B.

**Theorem 1.2 (The prefix ranks split equally).**

$$\forall n \in \mathrm{Nat},\; \operatorname{Odd}\left(n\right) \Rightarrow \left(\forall chi \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Bool},\; \left(\forall L \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{IsSublattice}\left(L\right) \Rightarrow \left(\operatorname{Monochromatic}\left(chi, L\right) \Rightarrow \operatorname{card}\left(L\right) \le \left\lfloor\frac{n + 1}{2}\right\rfloor\right)\right) \Rightarrow \left(\forall c \in \mathrm{Bool},\; \operatorname{card}\left(\operatorname{filter}\left(\operatorname{range}\left(n + 1\right), \lambda(r: \mathrm{Nat}) \operatorname{chi}\left(\operatorname{initialSegment}\left(n, r\right)\right) = c\right)\right) = \left\lfloor\frac{n + 1}{2}\right\rfloor\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/SublatticeRankRigidity.balanced_prefixes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard prefix chain consists of the subsets with elements less than r, for r from zero through n. Distinct ranks give distinct sets. The assumed upper bound applies to either colour class of this chain. Their cardinalities sum to the even number n plus one, and neither exceeds half that number, so both equal half.

## References

- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeRankRigidity.balanced_prefixes`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/SublatticeRankRigidity.rank_rigidity`
- Dependency: [D5/S3/Combinatorics/ErdosUlam/SublatticeDefs](SublatticeDefs.md)
