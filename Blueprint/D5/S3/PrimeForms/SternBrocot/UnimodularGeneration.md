# Natural unimodular matrix generation

## Abstract

All natural determinant-one matrices are finite left-right words.

PositiveMatrix is the existing carrier of four natural entries a,b,c,d arranged as [[a,b],[c,d]]; zero entries are allowed. Unimodular(A) means a d=b c+1. The existing factors L=[[1,0],[1,1]] and U=[[1,1],[0,1]] act by left multiplication. For a Boolean word w, wordMatrix([])=I, wordMatrix(false::w)=L wordMatrix(w), and wordMatrix(true::w)=U wordMatrix(w). Thus this list records matrix factors with its head on the left; it is distinct from chronological action order.

**Theorem 1.1 (Exact generation of determinant-one natural matrices).**

$$\forall A\in \operatorname{PositiveMatrix}, \operatorname{Unimodular}(A)\iff \exists w\in \{0,1\}^{*}, \operatorname{wordMatrix}(w)= A$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.unimodular_iff_wordMatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Axiom Math; Kenny Lau (2026). *HJO unimodular-pair descent*. URL: <https://github.com/AxiomMath/HJO/blob/6a58dfa6ab98bd35d841cb2cf8fd9081f62fad03/HJO/Shuffle/SlopeActions.lean>.

*Commentary.*

The quantifier ranges over every natural matrix, with no bound on entries or length and no strict positivity assumption. A word always has determinant one by the existing multiplication theorem.

For the converse, orient the two rows as p=(c,d) and p'=(a,b). The unimodular-pair equation is p'₁p₂=p₁p'₂+1. Except at p=(0,1), p'=(1,0), the pair has an additive unimodular parent. If p=q+p', reversing the subtraction is multiplication by L; if p'=p+q, it is multiplication by U. The subtracted row is nonzero, so the sum a+b+c+d strictly decreases. Strong induction constructs the entire finite word, terminating at I. The additive-parent arithmetic is Kenny Lau's HJO descent; the finite matrix-word construction and its connection to the existing wordMatrix use that descent.

Replacing L by chronological J,M and U by chronological M,J connects this determinant-one description to native forward histories. A row exchange accounts for determinant minus one. The cumulative continuation and prefix normal-form conclusions require their own additional arguments.

## References

- Truth anchor: `D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.unimodular_iff_wordMatrix`
- Dependency: [D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced](WordNodesAreReduced.md)
