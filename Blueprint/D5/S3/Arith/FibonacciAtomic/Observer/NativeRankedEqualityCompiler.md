# Exact scalar formulas for native tree equality

## Abstract

NativeRankedEqualityCompiler

**Theorem 1.1 (Native equality is a finite conjunction of offset equalities).**

$$\forall k, m: Nat, (\forall z: \operatorname{Fin}\left(m\right) \to Source, (\forall E, F: \operatorname{RankedExpr}\left(k, m\right), ((\operatorname{IsQF}\left(\operatorname{equalityFormula}\left(z, E, F\right)\right)) \land (\forall n: \operatorname{Fin}\left(k\right) \to Nat, ((\operatorname{Realize}\left(\operatorname{equalityFormula}\left(z, E, F\right), n\right)) \iff (\operatorname{rankedEval}\left(n, z, E\right) = \operatorname{rankedEval}\left(n, z, F\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedEqualityCompiler.ranked_equality_compilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native source is the ordered free binary magma on alpha and beta. Substitution sends alpha to beta and beta to the pair of beta and alpha. Its r-th iterate at alpha is the rank-r atom. A RankedExpr has finite native grounds, fixed powers of residual or scalar names, and ordered pairs. Each original scalar name denotes one shared natural rank, and each residual name denotes one shared finite native tree.

Fix a finite residual tuple z before choosing the scalar tuple n. An offset is either a constant c or n(j)+c. Normalize each finite ground into constant-rank leaves 0 and 1; normalize a decorated scalar into its original variable plus the decoration. A decorated residual becomes the expanded finite tree obtained by applying its fixed substitution power to z(i). Explicit pairs remain ordered pairs. The interpretation of this finite rank term is exactly rankedEval at the same n and z.

For a rank term T, its symbolic right clock K is its leaf offset when T is a leaf, and K(B)+2 when T is the pair of A and B. Its atomicity conditions C are empty at a leaf. At a pair they are C(A), C(B), and K(A)=K(B)+1. Structural induction proves that T evaluates to the rank-r atom exactly when every condition in C(T) holds and K(T)=r. Ranks zero and one are separated from pairs by the native constructors. At every higher rank the native Fibonacci recurrence identifies the two children.

Compare two leaves by equating their offsets. Compare a leaf with a pair by imposing the pair's atomicity conditions and equating its clock with the leaf offset. Compare two pairs by conjoining the comparisons of corresponding children. Thus a rank leaf may equal a compound native tree; treating them as disjoint syntax would give an incorrect compiler. The resulting finite equation list is interpreted by one common scalar tuple throughout.

conditionsFormula translates constant and variable offsets into the natural-number Presburger language with zero, one and addition, then conjoins the equality atoms. equalityFormula is quantifier free and uses only the original scalar names as free variables; unused names need not occur. Its realization is equivalent to native equality for every scalar tuple, including ranks zero and one, repeated variables, zero dimensions and closed ground expressions. No upper rank bound or rank enumeration is used. The theorem concerns finite syntax translation; it does not assert a bound on expanded ground size or the cost of unary numeral syntax.

**Theorem 1.2 (One formula describes the entire feasible-rank support).**

$$\forall k, m: Nat, (\forall pairs: \operatorname{List}\left(\operatorname{Prod}\left(\operatorname{RankedExpr}\left(k, m\right), \operatorname{RankedExpr}\left(k, m\right)\right)\right), ((\operatorname{IsQF}\left(\operatorname{supportFormula}\left(pairs\right)\right)) \land (\forall n: \operatorname{Fin}\left(k\right) \to Nat, ((\operatorname{Realize}\left(\operatorname{supportFormula}\left(pairs\right), n\right)) \iff (\exists z: \operatorname{Fin}\left(m\right) \to Source, (\operatorname{Negatives}\left(pairs, n, z\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedEqualityCompiler.support_compilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negatives(pairs,n,z) abbreviates the conjunction of all listed disequalities at the common n and z. For a finite list of pairs of ranked expressions, use the existing uniformSeparator for that entire list. Negate each equality formula after substituting this one residual tuple, then conjoin all negatives. The resulting supportFormula is quantifier free. It holds at n exactly when there is one finite residual tuple satisfying every listed disequality at that same n.

The uniform residual reflection theorem makes this a joint statement. If one tuple satisfies every negative, no listed equality is universal in the residuals, and every negative therefore holds at the common separator. Conversely the separator itself is a finite satisfying tuple. There is no separate choice of residual tuple or scalar ranks for individual conjuncts. The empty list gives true support, and either dimension may be zero.

A Presburger policy supplied with its own formula and semantic correspondence can be conjoined with this support formula. An arbitrary Prop-valued policy does not automatically have such a representation or an executable decision procedure. Fixed finite coordinates must be substituted before computing the separator for the remaining expressions. Unknown finiteness of completion trees, serialized observation decoding, and general quantified arithmetic decisions are separate questions. The formula translation uses the native Fibonacci recurrence and the existing uniform residual theorem; it makes no claim of literature originality.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedEqualityCompiler.ranked_equality_compilation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedEqualityCompiler.support_compilation`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization](NativeUniformResidualRealization.md)
