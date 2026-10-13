# Guarded rank-only navigation and records

## Abstract

NativeRankedNavigationCompiler

**Theorem 1.1 (A finite Presburger formula for all rank-only records).**

$$\forall k: Nat, (\forall records: \operatorname{List}\left(\operatorname{Record}\left(k\right)\right), (\forall n: \operatorname{Fin}\left(k\right) \to Nat, ((\operatorname{Realize}\left(\operatorname{refinementFormula}\left(records\right), n\right)) \iff (\forall r: \operatorname{Record}\left(k\right), ((r \in records) \implies (\operatorname{RecordHolds}\left(n, r\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedNavigationCompiler.rank_only_refinement_compilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source is the ordered free binary magma with alpha labelled true and beta labelled false. Native substitution sends alpha to beta and beta to the ordered pair of beta and alpha. Write T(r) for its r-th iterate at alpha. Thus T(0) is alpha, T(1) is beta, and T(r+2) has left child T(r+1) and right child T(r). False address edges go left and true edges go right.

Endpoint(k) contains a residual-free RankedExpr(k,0), a fixed natural epoch, and an arbitrary fixed finite address. The original rank tuple n maps Fin(k) to the natural numbers. A scalar occurrence with decoration a evaluates to T(n(j)+a); every repeated occurrence retains the same j. Grounds are actual fixed finite trees and explicit pairs retain their ordered structure. An endpoint tree is the epoch-th substitution iterate of rankedEval(n,Fin.elim0,expression). No residual tree variables occur.

pathCost is zero for the empty address. Prepending a left edge adds one; prepending a right edge adds two. pathThreshold is zero for the empty address. Prepending an edge of cost d gives max(2,d+pathThreshold(tail)). Native path induction proves that subtree(p,T(t)) is some u exactly when there is a natural r with pathThreshold(p) at most t, t=r+pathCost(p), and T(r)=u. The maximum retains every intermediate branch requirement. In particular, the final left edge requires starting index at least two: index one is a beta leaf even though subtracting one would yield a natural number. No truncated subtraction interprets an impossible path.

atEpoch distributes the fixed substitution power through the finite syntax. A ground is substituted literally, and each scalar decoration increases by the epoch. navigate then follows explicit pairs and actual fixed grounds until the address ends, becomes absent, or enters a scalar atom with a remaining suffix. navigationValue agrees with actual subtree navigation for every unbounded original rank tuple, including endpoints born after substitution.

For a reached atomic suffix introduce a fresh natural endpoint index r. guardFormula conjoins its exact threshold and the equation n(j)+a=r+pathCost(p). A constant lower bound h is a finite conjunction excluding indices 0 through h-1, which bounds the syntax construction without bounding the variable rank. Whole-expression endpoints have a true guard and absent endpoints have a false guard. reachedExpr keeps the complete reached expression, preserving all original rank names, or uses the fresh atomic endpoint index. The existing ranked_equality_compilation theorem supplies exact whole native equality, including equality between a ranked atom and an explicit pair.

Record(k) is either a literal endpoint and retained Reply or a positive link between two endpoints. RecordHolds(n,literal(a,y)) states exact native readout equality to y. Its four possible replies are alpha, beta, branch and absent. Absence negates endpoint reachedness. Each other reply requires a reached endpoint; alpha and beta compare its whole subtree with the corresponding leaf, while branch excludes both leaves. RecordHolds(n,link(a,b)) requires actual subtrees some u and some v at both endpoints and u=v. linkFormula conjoins both independent reach guards and equality of the complete reached expressions before existentially binding their two fresh natural indices.

refinementFormula maps the finite record list to its exact formulas and conjoins them. Every original scalar coordinate remains free; only fresh endpoint indices are existentially bound. Its realization at any one shared n is equivalent to every RecordHolds(n,r) in the list. Empty lists produce top. Zero rank dimensions, root addresses, empty suffixes, both leaf labels, fixed ground exterior pieces, repeated records and rank names, and links at distinct fixed epochs are included. The construction is computable finite first-order Presburger syntax. It does not require quantifier elimination, a general decision procedure, a rank bound or a complexity bound.

This is the native rank-only refinement interpretation of URR Definition 4.4, using the arithmetic navigation route in CAR Lemma 4.1. The result is a repository-derived connection to the existing native subtree, readout and ranked equality definitions. It concerns literal records and positive links on residual-free endpoints. Complete chart supports, whole-row comparison, global address translation and quantified arithmetic decisions are separate results. An external rank policy may restrict the family further when supplied with its own arithmetic interpretation; it asserts no additional acquired rank port or physical operation.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedNavigationCompiler.rank_only_refinement_compilation`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](../ActualLeafHistoryRigidity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedEqualityCompiler](NativeRankedEqualityCompiler.md)
