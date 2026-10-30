# Return-Distance Support Repair

## Abstract

Separated interval repair of consecutive return distances on the integers.

SupportAdjacent(P,p,q) means p and q belong to P, p<q, and P has no member strictly between them. For an allowed-distance set D and a positive integer h, gapInsertions(D,P,h) is the union of all integer intervals [p+h,q-h] over consecutive original pairs with q-p outside D. The repaired support is the union with P. This construction is defined without choosing an enumeration, and admits empty, singleton, finite and infinite supports.

**Theorem 1.1 (Insertions stay away from every original point).**

$$\begin{aligned}\forall D: \operatorname{Set}(\mathbb{Z}),\\\forall P: \operatorname{Set}(\mathbb{Z}),\\\forall h: \mathbb{Z},\\\forall t: \mathbb{Z},\\\forall s: \mathbb{Z},\\t \in \operatorname{gapInsertions}(D, P, h) \Rightarrow \\s \in P \Rightarrow \\t \le s-h \lor s+h \le t\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ReturnDistanceSupport.insertion_separated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An original point lies on or beyond one of the bracketing endpoints. Each insertion is therefore at least h away from it.

**Theorem 1.2 (The interval repair has only allowed return distances).**

$$\begin{aligned}\forall D: \operatorname{Set}(\mathbb{Z}),\\\forall P: \operatorname{Set}(\mathbb{Z}),\\\forall h: \mathbb{Z},\\0 < h \Rightarrow \\1 \in D \Rightarrow \\h \in D \Rightarrow \\(\forall p: \mathbb{Z},\forall q: \mathbb{Z},\operatorname{SupportAdjacent}(P, p, q) \Rightarrow q-p \le 2h \Rightarrow q-p \in D) \Rightarrow \\\forall x: \mathbb{Z},\\\forall y: \mathbb{Z},\\\operatorname{SupportAdjacent}(\operatorname{repairedSupport}(D, P, h), x, y) \Rightarrow \\y-x \in D\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ReturnDistanceSupport.repaired_support_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume one and h are allowed, and every original gap of length at most 2h is allowed. An illegal original gap exceeds 2h. The filled gap has edge distances h and internal distances one. For consecutive repaired points, the four possibilities (original/original, original/inserted, inserted/original, inserted/inserted) give respectively an unchanged allowed gap, h, h, and one. The separation lemma excludes crossings between distinct repaired intervals.

The window lemma states that if 2r<h and [i-r,i+r] contains an original support point, repair agrees with the original support throughout that window. The truncation lemma states that retaining only P intersect [l,u] is legal whenever every original consecutive gap of length at most u-l is legal. Neither lemma asserts that the original support is globally legal.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/ReturnDistanceSupport.insertion_separated`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ReturnDistanceSupport.repaired_support_legal`
