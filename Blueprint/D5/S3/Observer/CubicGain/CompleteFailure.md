# Complete targets and literal failure

## Abstract

Whole polynomial targets, actual response intersections and failure against arbitrary deterministic policies with early stopping.

A world of degree bound d stores a strictly entrywise positive real 2 by 2 source of rank one and trace one, a nonzero vector of d+1 ordinary polynomial coefficients, and an arbitrary real constant drift. Its gain is the whole polynomial of those coefficients. Boolean false denotes M=[[0,1],[1,1]], and true denotes J=[[0,1],[1,0]]. A finite list v is chronological: appending an atom left-multiplies the cumulative matrix. At original clock i, readAt(W,v,i) evaluates the same whole gain at i and multiplies it by the trace of the cumulative matrix of take(v,i) against the fixed source, then adds the drift. The initial read is included. There are no other observation ports or unobserved compound actions.

**Theorem 1.1 (The original singular-source condition).**

$$\forall P\in \mathbb{R}^{2\times2}, \operatorname{LegalSource}(P)\iff (\forall i,j\in \{0,1\}, 0< \operatorname{entry}(P,i,j))\land \operatorname{det}(P)= 0\land \operatorname{tr}(P)= 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/CompleteFailure.legal_source_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension two, positivity, zero determinant and trace one are exactly the existing legal-source condition. For the reverse direction the source is written in the positive chart with parameters P(1,0)/P(0,0) and P(0,1)/P(0,0). Its determinant equation and trace normalization give the exact original matrix. Thus no symmetry or off-diagonal equality is added.

**Theorem 1.2 (Exact unrestricted complete-domain correspondence).**

$$\forall d\in \mathbb{N}, \forall P\in \mathbb{R}^{2\times2}, \forall p\in \operatorname{Polynomial}(\mathbb{R}), \forall z\in \mathbb{R}, (\exists W\in \operatorname{World}(d), \operatorname{source}(W)= P\land \operatorname{gain}(W)= p\land \operatorname{drift}(W)= z)\iff (\forall i,j\in \{0,1\}, 0< \operatorname{entry}(P,i,j))\land \operatorname{det}(P)= 0\land \operatorname{tr}(P)= 1\land p\neq 0\land \operatorname{natDegree}(p)\leq d$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/CompleteFailure.whole_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero real polynomial of degree at most d is represented by its first d+1 coefficients, and reconstruction returns that same polynomial. Conversely, the ordinary polynomial of a world's coefficient vector is nonzero and has the stated degree bound. The source and drift are unchanged in both directions. Gain signs, lower degrees, all sampled or repeated roots and all real constant drifts remain present.

For a word v and an initial-inclusive reading vector h, wholeSet(v,h) consists of all worlds with readings(W,v)=h. There is no additional source or gain promise. The actual child slice(K,v,E,z) contains precisely those W in K whose immediate reading after the single next atom E is z. When K is compatible with one literal history, these are exactly its intersections with the corresponding complete child fibers.

Write N(K) for the existence of two distinct members of K. The failure recursion is L(0,K,v)=N(K), and L(n+1,K,v)=N(K) together with: for each Boolean atom E there exists a real response z with L(n,slice(K,v,E,z),v++[E]). Both action clauses are required. The repeated guard prevents a correct complete-target early stop at every node, including the terminal nodes.

**Theorem 1.3 (Same-history inclusion monotonicity).**

$$\forall d\in \mathbb{N}, \forall n\in \mathbb{N}, \forall K\in \operatorname{Set}(\operatorname{World}(d)), \forall S\in \operatorname{Set}(\operatorname{World}(d)), \forall v\in \operatorname{List}(\operatorname{Bool}()), \operatorname{L}(n,K,v)\land K\subseteq S\implies \operatorname{L}(n,S,v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/CompleteFailure.loses_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction preserves the distinct pair and sends each losing child into the corresponding full response intersection of the larger set. No cardinality or finiteness assumption is imposed on either set.

**Theorem 1.4 (Agreement with finite native-world failure).**

$$\forall n\in \mathbb{N}, \forall T\in \operatorname{Finset}(\operatorname{World}(3)), \forall v\in \operatorname{List}(\operatorname{Bool}()), \operatorname{L}(n,\operatorname{coe}(T),v)\iff \operatorname{FiniteLosing}(n,T,v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/CompleteFailure.finite_losing_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For cubic worlds and any finite support T, the set recursion is equivalent to MixedTripleExclusion.Losing. Set nontriviality is exactly cardinality at least two, and every child is the same full filter of the current support. The equivalence follows by induction on the remaining horizon.

A policy P receives the entire actual reading vector on each literal word and returns either a next Boolean atom or a complete world. Its choice can be an arbitrary deterministic function of that history. Identifies(P,0,v,W) means it returns W immediately. For n+1 further readings a returned world must equal W, while a chosen atom is immediately read on W and the policy continues at the extended literal word with n reads left. This semantics allows every early stop and imposes no output palette.

**Theorem 1.5 (Every losing fiber defeats every policy).**

$$\forall d\in \mathbb{N}, \forall n\in \mathbb{N}, \forall K\in \operatorname{Set}(\operatorname{World}(d)), \forall v\in \operatorname{List}(\operatorname{Bool}()), \forall h\in \operatorname{History}(v), \forall P\in \operatorname{Policy}(d), K\subseteq \operatorname{wholeSet}(v,h)\land \operatorname{L}(n,K,v)\implies \neg (\forall W\in K, \operatorname{Identifies}(P,n,v,W))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/CompleteFailure.loses_excludes_policy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All candidates start at the same literal history h. If the policy stops, the guard supplies two distinct complete targets receiving the same output. If it chooses an atom, the failure recursion supplies a losing actual child. Equality of the old full histories and of the new response gives equality of the new full histories; the induction hypothesis then applies. Thus the result concerns acquired original-clock histories and complete targets throughout.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/CompleteFailure.finite_losing_iff`
- Truth anchor: `D5/S3/Observer/CubicGain/CompleteFailure.legal_source_iff`
- Truth anchor: `D5/S3/Observer/CubicGain/CompleteFailure.loses_excludes_policy`
- Truth anchor: `D5/S3/Observer/CubicGain/CompleteFailure.loses_mono`
- Truth anchor: `D5/S3/Observer/CubicGain/CompleteFailure.whole_domain`
- Dependency: [D5/S3/Observer/CubicGain/MixedTripleExclusion](MixedTripleExclusion.md)
