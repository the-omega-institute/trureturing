# Two Row Cycle Obstruction

## Abstract

Every induced cycle of length at least four supports one or two Boolean rows per scope with equal complete overlap projections and empty natural join.

**Theorem 1.1 (Full overlap consistency without a global assignment).**

$$\forall u \in Universe, v \in Universe, E \in Type_{u}, V \in Type_{v},\; \forall S \in E \to \operatorname{Set}\left(V\right), n \in Nat,\; 4 \leq n \Rightarrow \left(\forall c \in \operatorname{Fin}\left(n\right) \to V,\; \operatorname{Injective}\left(c\right) \Rightarrow \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \exists e \in E,\; \operatorname{c}\left(i\right) \in \operatorname{S}\left(e\right) \land \operatorname{c}\left(\operatorname{finRotate}\left(n, i\right)\right) \in \operatorname{S}\left(e\right)\right) \Rightarrow \left(\left(\forall e \in E, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \neg(i = j) \Rightarrow \left(\operatorname{c}\left(i\right) \in \operatorname{S}\left(e\right) \Rightarrow \left(\operatorname{c}\left(j\right) \in \operatorname{S}\left(e\right) \Rightarrow \left(\operatorname{finRotate}\left(n, i\right) = j \lor \operatorname{finRotate}\left(n, j\right) = i\right)\right)\right)\right) \Rightarrow \left(\exists R \in \pi e:E, \operatorname{Set}\left(\operatorname{S}\left(e\right) \to Bool\right),\; \left(\forall e \in E,\; \exists a \in \operatorname{S}\left(e\right) \to Bool, b \in \operatorname{S}\left(e\right) \to Bool,\; \operatorname{R}\left(e\right) = \{a, b\}\right) \land \left(\left(\forall e \in E, f \in E,\; \operatorname{leftProjection}\left(S, e, f, \operatorname{R}\left(e\right)\right) = \operatorname{rightProjection}\left(S, e, f, \operatorname{R}\left(f\right)\right)\right) \land \neg(\exists g \in V \to Bool,\; \forall e \in E,\; \operatorname{restrict}\left(g, \operatorname{S}\left(e\right)\right) \in \operatorname{R}\left(e\right))\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/TwoRowCycleObstruction.two_row_cycle_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Catriel Beeri; Ronald Fagin; David Maier; Mihalis Yannakakis (1983). *On the Desirability of Acyclic Database Schemes*. DOI: [10.1145/2402.322389](https://doi.org/10.1145/2402.322389). URL: <https://s3.us.cloud-object-storage.appdomain.cloud/res-files/500-jacm83a.pdf>.

*Commentary.*

The universes u and v are independent. E is an arbitrary scope index type and V is an arbitrary variable type; either carrier may be infinite. S assigns a set of variables to each scope. The injection c lists n distinct cycle vertices, with n at least four. Every consecutive cycle pair lies in a scope. Within any scope, two distinct cycle indices must be consecutive in one of the two orientations.

A scope A in a function type denotes its subtype of variables. The local clause states explicitly that R(e)={r0,r1} for two functions on S(e). These functions may coincide when the scope contains no cycle vertex; each relation therefore has one or two rows. For fixed e and f, both projection images use the same carrier (S(e) intersect S(f)) to Bool. leftProjection(S,e,f,R(e)) is the image of R(e) under r mapping to (x mapping to r(x)), where x belongs to that complete intersection and is viewed in S(e). rightProjection uses the same x viewed in S(f). restrict(g,A) is x mapping to g(x) on A. One family R satisfies all these clauses simultaneously, and no ambient assignment g satisfies all its local relations.

Write z=c(0) and l=c(n-1). For each scope A and variable x let p_A(x) be the Boolean indicator of z in A and x=l. For b in Bool define row(A,b)(x)=b xor p_A(x) when x lies in the range of c, and false otherwise. R(A) is the range of this Boolean indexed constructor, equivalently {row(A,false),row(A,true)}. Every off-cycle coordinate is false, regardless of the size of A or V.

If A contains both z and l, chordlessness forces its cycle support into {z,l}: an additional cycle vertex would have to be adjacent to both endpoints of this edge, which is impossible for n at least four. Consequently p_A(c(i)) xor p_B(c(i)) is constant as i ranges over the shared cycle support. When z belongs to exactly one scope, two shared vertices with different potentials would force z into the other scope as well.

To match row(A,b) on B, choose a shared cycle anchor j when one exists and put d=b xor p_A(c(j)) xor p_B(c(j)). The constant difference law gives row(B,d)=row(A,b) on every shared cycle coordinate. With no shared cycle vertex choose d=false. On all other coordinates in the complete intersection both rows are false. Phase alignment thus preserves the entire intersection. Applying this construction in each ordered direction proves equality of both full projection images.

A global satisfying assignment would have equal values along the successor path from c(0) to c(n-1). The closing edge lies in a scope containing both endpoints, where their values are opposite. This is a contradiction. The edge charge is zero along the successor path and one at the closing edge, so its total is odd for every n, including even n.

Empty, duplicate and contained scopes, coordinates outside the cycle, and variables outside the union of all scopes remain allowed. No finiteness, nonemptiness or decidable equality assumption is imposed on E or V. The classical acyclic database scheme theorem supplies background for pairwise projection consistency in finite schemes. The explicit Boolean construction here gives at most two rows per scope and an empty join over arbitrary carriers. This precise statement is not attributed verbatim to that paper, and no claim of originality or full acyclicity classification is made.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/TwoRowCycleObstruction.two_row_cycle_obstruction`
