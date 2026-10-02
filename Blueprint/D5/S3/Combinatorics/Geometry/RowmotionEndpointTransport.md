# Endpoint transport along the literal toggle trace

## Abstract

A complete reverse extension transports minimal ceiling endpoints to maximal floor endpoints.

Let P be a partially ordered set and let e be an equivalence from Fin N to P. The equivalence enumerates every point exactly once. Write index(e,x) for the natural value of e's inverse at x. ReverseExtension means that a strictly larger point has a smaller index. All orders and extrema below refer to the given partial order, including when two comparable points share a coordinate in a product order.

**Definition 1.1 (A complete reverse linear extension).**

$$\forall P \in \mathrm{Type},\; [PartialOrder(P)] \forall N \in \mathrm{Nat},\; \forall e \in Equiv(Fin(N), P),\; (ReverseExtension(e)) \Leftrightarrow (\forall x \in P,\; \forall y \in P,\; (x < y) \Rightarrow (index(e, y) < index(e, x)))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.ReverseExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The enumeration visits every strictly larger point before a strictly smaller point. Completeness and uniqueness come from the equivalence, rather than from this order condition alone.

**Definition 1.2 (The interval-closed toggle).**

$$\forall P \in \mathrm{Type},\; [PartialOrder(P)] \forall x \in P,\; \forall S \in Set(P),\; toggle(x, S) = If(OrdConnected(SymmDiff(S, \{x\})), SymmDiff(S, \{x\}), S)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.toggle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Toggle x in S by taking its symmetric difference with the singleton x when that candidate is order-convex; otherwise retain S. Order-convexity means that every point between two included points is included.

**Definition 1.3 (The successive literal states).**

$$\forall P \in \mathrm{Type},\; [PartialOrder(P)] \forall N \in \mathrm{Nat},\; \forall e \in Equiv(Fin(N), P),\; \forall I \in Set(P),\; (trace(e, I, 0) = I) \land (\forall k \in \mathrm{Nat},\; ((k < N) \Rightarrow (trace(e, I, k + 1) = toggle(eval(e, k), trace(e, I, k)))) \land ((N \le k) \Rightarrow (trace(e, I, k + 1) = trace(e, I, k))))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.trace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Start with trace(e,I,0)=I. At step k below N, toggle the point e(k). At and after N the state stays fixed. In the displayed recurrence e(k) denotes evaluation at the element of Fin N with natural value k, under the condition k<N.

**Theorem 1.4 (Minimal ceiling endpoints become maximal floor endpoints).**

$$\forall P \in \mathrm{Type},\; [PartialOrder(P)] \forall N \in \mathrm{Nat},\; \forall e \in Equiv(Fin(N), P),\; \forall I \in Set(P),\; \forall m \in P,\; \forall c \in P,\; (ReverseExtension(e)) \Rightarrow ((OrdConnected(I)) \Rightarrow ((Minimal(I, m)) \Rightarrow ((Minimal(upperClosure(I) \setminus I, c)) \Rightarrow ((m < c) \Rightarrow ((Maximal(trace(e, I, N), c)) \land (Maximal(lowerClosure(trace(e, I, N)) \setminus trace(e, I, N), m)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.endpoint_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be order-convex, let m be globally minimal in I, and let c be globally minimal in the non-strict upper closure of I minus I, with m strictly below c. For the actual final state J=trace(e,I,N), c is globally maximal in J, and m is globally maximal in the non-strict lower closure of J minus J. The claim holds for every complete reverse extension and every finite poset, including all finite rectangles.

At a point's visit, all smaller points retain their initial membership and all larger points have their final membership. An initial included point below an initial hole prevents insertion of any point strictly above that hole. Applying this to m<c excludes every final point above c. Minimality of c makes its insertion order-convex. Minimality of m permits its removal. Finally, any point strictly between m and a final included point either was initially present and cannot be removed, or was initially absent and would have blocked that final point's insertion. This proves maximality of m in the final floor.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.ReverseExtension`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.endpoint_transport`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.toggle`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport.trace`
