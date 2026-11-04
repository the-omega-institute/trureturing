# Native endpoint causal order

## Abstract

The exact local and creating-split edges generate the native endpoint order.

The finite event set and original Call labels are NativeEndpointEventIdeals.events. First chooses the root promotion for alpha birth or root split for beta birth, requiring actual membership. Edge recursively contains exactly a local promotion-before-split edge when both occur, a parent split edge to the first existing local event of either child, and the corresponding shifted edges inside each child. There is no edge into an inactive alpha terminal, and a beta terminal born beta has no event.

Notation and native definitions: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals`. In particular Bool = {false,true}, Source is the original free binary-tree algebra, Call consists of promote(p) and split(p) at p : List(Bool), Event(b,t) is the subtype of calls in events(b,t), val is its underlying Call, and < is the induced strict prefix/phase order. TransGen(R,c,d) means there is a nonempty finite R-path from c to d; it is not reflexive closure.

For b : Bool, t : Source and e : Call, First(b,t,e) means e = ite(b,promote([]),split([])) and e belongs to events(b,t). For every birth type and all calls c,d, Edge(b,of(a),c,d) is false. For l,r : Source, Edge(b,mul(l,r),c,d) is exactly the disjunction of: b = true, c = promote([]), d = split([]); there exists e : Call with First(false,l,e), c = split([]), d = shift(e,[false]); there exists e : Call with First(true,r,e), c = split([]), d = shift(e,[true]); there exist e,f : Call with c = shift(e,[false]), d = shift(f,[false]), Edge(false,l,e,f); or there exist e,f : Call with c = shift(e,[true]), d = shift(f,[true]), Edge(true,r,e,f). Here a,b range over Bool, c,d over Call, ite is Boolean selection, and shift prefixes the indicated address. This recursive definition retains exactly the original local and creating-split edges.

**Theorem 1.1 (Exact transitive-closure correspondence).**

$$\forall b: \operatorname{Bool}, (\forall t: \operatorname{Source}, (\forall c: \operatorname{Event}\left(b, t\right), (\forall d: \operatorname{Event}\left(b, t\right), (\operatorname{TransGen}\left(\operatorname{Edge}\left(b, t\right), \operatorname{val}\left(c\right), \operatorname{val}\left(d\right)\right) \iff c < d))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointCausalOrder.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every birth type, every target and every two members of its endpoint-labelled finite event set, the transitive closure of Edge relates their original Calls exactly when the induced prefix/phase order strictly relates them. This also covers empty and singleton event sets. The result identifies the order used by native execution adequacy with the exact causal order defined in Atomic Generation Acquisition AA17.2; it is consumed for every promised comb by NativePromiseCausalBoundary.result.

Every generating edge strictly increases the prefix/phase order. Conversely, structural induction finds the first local event before any event in a nonempty child. A parent split reaches that first event directly and then follows the child induction. A root promotion first reaches the root split. Events in one child lift that child's generating path; distinct children cannot be related by prefix ancestry. Thus every strict comparison has an actual path of the specified local edges. Antisymmetry of the existing partial order excludes directed cycles.

The correspondence proves source-specific causal structure, with no execution, reachability, rational clock, chosen serial order or probability-law premise. Full seven/eight laws remain outside this module.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointCausalOrder.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals](NativeEndpointEventIdeals.md)
- Narrative reference: [D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals](NativeEndpointEventIdeals.md)
