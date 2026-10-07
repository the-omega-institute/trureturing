# Running Intersection Messages

## Abstract

Recursive separator messages characterize nonemptiness of the raw join on a finite running-intersection tree.

Node is a finite node type and Var is an arbitrary variable type. Value assigns a value type to each variable. S assigns a scope to each node, and Gamma assigns a set of complete assignments on that scope. Assignment, restriction, componentScope and rawJoin are the existing dependent record constructions. The global scope U is componentScope S on all nodes, hence the union of S n.

**Definition 1.1 (Recursive separator messages).**

$$\forall Node: Type, \forall Var: Type, [\operatorname{Finite}\left(Node\right)], \forall T: \operatorname{SimpleGraph}\left(Node\right), \forall Value: \operatorname{Family}\left(Var, Type\right), \forall S: \operatorname{Function}\left(Node, \operatorname{Set}\left(Var\right)\right), \forall Gamma: \operatorname{RelationFamily}\left(Value, S\right), \operatorname{IsTree}\left(T\right) \to \forall e: \operatorname{Dart}\left(T\right), \operatorname{M}\left(T, Value, S, Gamma, e\right) = \{t: \operatorname{Assignment}\left(Value, \operatorname{intersection}\left(\operatorname{S}\left(\operatorname{snd}\left(e\right)\right), \operatorname{S}\left(\operatorname{fst}\left(e\right)\right)\right)\right) \Vert \exists a: \operatorname{Assignment}\left(Value, \operatorname{S}\left(\operatorname{fst}\left(e\right)\right)\right), a \in \operatorname{Gamma}\left(\operatorname{fst}\left(e\right)\right) \land \operatorname{restrict}\left(a, \operatorname{intersection}\left(\operatorname{S}\left(\operatorname{snd}\left(e\right)\right), \operatorname{S}\left(\operatorname{fst}\left(e\right)\right)\right)\right) = t \land \forall w: Node, \operatorname{Adj}\left(T, w, \operatorname{fst}\left(e\right)\right) \land w \ne \operatorname{snd}\left(e\right) \to \operatorname{restrict}\left(a, \operatorname{intersection}\left(\operatorname{S}\left(\operatorname{fst}\left(e\right)\right), \operatorname{S}\left(w\right)\right)\right) \in \operatorname{M}\left(T, Value, S, Gamma, \operatorname{dart}\left(T, w, \operatorname{fst}\left(e\right)\right)\right)\}$$

*Formalization.* `D5/S3/ConceptDynamics/Gluing/RunningIntersectionMessages.separatorMessages` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For e directed from v to its parent p, a message contains the separator restriction of a Gamma v row precisely when that row passes every child message w to v, where w is adjacent to v and differs from p. The message carrier uses S p intersect S v. Swapping the intersection order is only equality transport. Recursion decreases the cardinality of the actual component reachable from v after deleting the edge. Each child component is a strict subset. A chosen root selects the darts pointing toward it; the same recurrence is defined for either orientation of every tree edge. No global join is used to define messages.

**Theorem 1.2 (Root acceptance characterizes the raw join).**

$$\forall Node: Type, \forall Var: Type, [\operatorname{Finite}\left(Node\right)], \forall T: \operatorname{SimpleGraph}\left(Node\right), \forall Value: \operatorname{Family}\left(Var, Type\right), \forall S: \operatorname{Function}\left(Node, \operatorname{Set}\left(Var\right)\right), \forall Gamma: \operatorname{RelationFamily}\left(Value, S\right), \operatorname{IsTree}\left(T\right) \land \operatorname{RunningIntersection}\left(T, S\right) \to \forall r: Node, \operatorname{Nonempty}\left(\operatorname{rawJoin}\left(Value, S, Gamma, \operatorname{univ}\left(Node\right)\right)\right) \iff \exists a: \operatorname{Assignment}\left(Value, \operatorname{S}\left(r\right)\right), a \in \operatorname{Gamma}\left(r\right) \land \forall w: Node, \operatorname{Adj}\left(T, w, r\right) \to \operatorname{restrict}\left(a, \operatorname{intersection}\left(\operatorname{S}\left(r\right), \operatorname{S}\left(w\right)\right)\right) \in \operatorname{M}\left(T, Value, S, Gamma, \operatorname{dart}\left(T, w, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/RunningIntersectionMessages.raw_join_nonempty_iff_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Running intersection means that the occurrence-induced graph of each variable is preconnected. Every occurring variable therefore has connected occurrences; absent variables impose no condition. The root is an actual node. Root acceptance asks for one Gamma r row whose restriction passes every inward message at the root.

A single global raw-join record yields every message membership by well-founded induction on the actual deleted-edge components. Conversely, message witnesses propagate local rows along the unique paths from the root. The selected rows agree on every complete edge separator. Their singleton relations are nonempty and have equal complete edge projection images. The existing local-row extension theorem glues this singleton family, and the resulting record belongs to the original local relations.

No edge projection consistency is assumed for Gamma. Value types, relations, scopes and separators may be empty or infinite. A one-node tree reduces to nonemptiness of its sole relation. For a fixed k, take Value constant with value O, S n equal to Sigma n and Gamma n equal to R n at that same k. The raw join is then the natural join on the union of those supports. This statement concerns join nonemptiness only; capacity bounds, message counts, separator width and certificate claims require separate results.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionMessages.raw_join_nonempty_iff_root`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/RunningIntersectionMessages.separatorMessages`
- Dependency: [D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords](RunningIntersectionRecords.md)
