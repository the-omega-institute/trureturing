# Coherent All-Subface Follower Covers

## Abstract

Coherent closed forward-invariant finite-follower languages over finite alphabets have finite live covers with onto maps on entire paths.

**Theorem 1.1 (Finite followers of a finite graph).**

$$\begin{aligned}\forall A: Type, \forall V: Type, [Finite(V)], \forall e: V \Rightarrow V \Rightarrow Prop, \forall ell: V \Rightarrow A, \\Finite(Followers(graphLanguage(e, ell)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.finite_followers_of_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary alphabet and a finite vertex type, the nonempty followers of the complete graph language form a finite type. Consuming a finite past tracks the reachable subset at the next time. Every initial vertex is allowed, so the empty past begins at the entire vertex set and needs no predecessor.

**Theorem 1.2 (The powerset bound).**

$$\begin{aligned}\forall A: Type, \forall V: Type, [Fintype(V)], \forall e: V \Rightarrow V \Rightarrow Prop, \forall ell: V \Rightarrow A, \\Nat.card(Followers(graphLanguage(e, ell))) \le 2^{Fintype.card(V)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.followers_card_le_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A presentation on n vertices has at most 2^n nonempty followers. Followers factor through reachable subsets, including subsets containing transient or dead vertices; no trimming premise is needed.

**Theorem 1.3 (Soficity supplies finite followers).**

$$\begin{aligned}\forall A: Type, \\\forall L: Set(Word(A)), \\IsSofic(L) \Rightarrow Finite(Followers(L))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.finite_followers_of_sofic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing IsSofic predicate supplies a finite vertex-labelled graph presentation and hence finite followers. No particular presentation is retained in the language-family data.

**Definition 1.4 (Coherent language premises).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], {}\\LanguageSystem(A) = \{L:\pi_{F:Finset(I)} Set(ScopedWord(A, F)) \mid (\forall F: Finset(I), Nonempty(L(F))) \land (\forall F: Finset(I), IsClosed(L(F))) \land (\forall F: Finset(I), ForwardInvariant(L(F))) \land (\forall F: Finset(I), Finite(Followers(L(F)))) \land (\forall F: Finset(I), \forall G: Finset(I), \forall h: F \subseteq G, Set.image(restrictWord(A, h), L(G)) = L(F))\}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.LanguageSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary index type I and a family of topological alphabets A_i, every finite scope F has a nonempty closed forward-invariant language L_F with finitely many nonempty followers. For F contained in G, the coordinate restriction of entire words in L_G has image exactly L_F. The shift need not be onto. ofSofic obtains this data from a coherent family of sofic languages. Finite alphabets are required only for finiteness of vertices.

**Definition 1.5 (Reachable all-subface contexts).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \\S.Context(F) = \{s:RawContext(A, F) \mid \exists u: List(Letter(A, F)), (S.IsPrefix(F, u)) \land (s = S.vector(F, u))\}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.Context` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write Q_H(u) for the follower of a finite past u in L_H. A context at F is the vector of Q_H(u restricted to H) over every H contained in F, realized by one common past u that extends to a word in L_F. Reachability is part of the definition; arbitrary independent choices of followers are excluded. The face type is finite by the powerset of F, even when I is uncountable. Contexts inject into the product of the finite follower types.

**Definition 1.6 (Allowed current letters).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \\S.Vertex(F) = \{(s,a):S.Context(F) \times Letter(A, F) \mid Nonempty(derivative(apply(Subtype.val(s), topFace(F)), a))\}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vertex consists of a reachable context s and a current letter a whose left derivative in the top component is nonempty. Its label is a. An edge requires the next context to be the componentwise derivative by the restrictions of a. The next letter is already allowed because its endpoint is a vertex. This gives deterministic context updates without choosing a representative past.

**Theorem 1.7 (Exact soundness from an arbitrary initial past).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \\\forall p: S.Path(F), \\\forall u: List(Letter(A, F)), \\Subtype.val(context(p(0))) = S.vector(F, u) \Rightarrow prepend(u, S.pathLabels(p)) \in S.language(F)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.path_in_initial_follower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be any entire graph path and let u represent its initial context. Then u concatenated with the whole label word of p belongs to L_F. The past u may be nonempty. At time n the edge equations reconstruct the context after u followed by the first n labels. All these finite prefixes have continuations. Choosing continuations gives a sequence eventually equal to the prescribed future in each coordinate; the existing product-convergence and closed-limit lemmas place that future in the closed initial follower.

**Theorem 1.8 (The complete graph language is exact).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \\graphLanguage(S.Edge(F), S.label(F)) = S.language(F)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.graphLanguage_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph language equals L_F with every initial vertex allowed. Forward invariance removes the initial finite past from path soundness. Conversely each word in L_F gives a path of its prefix contexts from the empty past. The construction uses one-sided time and requires no negative-time orbit or onto shift.

**Theorem 1.9 (Every vertex starts a whole path).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \\\forall v: S.Vertex(F), \exists p: S.Path(F), p(0) = v\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.vertex_live` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a finite past representing the vertex context and a whole continuation witnessing allowedness of its current letter. The prefix-context path of that single admitted concatenation, beginning after the chosen past, starts at the prescribed vertex. Thus no admitted vertex is dead.

**Theorem 1.10 (Every stage is nonempty).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \\Nonempty(S.Vertex(F))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.vertex_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A word from the nonempty language gives a prefix-context path and therefore an initial vertex. This remains valid for an empty coordinate scope.

**Theorem 1.11 (Labels commute with deletion).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \forall G: Finset(I), \forall h: F \subseteq G, \forall v: S.Vertex(G), S.label(S.restrictVertex(h, v)) = restrictLetter(A, h, S.label(v))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictVertex_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertex map restricts the current symbol and deletes the face-vector components outside the smaller scope. Its label is exactly the coordinate restriction of the original label.

**Theorem 1.12 (Deletion preserves edges).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \forall G: Finset(I), \forall h: F \subseteq G, \forall v: S.Vertex(G), \forall w: S.Vertex(G), S.Edge(v, w) \Rightarrow S.Edge(S.restrictVertex(h, v), S.restrictVertex(h, w))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictVertex_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each smaller-scope face is also a larger-scope face. The corresponding derivative equation is literally one of the original edge equations. A projected allowed letter remains allowed by restriction of the common admitted extension.

**Theorem 1.13 (Identity on vertices).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \forall v: S.Vertex(F), S.restrictVertex(Subset.refl(F), v) = v\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictVertex_refl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restriction from a scope to itself is the identity, including the entire reachable context and its current letter.

**Theorem 1.14 (Exact vertex deletion squares).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \forall G: Finset(I), \forall H: Finset(I), \forall h: F \subseteq G, \forall k: G \subseteq H, \forall v: S.Vertex(H), S.restrictVertex(h, S.restrictVertex(k, v)) = S.restrictVertex(Subset.trans(h, k), v)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictVertex_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For F contained in G contained in H, restricting from H to G and then to F equals restriction directly from H to F. All subface components and symbols coincide; no choice of presentation or representative past enters the maps.

**Theorem 1.15 (Identity on whole paths).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \forall p: S.Path(F), S.restrictPath(Subset.refl(F), p) = p\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictPath_refl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise identity on vertices induces identity on entire path spaces.

**Theorem 1.16 (Exact whole-path deletion squares).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \forall G: Finset(I), \forall H: Finset(I), \forall h: F \subseteq G, \forall k: G \subseteq H, \forall p: S.Path(H), S.restrictPath(h, S.restrictPath(k, p)) = S.restrictPath(Subset.trans(h, k), p)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictPath_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise composition of vertex restrictions proves composition on complete infinite paths. Equality includes time zero.

**Theorem 1.17 (Every prescribed whole path lifts).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \forall G: Finset(I), \forall h: F \subseteq G, Surjective(S.restrictPath(h))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictPath_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an arbitrary target path p, its label word z, and one past u representing its initial context. Initial-follower soundness puts the single concatenation uz in L_F. Whole-word coordinate surjectivity gives one w in L_G restricting to uz. At time n choose the context after the first length(u)+n letters of w and the current letter at that time. The resulting graph path restricts to p at every time: its context projects to the context after u followed by the first n letters of z, and its letter projects to z(n). The fine initial context is after a finite past and is not required to be empty. Vertex, edge or label surjectivity alone is not used as a replacement for this assertion.

**Theorem 1.18 (Whole-path equality in the graph-language interface).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\\forall F: Finset(I), \forall G: Finset(I), \forall h: F \subseteq G, graphLanguage(S.Edge(G), S.restrictVertex(h)) = graphLanguage(S.Edge(F), id)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.projected_path_language` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The label map here is the vertex restriction itself. Its complete graph language is exactly the smaller graph path language with identity labels. Edge preservation gives one inclusion; surjectivity of the entire path map gives the other.

**Theorem 1.19 (Compatibility with the existing prefix criterion).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\{}[\forall i: I, Finite(A(i))], \\\forall F: Finset(I), \forall G: Finset(I), \forall h: F \subseteq G, \forall p: \mathbb{N} \Rightarrow S.Vertex(F), p \in graphLanguage(S.Edge(F), id) \Rightarrow \forall m: \mathbb{N}, PrefixLift(S.Edge(G), S.restrictVertex(h), p, m)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.every_prefix_lifts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite alphabets, every finite prefix of every whole target path lifts through the vertex restriction. This applies the existing graphLanguage_eq_iff_prefix_lifts theorem to the exact whole-path equality. Its finite inverse-system compactness argument is reused rather than reproved.

**Theorem 1.20 (One fixed finite product bound).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\{}[\forall i: I, Finite(A(i))], \\\forall F: Finset(I), \\Nat.card(S.Vertex(F)) \le Nat.card(Letter(A, F)) \cdot \prod_{H:Face(F)} Nat.card(Followers(S.language(Subtype.val(H))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.vertex_card_bound_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertex cardinal is at most the alphabet cardinal times the product of the nonempty-follower cardinals over all subfaces H of F. The injection records the current symbol and all follower components; Nat.card product and Pi formulas supply the estimate. This bound depends only on the once-fixed languages at subfaces of F, independently of every later upper scope.

**Theorem 1.21 (The empty-scope singleton loop).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\(Nonempty(S.Vertex(\emptyset))) \land (Subsingleton(S.Vertex(\emptyset))) \land (\forall v: S.Vertex(\emptyset), \forall w: S.Vertex(\emptyset), S.Edge(v, w))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.empty_singleton_loop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the empty scope the alphabet and whole-word type are singletons. Nonemptiness forces its language to contain the unique word, all reachable follower components are the full set, and its unique vertex has a loop.

**Theorem 1.22 (Coherent finite live covers).**

$$\begin{aligned}\forall I: Type, \forall A: I \Rightarrow Type, [\forall i: I, TopologicalSpace(A(i))], \forall S: LanguageSystem(A), \\{}[\forall i: I, Finite(A(i))], \\(\forall F: Finset(I), Finite(S.Vertex(F))) \land (\forall F: Finset(I), Nonempty(S.Vertex(F))) \land (\forall F: Finset(I), \forall v: S.Vertex(F), \exists p: S.Path(F), p(0) = v) \land (\forall F: Finset(I), graphLanguage(S.Edge(F), S.label(F)) = S.language(F)) \land (\forall F: Finset(I), \forall G: Finset(I), \forall h: F \subseteq G, Surjective(S.restrictPath(h))) \land (\forall F: Finset(I), \forall v: S.Vertex(F), S.restrictVertex(Subset.refl(F), v) = v) \land (\forall F: Finset(I), \forall G: Finset(I), \forall H: Finset(I), \forall h: F \subseteq G, \forall k: G \subseteq H, \forall v: S.Vertex(H), S.restrictVertex(h, S.restrictVertex(k, v)) = S.restrictVertex(Subset.trans(h, k), v)) \land (\forall F: Finset(I), \forall G: Finset(I), \forall h: F \subseteq G, \forall v: S.Vertex(G), S.label(S.restrictVertex(h, v)) = restrictLetter(A, h, S.label(v))) \land (\forall F: Finset(I), \forall G: Finset(I), \forall h: F \subseteq G, \forall v: S.Vertex(G), \forall w: S.Vertex(G), S.Edge(v, w) \Rightarrow S.Edge(S.restrictVertex(h, v), S.restrictVertex(h, w))) \land (\forall F: Finset(I), \forall p: S.Path(F), S.restrictPath(Subset.refl(F), p) = p) \land (\forall F: Finset(I), \forall G: Finset(I), \forall H: Finset(I), \forall h: F \subseteq G, \forall k: G \subseteq H, \forall p: S.Path(H), S.restrictPath(h, S.restrictPath(k, p)) = S.restrictPath(Subset.trans(h, k), p)) \land (\forall F: Finset(I), \forall G: Finset(I), \forall h: F \subseteq G, \forall p: \mathbb{N} \Rightarrow S.Vertex(F), p \in graphLanguage(S.Edge(F), id) \Rightarrow \forall m: \mathbb{N}, PrefixLift(S.Edge(G), S.restrictVertex(h), p, m)) \land (\forall F: Finset(I), Nat.card(S.Vertex(F)) \le Nat.card(Letter(A, F)) \cdot \prod_{H:Face(F)} Nat.card(Followers(S.language(Subtype.val(H))))) \land ((Nonempty(S.Vertex(\emptyset))) \land (Subsingleton(S.Vertex(\emptyset))) \land (\forall v: S.Vertex(\emptyset), \forall w: S.Vertex(\emptyset), S.Edge(v, w)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.coherent_follower_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed graph stages are finite, nonempty, forward-live and exact presentations of their languages. The vertex and whole-path restrictions have identity and composition laws, preserve labels and edges, and are surjective on whole paths. The all-subface product bound and empty-scope loop describe the size and initial object. These conclusions are conditional on the coherent language family. A coherent family has not been constructed from an arbitrary compact source with shadowing, so original Peng Q5.1 remains open. The result is a general symbolic and topological dynamics bridge and carries no global novelty or official-resolution claim.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.Context`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.LanguageSystem`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.Vertex`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.coherent_follower_cover`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.empty_singleton_loop`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.every_prefix_lifts`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.finite_followers_of_graph`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.finite_followers_of_sofic`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.followers_card_le_pow`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.graphLanguage_exact`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.path_in_initial_follower`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.projected_path_language`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictPath_comp`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictPath_refl`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictPath_surjective`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictVertex_comp`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictVertex_edge`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictVertex_label`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.restrictVertex_refl`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.vertex_card_bound_product`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.vertex_live`
- Truth anchor: `D5/S1/Dynamics/Shadowing/CoherentFollowerCover.vertex_nonempty`
- Dependency: [D5/S1/Dynamics/Shadowing/WholePathProjection](WholePathProjection.md)
