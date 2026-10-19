using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SeidelSwitching;

internal sealed class VertexIdentitySwitchesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/gervacio2026identityseidel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite nonempty simple graph has every vertex as an identity Seidel switch if and only if it has one vertex. Edge-count preservation forces regularity, and switching at a vertex changes the degree of each other vertex by one.",
        H("Every vertex an identity Seidel switch"),
        Blocks(
            Node("switch", "Seidel switching across a subset", "seidelSwitch", SwitchFormula(),
                "Theorem 2.6, page 6: \"Let G be a graph and S a non-empty subset of V(G). Then S(G) is obtained from G by deleting all edges xy with x ∈ S and y ∈ V(G) ∖ S, and adding all non-edges xy with x ∈ S and y ∈ V(G) ∖ S. Edges with both ends in S or both ends in V(G) ∖ S remain unchanged.\" The displayed adjacency relation is the subset switch: different membership in S negates G.Adj, equal membership preserves it, and x ≠ y excludes loops. For the empty subset the relation is G.Adj, agreeing with the source's empty-switch convention on page 6. Section 2.1, page 3: \"Let G be a graph and v ∈ V(G). The Seidel switch of G by v, denoted v(G), is the graph obtained from G by deleting all edges vy where y ∈ N_G(v) and adding all edges vz where z ∈ V(G) ∖ N_G(v) and z ≠ v. In other words, we complement the adjacency relation between v and the rest of the vertex set, while leaving all other adjacencies unchanged.\" Taking S = {v} gives this vertex switch.",
                AssessedProvenance.FromLiterature(Source)),
            Node("vertex", "Vertex identity Seidel switch", "IsVertexISS", VertexFormula(),
                "Definition 4.1, page 8: \"Let G be a graph. A subset S ⊆ V(G) is called an identity Seidel switch (abbreviated ISS) if S(G) ≅ G.\" Section 4, page 9: \"We say that {x} is a vertex-ISS if {x} is an ISS, and that {x, y} is an edge-ISS if {x, y} is an ISS and xy ∈ E(G).\" Nonempty expresses existence of a graph isomorphism; the cut is precisely the singleton {x}.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete characterization", "claim", ClaimFormula(),
                "Problem 6.1, page 13: \"Characterize graphs G for which every vertex is a vertex-ISS. Lemma 4.4 gives a necessary condition in terms of the minimum and maximum degree; can this be strengthened to a complete characterization?\" Section 2, page 3: \"Throughout, a graph G is an ordered pair G = ⟨V(G), E(G)⟩ where V(G) is a non-empty finite set whose elements are called vertices and E(G) is a set of 2-element subsets of V(G) called edges.\" V is any Type with Fintype, DecidableEq and Nonempty instances, and G is any SimpleGraph on V. The answer is that its cardinality equals one. There is no connectivity, regularity, or adjacency-decidability hypothesis.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(DescribeId.Create("seidel-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Exactly the one-vertex graph"), StatementSource.FromAuthor(Disp(Call("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Switching at v leaves the nonincident edges unchanged. The old and new incident-edge counts are the two complementary neighbour counts, whose sum is card(V)−1. Hence the new edge count plus twice degree(v) equals the old edge count plus card(V)−1. An identity switch preserves the edge count; if every vertex is an identity switch, twice every degree equals card(V)−1. If card(V)>1 this forces a positive common degree. Choose a neighbour w of v. Switching at v lowers the degree of w by one, while the isomorphism would send w to a vertex with the original common degree: contradiction. At order one the adjacency relation is empty and the switch equals G. More generally, at a vertex y, switching across S preserves same-side neighbours and exchanges crossing neighbours with crossing non-neighbours. The new degree plus twice the old crossing-neighbour count equals the old degree plus the number of vertices on the opposite side. This identity includes empty and full cuts. Natural subtraction denotes truncated subtraction. The literal conclusion of Lemma 4.4 includes a same-vertex case in the one-vertex graph; an adjacency assertion there needs distinct vertices. The characterization does not answer Problems 6.2–6.4."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gervacio-2026-vertex-identity-seidel-switches"),
                    ResolutionKind.Proved)),
            // GV-PROVENANCE
            Paragraph(Text(
                "Application scope and provenance. The applications below use the cut-switch and vertex-ISS definitions already described above. The family derivations are by Haobo Ma and Wenlin Zhang; the cited Gervacio source supplies terminology and context, and no global priority claim is made for these derivations. The published Lean source at https://github.com/the-omega-institute/trureturing/blob/c45a4dc193485b3a2979b4df7516972221ede61c/D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.lean exposes seidelSwitch, IsVertexISS, claim and result. Its result is the all-vertices characterization above. The following application arguments are mathematical exposition, not further admitted Lean theorem declarations. The degree calculations are explained directly from the cut definition; they require no public access to the owner's private proof lemmas.")),
            // GV-D
            Paragraph(Text(
                "Application GV-D — definitions. Let G be a simple graph on a vertex set V. Write G^S for seidelSwitch G S, so distinct vertices on opposite sides of S have their adjacency toggled, and every other pair keeps its adjacency. Write ISS(G,S) for the existence of an actual graph isomorphism G^S → G, and W(G) = {v ∈ V : ISS(G,{v})}; thus membership in W is exactly the existing IsVertexISS predicate. Define the partner graph P(G) on V by P(G).Adj(x,y) if and only if G.Adj(x,y) and ISS(G,{x,y}). The original adjacency condition is part of this definition. Define U(G) = {v : for every x, not P(G).Adj(v,x)}. When V is finite, this is exactly the set of vertices of degree zero in P(G), because a finite neighbor set has cardinality zero exactly when it is empty. Say G is covered if every v belongs to W(G) or has a neighbor in P(G). Then U(G) ⊆ W(G): the partner alternative of coverage contradicts the defining nonadjacency of a member of U. Essentiality and singleton-ISS membership are distinct predicates.")),
            // GV-T
            Paragraph(Text(
                "Application GV-T — covariance and two switches. For any subsets S,T, (G^S)^T = G^(S △ T), where △ is symmetric difference: for each distinct pair, toggling twice cancels and toggling once negates adjacency. For any graph isomorphism f:G → H, the same underlying bijection is an isomorphism G^S → H^(f(S)); it preserves adjacency and cut membership simultaneously. Applying this with S={x}, and composing with an actual switch isomorphism and its inverse, proves x ∈ W(G) if and only if f(x) ∈ W(H). In particular f restricts to a bijection W(G) → W(H), whose inverse is the restriction of f⁻¹. These statements concern labelled switches and transport of actual isomorphisms; they do not assert that the ISS subsets are closed under symmetric difference.")),
            // GV-T
            Paragraph(Text(
                "Application GV-T — the complete local singleton set. Fix any actual p:G^{v} → G, with G^{v} meaning G^{ {v} }, and put H=G^{v}. At x=v, H^{v}=G and p⁻¹:G → H certifies v ∈ W(H). At x≠v, H^{x}=G^{ {v,x} }. An isomorphism H^{x} → H composes with p to give G^{ {v,x} } → G; conversely an isomorphism G^{ {v,x} } → G composes with p⁻¹ to give H^{x} → H. Therefore W(H) = {v} ∪ {x≠v : ISS(G,{v,x})}. Transport by the given p sends this entire set bijectively onto W(G), and in particular p(v) ∈ W(G). This argument applies to every actual p, without selecting a preferred switching permutation.")),
            // GV-T
            Paragraph(Text(
                "Application GV-T — the actual partner correspondence. For every x∈V, P(G).Adj(v,x) if and only if p(x)∈W(G), p(x)≠p(v), and not G.Adj(p(v),p(x)). Indeed, a partner is distinct from v and its two-point switch puts x in W(H) by the local formula. Its original adjacency to v is toggled to nonadjacency in H, and p preserves that relation. Conversely the three conditions pull back under p to x∈W(H), x≠v and not H.Adj(v,x). The local formula supplies ISS(G,{v,x}), while the singleton toggle supplies the original edge G.Adj(v,x). Thus the equivalence retains both the actual switch and the original edge.")),
            // GV-T
            Paragraph(Text(
                "Application GV-T — exact finite count. Suppose V is finite, let k=|W(G)|, and regard w=p(v) as a vertex of the induced graph K=G[W(G)]. The map x↦p(x) is a bijection from N_P(v) to the neighbors of w in the complement of K: the preceding equivalence gives its membership condition, and y↦p⁻¹(y) is its inverse. Hence d_P(v)=k−1−d_K(w). Here k≥1 since w∈W(G), and 0≤d_K(w)≤k−1, so the formula also agrees with successive natural subtraction. This is a neighbor bijection, not just a comparison of degree sequences.")),
            // GV-TC
            Paragraph(Text(
                "Application GV-TC — both count endpoints and fixing. The count gives d_P(v)=0 if and only if d_K(p(v))=k−1, that is, p(v) is adjacent to every other vertex of W(G). It also gives d_P(v)=k−1 if and only if d_K(p(v))=0. Equivalently these follow by taking the empty and full possibilities in the complement-neighbor correspondence. If W(G)={v}, then every actual p:G^{v} → G fixes v, since p(v)∈W(G). If v∈U(G) and an actual p is given, p(v) is universal in G[W(G)]; this conclusion needs no coverage assumption. If W(G) is independent, universality forces W(G)={p(v)}. Since p itself witnesses v∈W(G), this is {v}, and every switching isomorphism at v fixes it.")),
            // GV-TC
            Paragraph(Text(
                "Application GV-TC — complete and intermediate singleton graphs. Assume G is covered. If G[W(G)] is complete, choose a switching isomorphism at each v∈W(G). Its image is universal in that complete graph, so d_P(v)=0. Thus W(G)⊆U(G), and coverage gives the reverse inclusion; hence U(G)=W(G). If instead |U(G)|=1 and |W(G)|>1, the induced singleton graph is neither complete nor independent: completeness would give U=W, and independence, applied to the essential vertex and its switch supplied by coverage, would give |W|=1. Moreover |W|≥3. If |W|=2, the universal image of the essential vertex is adjacent to the only other singleton vertex, making G[W] complete, a contradiction. The condition |U|=1 alone has not been replaced by |W|=1.")),
            // GV-B
            Paragraph(Text(
                "Application GV-B — exact edge and degree balances. Suppose V is finite of order n, write e(G) for its edge count, and take any v∈V. The n−1 possible edges incident to v split into its d_G(v) old neighbors and n−1−d_G(v) old nonneighbors. The first set disappears and the second appears; nonincident edges stay fixed. Consequently e(G^{v})+2d_G(v)=e(G)+(n−1), and in the integers e(G^{v})−e(G)=n−1−2d_G(v). At v the degrees satisfy d_{G^{v}}(v)+d_G(v)=n−1. At y≠v, all incident edges except yv stay fixed, so d_{G^{v}}(y)+2·1_{G.Adj(y,v)}=d_G(y)+1. These additive identities avoid ambiguity from truncated natural subtraction; each indicator is 1 when its subscript is true and 0 otherwise.")),
            // GV-B
            Paragraph(Text(
                "Application GV-B — original-edge balance and parity. For every original edge xy, x≠y and (G^{x})^{y}=G^{ {x,y} }. The edge xy is removed in the first switch, so d_{G^{x}}(y)=d_G(y)−1. Adding the two integer singleton edge changes gives e(G^{ {x,y} })−e(G)=2(n−d_G(x)−d_G(y)). Actual graph isomorphisms preserve edge count. It follows that v∈W(G) implies 2d_G(v)=n−1, and P(G).Adj(x,y) implies d_G(x)+d_G(y)=n. In particular, if G is covered and U(G) is nonempty, an essential vertex supplies a singleton switch and n=2d_G(v)+1 is odd. No converse to the partner degree-sum condition has been asserted.")),
            // GV-2D
            Paragraph(Text(
                "Application GV-2D — exact neighborhoods at every h≥1. Let |V|=2h+1 with h≥1, and suppose every degree of G is h or h+1. If v∈W(G), the singleton balance gives d_G(v)=h. Fix any actual p:G^{v} → G. For x≠v, an original neighbor x of degree h would have switched degree h−1, and an original nonneighbor x of degree h+1 would have switched degree h+2. Each contradicts degree preservation at p(x), whose degree in G is h or h+1. Thus G.Adj(v,x) if and only if d_G(x)=h+1. The same equivalence holds at x=v because loops are absent and d_G(v)=h. Hence N_G(v) is exactly the upper degree level. Every singleton-ISS vertex has degree h, so W(G) is independent.")),
            // GV-2D
            Paragraph(Text(
                "Application GV-2D — all fixing isomorphisms. Under the same hypotheses, if v∈U(G) and an actual p:G^{v} → G is supplied, the independence just proved and the transport argument imply W(G)={v}. Every actual q:G^{v} → G therefore fixes v. In a covered graph, membership in U supplies the required singleton switch, so the conclusion holds for every essential vertex. The argument has used the complete two-degree hypothesis and all h≥1; it imposes no connectivity or regularity assumption and does not settle the unrestricted fixing question.")),
            // GV-2E
            Paragraph(Text(
                "Application GV-2E — necessity for every original edge. In any finite graph with all degrees in {h,h+1}, let xy be an original edge and let z be any vertex outside {x,y}. Put c_z=1_{G.Adj(z,x)}+1_{G.Adj(z,y)}. Only those two incident edges are toggled, so d_{G^{ {x,y} }}(z)+2c_z=d_G(z)+2. If an actual pair-switch isomorphism exists, its image of z has an allowed original degree. The case c_z=0 would give degree d_G(z)+2≥h+2; the case c_z=2 would give degree d_G(z)−2≤h−1. Both are impossible. Thus c_z=1 at every outside z, equivalently G.Adj(z,x) if and only if not G.Adj(z,y). This proof needs neither the order 2h+1 nor coverage, and in particular includes the full original two-degree setting.")),
            // GV-2E
            Paragraph(Text(
                "Application GV-2E — sufficiency and the actual certificate. Conversely, suppose every z outside {x,y} is adjacent to exactly one endpoint. Define σ(x)=y, σ(y)=x and σ(z)=z for every outside vertex. This involution is a bijection G^{ {x,y} } → G. A pair of outside vertices is unchanged both by switching and by σ. The endpoint pair is unchanged by the cut and is sent to its reverse, which has the same adjacency. A crossing pair has its adjacency toggled; replacing its endpoint by the other endpoint also negates adjacency, by the assumed complementarity. Loops remain absent. These cases verify adjacency in both directions, so σ is an actual graph isomorphism fixing every outside vertex. Therefore, for every original edge xy in the stated degree class, ISS(G,{x,y}) holds if and only if every outside vertex sees exactly one endpoint. The transposition certificate itself only requires distinct endpoints and outside complementarity.")),
            // GV-CDEF
            Paragraph(Text(
                "Application GV-CDEF — the full arbitrary-base construction. Let I be any finite set of size m≥2 and let F be any simple graph on I, including graphs with isolated vertices. Form C(F) on the disjoint union {v} ⊔ {a_i:i∈I} ⊔ {b_i:i∈I}. Equivalently its carrier is Option(Bool×I), with v=none, a_i=some(false,i), b_i=some(true,i); its order is 2m+1. The apex v is adjacent to every a_i and to no b_i. Within either layer, adjacency is F.Adj(i,j). Across layers, a_i is adjacent to b_j if and only if not F.Adj(i,j). Since F has no loops, this last rule includes every matched edge a_i b_i, and is equivalently i=j or (i≠j and not F.Adj(i,j)). These rules, together with symmetry, specify every vertex pair. They give a simple graph without any connectivity, regularity or isolate-free assumption on F.")),
            // GV-C
            Paragraph(Text(
                "Application GV-C — apex switch and coverage. Define τ(v)=v, τ(a_i)=b_i and τ(b_i)=a_i for every i. It is an involution. Switching at v exchanges the v–A and v–B adjacencies, exactly as τ does. Pairs within a layer map to the other copy of F, and cross pairs keep the same negated F relation by symmetry. Thus τ is an actual isomorphism C(F)^{v} → C(F). For every i, the endpoints a_i,b_i form an original edge. The apex sees exactly a_i. At a_k with k≠i the incidences with a_i and b_i are F.Adj(k,i) and its negation; at b_k with k≠i they are its negation and F.Adj(k,i). Thus every outside vertex sees exactly one endpoint. The transposition of a_i,b_i is an actual pair-switch isomorphism fixing every outside vertex. The apex singleton and all matched pairs cover every vertex of C(F), for every base F.")),
            // GV-C
            Paragraph(Text(
                "Application GV-C — all three degrees. The apex has precisely the m vertices a_i as neighbors, so d(v)=m. For each i and each base index j, exactly one of a_j,b_j is adjacent to a_i: choose a_j when F.Adj(i,j), and b_j otherwise. The remaining neighbor is v, so d(a_i)=m+1. Similarly exactly one copy of each j is adjacent to b_i: choose b_j when F.Adj(i,j), and a_j otherwise; b_i has no apex neighbor, so d(b_i)=m. Forgetting the layer label gives the inverse to each displayed neighbor parametrization. In particular the diagonal choice j=i is the other-layer matched vertex, not a loop. These bijections prove the degrees also for mixed-isolate and entirely isolated bases.")),
            // GV-C
            Paragraph(Text(
                "Application GV-C — every singleton, with both directions. The complete singleton set is W(C(F))={v}∪{b_i : i is isolated in F}. To prove necessity, a singleton switch must have degree m, by the balance at order 2m+1, so no a_i qualifies. If b_i qualifies, its neighborhood must be the upper level A by GV-2D. A base neighbor j of i would instead give the lower-level neighbor b_j of b_i, a contradiction. Hence i has no base neighbors, which in a finite graph is equivalent to d_F(i)=0. For sufficiency, the apex switch τ is already available. If i is isolated, both v and b_i have open neighborhood exactly A and are nonadjacent. Their transposition is an automorphism of C(F): all incidences with an outside vertex agree, and their mutual nonedge stays a nonedge. Singleton transport under this automorphism carries the switch at v to a switch at b_i. This accounts for every vertex and includes every isolate.")),
            // GV-C
            Paragraph(Text(
                "Application GV-C — exhaustive candidate types for the partner graph. Since every partner edge has degree sum |V(C(F))|=2m+1, the degree formulas exclude pairs of two a-layer vertices and pairs of two vertices in {v}∪B. The only remaining possible unordered types are a_i b_j and v a_i. This is only a restriction of candidates: each candidate must still be an original edge and must satisfy the full outside-complementarity criterion. We now check both directions for each remaining type.")),
            // GV-C
            Paragraph(Text(
                "Application GV-C — all cross-layer partners, necessity including boundary coordinates. For an original cross edge a_i b_j we have not F.Adj(i,j). If it is a partner edge, apply outside complementarity at a_k for each k≠i. Its adjacencies to a_i and b_j are F.Adj(k,i) and not F.Adj(k,j), so complementarity says F.Adj(k,i) if and only if F.Adj(k,j). At k=i the same equality holds because F.Adj(i,i) is false and the original cross edge gives not F.Adj(i,j). Thus the complete open adjacency rows at i and j agree: N_F(i)=N_F(j). When j≠i the comparison k=j was an allowed outside vertex a_j and is included; the omitted endpoint coordinate k=i has been checked separately. This does not silently drop the diagonal or either boundary coordinate.")),
            // GV-C
            Paragraph(Text(
                "Application GV-C — all cross-layer partners, sufficiency including original adjacency. Suppose N_F(i)=N_F(j). Evaluating this row equality at j and using looplessness gives not F.Adj(i,j), so a_i b_j really is an original edge. The apex sees a_i alone. At any outside a_k, row equality makes F.Adj(k,i) and not F.Adj(k,j) opposite truth values. At any outside b_k, it makes not F.Adj(k,i) and F.Adj(k,j) opposite truth values. This covers k=j in the a-layer and k=i in the b-layer when the indices differ, and also covers the case i=j. The criterion therefore gives an actual pair-switch isomorphism, namely the transposition of a_i and b_j fixing all outsiders. Hence a_i b_j is a partner edge if and only if N_F(i)=N_F(j), including every matched pair.")),
            // GV-C
            Paragraph(Text(
                "Application GV-C — all apex partners, both directions. Every v a_i is an original edge. If i is isolated in F, then for every outside a_k, v is adjacent and a_i is not; for every b_k, v is nonadjacent and a_i is adjacent. Thus outside complementarity holds, including b_i, and transposing v and a_i certifies the pair switch. If i has a base neighbor j, then j≠i and a_j is adjacent to both v and a_i. Switching {v,a_i} removes both incidences at a_j, changing its degree from m+1 to m−1. No original vertex has that degree, so no switch isomorphism can exist. Thus v a_i is a partner edge if and only if i is isolated.")),
            // GV-C
            Paragraph(Text(
                "Application GV-C — the complete partner graph and both essential-set branches. Combining the exhaustive types with the two equivalences gives E(P(C(F)))={ {a_i,b_j}:N_F(i)=N_F(j) } ∪ { {v,a_i}:i is isolated in F }. In ordered adjacency form these are exactly four cases: (a_i,b_j), (b_j,a_i) with equal open base neighborhoods, and (v,a_i), (a_i,v) with i isolated. There are no other partner edges. Each a_i and b_i always has its matched partner, so neither layer contributes to U. The apex has a partner exactly when some base vertex is isolated. Consequently U(C(F))=∅ if F has at least one isolated vertex, and U(C(F))={v} if F has none. Both conclusions include arbitrary mixtures of isolated and nonisolated vertices; the first also includes entirely isolated bases.")),
            // GV-CF
            Paragraph(Text(
                "Application GV-CF — isolate-free fixing for every switch. Suppose now that every i∈I has some j with F.Adj(i,j). The singleton classification gives W(C(F))={v}, and the essential-set classification gives U(C(F))={v}. For any actual p:C(F)^{v} → C(F), singleton transport puts p(v) in this unique singleton set, hence p(v)=v. This quantifies over every switching isomorphism, not only τ. The isolate-free condition is used here for these conclusions; it was not imposed on the construction, coverage, degree formulas or complete switch classifications.")),
            // GV-CF
            Paragraph(Text(
                "Application GV-CF — actual neighborhood recovery. For every base F, the map r_F:i↦a_i is a bijection from I to N_{C(F)}(v), with inverse a_i↦i. The induced adjacency between a_i and a_j is exactly F.Adj(i,j). Thus r_F is an actual graph isomorphism F → C(F)[N(v)], with no finiteness or isolate-free assumption required for this map. Recovery retains the base relation on all vertex pairs.")),
            // GV-CF
            Paragraph(Text(
                "Application GV-CF — lifting every supplied base isomorphism. For any graphs F on I and F′ on J and every actual isomorphism f:F → F′, define L_f(v)=v′, L_f(a_i)=a′_{f(i)} and L_f(b_i)=b′_{f(i)}. Its inverse is L_{f⁻¹}. Apex incidences are preserved by the layer tags. Within each layer, adjacency is preserved by f; across layers, the negation of adjacency is preserved by the same equivalence. Hence L_f:C(F) → C(F′) is an actual graph isomorphism. In particular isomorphic bases always give isomorphic constructed graphs.")),
            // GV-CF
            Paragraph(Text(
                "Application GV-CF — recovering from every supplied constructed-graph isomorphism. Let F be any base and let F′ be finite and isolate-free. Given any actual g:C(F) → C(F′), the apex v is a singleton-ISS vertex, so singleton transport sends g(v) into W(C(F′))={v′}. Thus g(v)=v′. For each x, adjacency to v is equivalent under g to adjacency of g(x) to v′; g therefore restricts to a bijection g_N:N(v) → N(v′), with inverse the restriction of g⁻¹, and preserves the induced adjacency in both directions. The composition r_{F′}⁻¹ ∘ g_N ∘ r_F is an actual isomorphism F → F′. In particular this applies to every pair of finite isolate-free bases, even on differently named carriers, and every isomorphism between their constructions. Nonisomorphic such bases consequently give nonisomorphic constructions.")),
            // GV-CF
            Paragraph(Text(
                "Application GV-CF — exact quotient domains and well-defined embedding. Fix a finite carrier I of size m≥2. Let B_I consist of all isolate-free simple graphs on I, and let T_I consist of all covered simple graphs on Option(Bool×I) whose essential set is {u} for some vertex u. In each collection, identify two graphs exactly when an actual graph isomorphism exists; identity, inverse and composition make this an equivalence relation. The construction sends every F∈B_I to an element C(F)∈T_I by coverage and U(C(F))={v}. Define Φ([F])=[C(F)]. If representatives F,H are isomorphic, L_f supplies an isomorphism C(F)→C(H), so Φ is well defined. If Φ([F])=Φ([H]), quotient equality supplies an actual isomorphism between the constructed graphs; the preceding recovery gives an actual F→H isomorphism, so [F]=[H]. Thus Φ is an injection of these isomorphism-class sets. The target includes all covered graphs of this carrier with one essential vertex; this does not assert that every such graph is a construction.")),
            // GV-CF
            Paragraph(Text(
                "Application GV-CF — the complete counting consequence. There are finitely many simple graphs on a fixed finite carrier, so B_I,T_I and both isomorphism quotients are finite. The injection Φ therefore gives |B_I/≅|≤|T_I/≅|. For I=Fin m and every m≥2, let a_m be the number of isomorphism classes of isolate-free m-vertex simple graphs. Since the target carrier has 2m+1 vertices, there are at least a_m isomorphism classes of covered graphs of order 2m+1 having one essential vertex. This lower bound counts actual graph-isomorphism classes and follows from the well-defined embedding, rather than from labelled counts or degree data.")),
            // GV-INF
            Paragraph(Text(
                "Application GV-INF — the entire infinite family and the house. For every m≥2 take the complete base F=K_m. Every i has a different j and hence a base neighbor, so C(K_m) is covered, has order 2m+1, has U=W={v}, and every actual apex-switch isomorphism fixes v. Thus examples occur at every odd order at least five. If C(K_m) and C(K_n) were isomorphic, their vertex bijection would give 2m+1=2n+1 and hence m=n; different parameters give nonisomorphic graphs. At m=2 the layer vertices form the four-cycle a_0,a_1,b_1,b_0,a_0 and the apex is joined precisely to a_0,a_1, giving the house. This specialization illustrates the full family rather than replacing its arbitrary-base statement.")),
            // GV-INF
            Paragraph(Text(
                "Application GV-INF — why the degree-sum test is insufficient in every isolate-free base. For every i, the original edge v a_i has degree sum m+(m+1)=2m+1 and passes the necessary partner test. Choose an actual base neighbor j of i, which exists by isolate-freeness. The outside vertex a_j is a common neighbor of v,a_i, and after switching that pair has degree m−1 rather than m+1. All original degrees are m or m+1, so this rejects ISS(C(F),{v,a_i}) for every i. Together with the exhaustive candidate types, it explains the apex's essentiality by actual degree changes after each candidate switch.")),
            // GV-RESIDUAL
            Paragraph(Text(
                "Applicability limits. The transport statements, exact balances, two-degree result and complete arbitrary-base construction do not settle fixing for unrestricted covered graphs, including arbitrary covered graphs with |U|=1. Existence and structure questions for larger essential sets, possible induced graphs G[U], and a complete classification of covered graphs remain open. No finite catalogue or permutation search is used as a proof of the universal statements above."))), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("seidel-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Qualified(string name)
    {
        var parts = name.Split('.');
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq([.. tokens]);
    }
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Qualified(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Qualified(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instances(Formula body, params Formula[] types)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var type in types) tokens.Add(Seq(OpenBracket, type, CloseBracket, Sp));
        tokens.Add(body);
        return Seq([.. tokens]);
    }
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Singleton(Formula x) => Seq(OpenBrace, x, CloseBrace);
    private static Formula V() => F.Id("V");
    private static Formula G() => F.Id("G");
    private static Formula Graph() => Call("SimpleGraph", V());
    private static Formula GraphBinders(Formula body) => All("V", F.Id("Type"), All("G", Graph(), body));
    private static Formula SwitchFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), s = F.Id("S");
        Formula adjacency = And(Rel(x, FormulaRelationOperator.NotEqual, y),
            Iff(Call("SimpleGraph.Adj", G(), x, y), Iff(Member(x, s), Member(y, s))));
        return GraphBinders(All("S", Call("Set", V()), All("x", V(), All("y", V(),
            Iff(Call("SimpleGraph.Adj", Call("seidelSwitch", G(), s), x, y), adjacency)))));
    }
    private static Formula VertexFormula()
    {
        Formula x = F.Id("x");
        Formula iso = Call("SimpleGraph.Iso", Call("seidelSwitch", G(), Singleton(x)), G());
        return GraphBinders(All("x", V(), Iff(Call("IsVertexISS", G(), x), Call("Nonempty", iso))));
    }
    private static Formula ClaimFormula()
    {
        Formula body = Iff(All("x", V(), Call("IsVertexISS", G(), F.Id("x"))),
            Equal(Call("Fintype.card", V()), D(1)));
        Formula quantified = All("V", F.Id("Type"), Instances(All("G", Graph(), body),
            Call("Fintype", V()), Call("DecidableEq", V()), Call("Nonempty", V())));
        return Iff(Call("claim"), quantified);
    }
}
