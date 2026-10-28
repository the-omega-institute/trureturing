using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteGraphVertexSubstitutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGraphVertexSubstitution.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual singleton-fiber substitution decomposition in finite coordinates.",
        H("Single-vertex graph substitution"),
        Blocks(
            Node("mapped-coordinates", "mapped_coordinates", "Recovery of embedded coordinates",
                "For all finite source and target vertex types U and X, every pre-abstract complex K on U, every vertex embedding f from U to X, and every point y in the coordinate realization of K mapped by f, the function sending z to the sum over u of y(f(u)) when f(u)=z, and zero otherwise, equals y. A mapped face contains no ambient vertex outside the embedding image, so all such coordinates vanish. Injectivity reduces every image coordinate to its unique source coordinate.", DescribeRole.Theorem),
            Node("embedding-homeomorphism", "mapHomeomorph", "Native realization transport along an embedding",
                "For all finite vertex types U and X, every pre-abstract complex K on U, and every embedding f from U to X, the native finite-coordinate realization of K is homeomorphic to that of K mapped by f. The forward map sums coordinates over the preimage of each vertex; the inverse restricts the coordinates at f(u). Nonnegativity, the coordinate sum one, and support in a mapped face prove membership. Both maps are continuous finite-coordinate maps. Unused ambient vertices are allowed.", DescribeRole.Definition),
            Node("independence-complex", "independenceComplex", "The actual independence complex",
                "For every simple graph, the faces are exactly its nonempty finite independent vertex sets. Every singleton is present, as required by Mathlib's abstract simplicial complex convention. An unoccupied fiber contributes an empty selected set, rather than a required nonempty face.", DescribeRole.Definition),
            Node("sigma-substitution", "substitution", "Heterogeneous graph substitution",
                "For a base graph G and a graph H(u) on each current fiber D(u), the vertices are the dependent pairs (u,d). Adjacency holds over a base edge, or within one fiber according to H(u). Fibers may be empty.", DescribeRole.Definition),
            Node("tail", "Tail", "The current vertices away from v",
                "The tail is the dependent sum of D(u) over all base vertices unequal to v. It keeps every current fiber without changing its graph.", DescribeRole.Definition),
            Node("link-base", "LinkBaseSet", "The restricted base for the link",
                "The link base consists of all u unequal to v for which G has no edge from v to u. This is the complement of the closed neighborhood in the current base graph.", DescribeRole.Definition),
            Node("link-vertices", "LinkVerts", "The current-fiber link vertices",
                "The link vertices are the dependent sum of the original current fibers D(u) over the restricted link base. Any earlier fiber replacements remain present on this restriction.", DescribeRole.Definition),
            Node("link-complex", "linkComplex", "The restricted substitution independence complex",
                "Restrict G to the link base, retain H(u) on D(u), form their heterogeneous substitution, and take its actual independence complex. The resulting pre-abstract complex may have no faces.", DescribeRole.Definition),
            Node("new-fiber", "newFiber", "The replacement sigma family",
                "For a distinguished base vertex v and a finite new vertex type W, the new family has W at v and the old D(u) at every other u. The construction includes the dependent casts between these branch types.", DescribeRole.Definition),
            Node("finite-new-fiber", "newFiberFintype", "Finiteness of the replacement fibers",
                "The replacement fibers are finite because W and every current D(u) are finite.", DescribeRole.Definition),
            Node("decidable-new-fiber", "newFiberDecidableEq", "Decidable equality on replacement fibers",
                "Decidable equality on W and each D(u) supplies decidable equality on each branch of the replacement family.", DescribeRole.Definition),
            Node("new-graphs", "newGraphs", "The actual graphs on the replacement family",
                "Use the new graph on W at v and H(u) at every other vertex, transported across the defining branch equalities of the new family.", DescribeRole.Definition),
            Node("old-point", "oldPoint", "The old distinguished coordinate point",
                "For every current substitution and chosen d0 in D(v), the old point is the coordinate singleton (v,d0) in its independence realization.", DescribeRole.Definition),
            Node("join-point", "joinPoint", "The pure-right singleton",
                "For every l0 in W, the point of the simplicial join is its pure-right coordinate singleton l0. It exists even if the restricted link complex has no faces. No ordinary topological join or point of the link realization is used.", DescribeRole.Definition),
            Node("replacement-equivalence", "oneVertexReplacementEquiv", "The actual quotient-wedge decomposition",
                "Let V and all current fibers D(u) be finite, let G be a simple base graph and H(u) a simple graph on D(u), choose v and d0 in D(v), and suppose every d in D(v) equals d0. For every finite graph Hnew on W and l0 in W, the coordinate independence realization of the actual new sigma substitution is homotopy equivalent to the actual quotient wedge of the old independence realization at (v,d0) and the realization of the simplicial join of the current restricted link complex with the independence complex of Hnew, based at the pure-right singleton l0. No other fiber or link nonemptiness is assumed. On the common carrier Tail plus W, A is embedded deletion union the join with the pre-complex whose sole face is the singleton l0; B is the embedded full simplicial join, and their exact intersection is that singleton-apex cone. The cone remains nonempty when the link has no faces. The cone-union equivalence is followed by an actual quotient homeomorphism induced by two apex-preserving homeomorphisms of the summands. The singleton old-fiber hypothesis rules out a residual old fiber at v. This all-finite-case coordinate decomposition is a local realization refinement for the lexicographic-product setting of Carnero Bravo arXiv:2505.06457v2, not a theorem attributed to that paper. Theorem 21 there concerns suspended independence complexes; Question 22 asks for unsuspended hereditary membership in the class W. The present bridge asserts neither that question's resolution nor a novelty claim. An ordinary-join interpretation requires both factor realizations to be nonempty and is outside this statement.", DescribeRole.Definition),
            Node("graph-iso-realization", "graphIsoHomeomorph", "Graph isomorphism transport",
                "For every isomorphism of finite simple graphs, transport the actual independence realization by the vertex equivalence. The exact equality of mapped independent faces reuses the original restricted-map proof; the coordinate embedding homeomorphism then gives the actual homeomorphism, including empty graphs.", DescribeRole.Definition),
            Node("fiber-iso", "substitutionFiberIso", "Fiberwise substitution transport",
                "For a fixed base graph and a graph isomorphism on every fiber, the dependent-sum equivalence preserves and reflects substitution adjacency and keeps the base coordinate. This is consumed in the actual mixed-stage identifications.", DescribeRole.Definition),
            Node("nested-induce", "nestedInduceIso", "Nested induced graph reindexing",
                "For a subset B of the base and a subset S of B, send a nested subtype vertex to its underlying base vertex in the image of S under subtype projection. This explicit bijection identifies the twice-induced graph with the original graph induced on that image, and transports the hereditary base hypothesis in the smaller-link induction.", DescribeRole.Definition),
            Node("singleton-stage", "singletonSubstitutionIso", "Singleton fibers recover the base",
                "Substitution of an edge-free singleton at every base vertex is isomorphic to the base graph by projection, with inverse adjoining the unique singleton element. Empty and singleton base graphs are included.", DescribeRole.Definition),
            Node("empty-link-unit", "emptyLeftJoinHomeomorph", "The augmented empty-left simplicial unit",
                "If M has no faces, every surviving face of its simplicial join with N is purely right. Thus the join is exactly N mapped by the right vertex embedding, and their actual realizations are homeomorphic. No identification with the ordinary join of an empty space is asserted.", DescribeRole.Definition),
            Node("stage-fiber", "stageFiber", "The actual mixed replacement family",
                "At a vertex in the replaced finset use its final fiber D(v); elsewhere use PUnit in the same fiber universe. This family retains all previously replaced fibers on every restricted current link.", DescribeRole.Definition),
            Node("stage-finite", "stageFiberFintype", "Finiteness of the mixed fibers",
                "Each mixed fiber is finite by its selected finite final-fiber or singleton branch.", DescribeRole.Definition),
            Node("stage-decidable", "stageFiberDecidableEq", "Decidable equality of the mixed fibers",
                "Branch reduction transfers decidable equality from each final fiber or from the singleton.", DescribeRole.Definition),
            Node("stage-nonempty", "stageFiberNonempty", "Nonempty mixed fibers",
                "If every final fiber is nonempty, both branches of every mixed fiber are nonempty. This supplies actual current-link vertices when the restricted base is nonempty.", DescribeRole.Definition),
            Node("stage-graphs", "stageGraphs", "Graphs on the mixed family",
                "Transport H(v) across the selected branch equality, and transport the edge-free singleton graph across the other branch equality. These are graphs on the actual dependent stage types.", DescribeRole.Definition),
            Node("initial-stage", "initialStageIso", "The initial stage is the base graph",
                "The stage with no replaced vertices is isomorphic to the base graph, by fiberwise singleton transport and projection. This starts replacement induction without an order-two assumption.", DescribeRole.Definition),
            Node("final-stage", "finalStageIso", "The final stage is full substitution",
                "The stage indexed by the full base finset is isomorphic to the full original heterogeneous substitution, by the explicit selected-fiber equivalences.", DescribeRole.Definition),
            Node("replacement-stage", "replacementStageIso", "A supplier replacement is the next mixed stage",
                "Pointwise branch casts identify the supplier newFiber construction at v with the stage indexed by insert v R, preserving actual fiber adjacency. When v is absent from R, the old stage fiber at v is a singleton; no singleton assumption is made on the new final fiber. These transports serve the private strong induction on base cardinality and inner induction on replaced vertices. Its homotopy-class inputs are explicit point, nonempty ordinary-join, coordinate-vertex quotient-wedge and homotopy-invariance closure assumptions, not discharged properties of the source class W. The link carries all current mixed fibers. A nonempty link uses the smaller-base induction, and an empty link uses the augmented simplicial unit. Full Question 22 still requires the actual accepted topology closures and both source-model normalization directions.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
