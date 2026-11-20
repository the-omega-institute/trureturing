using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Cographs;

internal sealed class UniversalCliqueCographDistanceDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Combinatorics/SpectralGraph/Cographs/UniversalCliqueCographDistance.";
    private static readonly LibraryNoteRef Survey =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mannamandaltura2026cographdistance");
    private static readonly LibraryNoteRef WidthSource =
        LibraryNoteRef.Create("D5/L/Eigenstructure/mandalmanna2026distance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A native width-two cograph family attains the ordinary distance multiplicity bound at unbounded orders.",
        H("Distance multiplicity for a universal-clique family"),
        Blocks(
            Paragraph(Text("Open Problem 14.2(ii) has a characterization clause and an explicit infinite-family clause. "
                + "The results here give the explicit family and classify its parameters at the fixed shift s − 2. "
                + "The source question and its bound are in "), Ref(Survey.Value), Text(".")),
            Entry("Vertex", "Native vertex carrier",
                "For natural r, s and b the vertices are Fin r ⊕ ((Fin s ⊕ Fin s) ⊕ Fin b). "
                + "The four summands are the hub clique, the two bipartite parts and the isolates.",
                DescribeRole.Definition),
            Entry("graph", "Universal-clique join",
                "On Vertex(r,s,b), the graph is the join of K_r with the disjoint union of K_{s,s} "
                + "and b isolates. The join is the complement of the disjoint sum of the two complements.",
                DescribeRole.Definition),
            Entry("connected", "Connectedness",
                "For r > 0 the first hub is universal, so the native graph is connected."),
            Entry("distance", "Ordinary shortest-path distances",
                "For r > 0 and all vertices u and v, dist(u,v) is zero when u=v, one for an edge "
                + "and two for distinct nonadjacent vertices. A hub supplies the intermediate vertex."),
            Entry("induced_path_excluded", "Induced four-vertex path exclusion",
                "For all natural r, s and b the native graph has no induced P4. Nonedges at positions "
                + "0 and 2, and 1 and 3, exclude the hub vertices. A putative path cannot use an isolate. "
                + "Alternation across the two bipartite parts makes the endpoints adjacent."),
            Entry("two_chain_cover", "Two vicinal chains",
                "For every r, s and b put the right part in one chain and all other vertices in the other. "
                + "Vertices of a fixed independent part have the same open neighborhood. Isolates are "
                + "below all vertices and hubs are above all vertices for N(u) ⊆ N[v]."),
            Entry("incomparable_parts", "An opposite-part antichain",
                "For s ≥ 2 every left vertex and every right vertex are incomparable in both directions. "
                + "A second vertex in each part supplies the required neighborhood obstruction."),
            Entry("width", "Exact vicinal width",
                "For s ≥ 2 the minimum vicinal chain-cover size is two in the existing extended-natural "
                + "width. The exhibited cover gives the upper bound. The two incomparable vertices "
                + "must receive distinct chain labels."),
            Entry("distanceMatrix", "Real ordinary distance matrix",
                "The (u,v) entry is the real cast of SimpleGraph.dist on graph(r,s,b).",
                DescribeRole.Definition),
            Entry("shiftedDistance", "Fixed shifted distance matrix",
                "Subtract ((s : ℝ) − 2) times the identity from distanceMatrix(r,s,b).",
                DescribeRole.Definition),
            Entry("shiftedKernel", "Real shifted kernel",
                "Take the linear-map kernel of shiftedDistance(r,s,b) on real vertex functions. "
                + "This is the eigenspace at s − 2.",
                DescribeRole.Definition),
            Entry("shiftedKernel_finrank", "Exact multiplicity at s − 2",
                "For r > 0, s ≥ 2 and b > 0 the real kernel dimension is two if "
                + "b(r − 2(s − 1)) = s(s − 1) in the integers and one otherwise. "
                + "In particular r=1 always gives one. Row differences force constancy in the four cells. "
                + "Every kernel vector has coordinates (−((s+2b)/r)z, p, z−p, z) with "
                + "(rb−(s−1)(s+2b))z=0. The two parameters are recoverable from their left and isolate "
                + "coordinates, giving a linear equivalence with ℝ × ℝ in the zero-residual case "
                + "and with ℝ otherwise. The dimension counts the full eigenspace of the real "
                + "symmetric distance matrix."),
            Entry("parameter_iff_divisor", "Positive-divisor parameterization",
                "For s ≥ 2 and b > 0 the integer equality holds exactly when there is a positive "
                + "natural divisor d of s(s−1) such that r=2(s−1)+d and b=s(s−1)/d. "
                + "Positivity of s(s−1) forces the integer difference r−2(s−1) to be positive. "
                + "Its natural value gives the divisor, and exact division recovers b."),
            Entry("family", "An explicit extremal graph at each s ≥ 2",
                "Choose the divisor s−1, so r=3(s−1) and b=s. The graph has order 6s−3, "
                + "is connected and induced-P4-free, and has vicinal width two. The real shift "
                + "s−2 is distinct from −1 and −2, belongs to the ordinary distance spectrum, "
                + "and has real eigenspace dimension two."))));

    private static DocumentBlock Entry(string name, string title, string text,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("universal-clique-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Survey, WidthSource), Blocks(Paragraph(Text(text))), role);
}
