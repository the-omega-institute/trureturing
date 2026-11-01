using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteGraphSubgraphSuspensionRetractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The variable neighborhood retraction and old-coordinate intersection bridge.",
        H("Neighborhood retraction and intersection"),
        Blocks(
            Node("coordinates-neighborhoodretraction", "neighborhoodRetraction", "A variable-cutoff neighborhood retraction",
                "On O, apply the variable cutoff delta(x) to every coordinate and normalize. The coordinate sum exceeds three quarters, all support shrinks, and a minimizing b_M has its forbidden coordinates killed. The resulting continuous map lands in B. It fixes B pointwise because delta=0 there.", DescribeRole.Definition),
            Node("coordinates-neighborhoodequiv", "neighborhoodEquiv", "The actual neighborhood equivalence",
                "The variable-cutoff retraction and the inclusion of B in O are homotopy inverse. Straight interpolation is supported in the original independent face and stays in O by the b_M bound. The other composite is exactly the identity on B.", DescribeRole.Definition),
            Node("coordinates-contractible-o", "contractible_O", "Contractibility of the second open set",
                "The constructed equivalence with the actual contractible apex star cluster makes O contractible. No homological vanishing assumption is supplied.", DescribeRole.Theorem),
            Node("coordinates-intersectionequiv", "intersectionEquiv", "The actual open intersection",
                "For every H less than or equal to G, the old epsilon cutoff and normalization map U intersect O to the actual old independence realization. Its denominator exceeds one quarter. Edges of H are excluded by a maximal independent set; edges retained from G minus H are excluded by the original gadget support. Inclusion on old coordinates is the inverse up to the two displayed straight homotopies.", DescribeRole.Definition)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
