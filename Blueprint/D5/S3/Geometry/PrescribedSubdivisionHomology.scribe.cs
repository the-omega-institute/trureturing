using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class PrescribedSubdivisionHomologyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/PrescribedSubdivisionHomology.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous prescribed triple subdivisions", H("Simultaneous prescribed triple subdivisions"), Blocks(
            Node("n0", "baseGraph", "The complete endpoint graph",
                "Every supplied unordered endpoint pair is an edge of the base graph. All original vertices, including isolated vertices, are retained."),
            Node("n1", "tip_adjacent", "The current terminal edge",
                "A partial path with multiplicity zero retains the original edge; a positive path has its terminal internal vertex adjacent to the original right endpoint."),
            Node("n2", "stepIso", "One actual subdivision step",
                "Increasing one multiplicity by one identifies the new partial graph with a literal triple subdivision of its current terminal edge. Injectivity of unordered endpoint pairs handles the zero-stage edge deletion."),
            Node("n3", "positiveIso", "The final path carrier",
                "At the prescribed positive multiplicities, the partial graph is isomorphic to the actual prescribed-subdivision graph on original vertices and indexed internal path vertices."),
            Node("n4", "reducedHomologyIsoOfAdjacency", "The total homology shift",
                "For finite original vertex and edge types, injective unordered endpoint pairs, an exact endpoint adjacency inventory for G and q at least one, the actual prescribed graph has reduced integral singular homology in degree q plus the sum of multiplicities isomorphic to that of G in degree q. Well-founded recursion on the total multiplicity proves the iteration without a nested expanded carrier."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole? role = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
