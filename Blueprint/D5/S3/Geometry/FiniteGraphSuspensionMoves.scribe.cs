using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteGraphSuspensionMovesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGraphSuspensionMoves.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite chains of suspension moves", H("Finite chains of suspension moves"), Blocks(
            Node("n0", "MoveChain", "Literal operation chains",
                "A chain is built from identity, triple-subdivision, matching and Lozin constructors. Every constructor contains its chosen vertices, adjacency or neighborhood-partition proofs, and an actual relabeling equivalence.", DescribeRole.Definition),
            Node("n1", "reducedHomologyIso", "The iterated shift",
                "A chain of n moves from G to F gives reduced integral singular homology of the actual F-independence realization in degree q+n isomorphic to that of G in degree q, for q at least one."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole? role = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
