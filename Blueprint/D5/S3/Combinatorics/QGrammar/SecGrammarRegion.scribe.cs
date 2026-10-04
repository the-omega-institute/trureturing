using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.QGrammar;

internal sealed class SecGrammarRegionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/QGrammar/SecGrammarRegion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/han2026qgrammar");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite region of canonical states is exactly the support of every positive derivative iterate.",
        H("The Sec Grammar Support Region"),
        Blocks(
            Node("sec-grammar-region-region", "The finite support region", "region",
                "For a natural step n, region n is the finite set of family tags, indices, and multiplicities satisfying the canonical inequalities and parity conditions for step n.", DescribeRole.Definition),
            Node("sec-grammar-region-reachable", "Reachability of the region", "reachable_region",
                "For every positive n, the support after n derivative steps is exactly the image under canonical encoding of region n.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
