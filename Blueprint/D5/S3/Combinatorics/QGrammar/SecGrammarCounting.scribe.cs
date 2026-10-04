using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.QGrammar;

internal sealed class SecGrammarCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/QGrammar/SecGrammarCounting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2026qgrammar");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting the finite support region gives the cubic formula in Conjecture III.7.",
        H("Counting the Sec Grammar Region"),
        Blocks(
            Node("sec-grammar-counting-region-count", "Region cardinality", "region_count",
                "For every positive natural n, the cardinality of region n equals omegaFormula n. The small steps are evaluated directly, and the odd and even ranges reduce to the two cubic expressions.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
