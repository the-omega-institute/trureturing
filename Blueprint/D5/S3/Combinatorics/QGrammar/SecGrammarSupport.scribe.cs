using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.QGrammar;

internal sealed class SecGrammarSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/QGrammar/SecGrammarSupport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2026qgrammar");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive coefficients make support evolution exactly the collection of normalized positional branches.",
        H("Support Reduction for the Sec Derivative"),
        Blocks(
            Node("sec-grammar-support-reduction", "Support reduction and positivity", "support_reduction",
                "At every step all polynomial coefficients are nonnegative. A word belongs to the next support exactly when it is obtained by choosing a support word, a position, and a supported replacement, then applying the DIO normalization to the resulting concatenation.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
