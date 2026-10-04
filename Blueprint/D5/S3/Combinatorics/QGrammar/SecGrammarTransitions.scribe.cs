using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.QGrammar;

internal sealed class SecGrammarTransitionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/QGrammar/SecGrammarTransitions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/han2026qgrammar");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every canonical family has the stated transition multiplicities under one derivative step.",
        H("Sec Grammar Transitions"),
        Blocks(
            Node("sec-grammar-transitions-transitions", "Canonical transition counts", "transitions",
                "For each family, index, and pair of multiplicities, the support branches produced by one derivative step are exactly the listed canonical states, with the stated boundary cases and multiplicities.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
