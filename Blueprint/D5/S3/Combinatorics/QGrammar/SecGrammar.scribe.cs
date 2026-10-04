using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.QGrammar;

internal sealed class SecGrammarDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/QGrammar/SecGrammar.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/han2026qgrammar");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The number of distinct terms in every positive iterate of the Sec q-derivative is the formula of Conjecture III.7.",
        H("Han, Ji and Xiong's Sec Grammar Conjecture"),
        Blocks(
            Node("sec-grammar-result", "Conjecture III.7 resolved", "result", "For every positive natural n, the support of the n-fold q-derivative of y at index zero has cardinality omegaFormula n. This proves Conjecture III.7 for the Sec grammar.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("han-ji-xiong-sec-grammar-support"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
