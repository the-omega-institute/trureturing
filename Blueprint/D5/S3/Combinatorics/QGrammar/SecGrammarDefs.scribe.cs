using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.QGrammar;

internal sealed class SecGrammarDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/QGrammar/SecGrammarDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/han2026qgrammar");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Sec grammar supplies ordered words, a q-derivative, and the conjectured support count.",
        H("Sec Grammar Definitions"),
        Blocks(
            Node("sec-grammar-defs-var", "Grammar variables", "Var",
                "A grammar variable is a Boolean tag together with a natural index. The false tag denotes x at that index and the true tag denotes y.", DescribeRole.Definition),
            Node("sec-grammar-defs-diole", "DIO precedence", "dioLe",
                "The DIO precedence places larger indices first and places x before y when the indices agree.", DescribeRole.Definition),
            Node("sec-grammar-defs-decidable", "Decidable precedence", "instDecidableRelVarDioLe",
                "The DIO precedence has a decidable comparison for every pair of grammar variables.", DescribeRole.Definition),
            Node("sec-grammar-defs-dio", "DIO normalization", "dio",
                "DIO normalization sorts a finite word by the DIO precedence.", DescribeRole.Definition),
            Node("sec-grammar-defs-up", "Index raising", "up",
                "The up operation raises every index in a word by one and preserves each variable tag.", DescribeRole.Definition),
            Node("sec-grammar-defs-rule", "The Sec replacement rule", "rule",
                "The replacement of y at index j is the single word y at j followed by x at j plus one, weighted by q to the j. The replacement of x at j is the sum of the empty word and that same two letter word, with the same weight.", DescribeRole.Definition),
            Node("sec-grammar-defs-deriv-word", "Derivative of a word", "derivWord",
                "The derivative of a word sums, over each position, the replacement at that position followed by the raised suffix, then normalizes the resulting word by DIO.", DescribeRole.Definition),
            Node("sec-grammar-defs-deriv", "Linear q-derivative", "deriv",
                "The q-derivative of a formal sum of words is the coefficient weighted sum of the derivatives of its words.", DescribeRole.Definition),
            Node("sec-grammar-defs-omega-formula", "The conjectured support formula", "omegaFormula",
                "The function omegaFormula gives one at step one, three at step two, the stated cubic expression at odd steps at least three, and the stated cubic expression at even steps at least four.", DescribeRole.Definition),
            Node("sec-grammar-defs-claim", "The support-count conjecture", "claim",
                "For every positive natural step n, the support of the n-fold derivative of the single y at index zero has cardinality omegaFormula n.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
