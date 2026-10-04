using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.QGrammar;

internal sealed class SecGrammarWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/QGrammar/SecGrammarWords.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/han2026qgrammar");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Support words have two canonical blocks, and every such word is represented by one admissible tuple.",
        H("Canonical Sec Grammar Words"),
        Blocks(
            Node("sec-grammar-words-encode", "Canonical word encoding", "encode",
                "For a family tag, index j, and natural multiplicities a and b, encode forms a block of x at j plus one, x at j, and one y at j, or a block of x at j, one y at j, and x at j minus one.", DescribeRole.Definition),
            Node("sec-grammar-words-normal-form", "Unique word normal form", "normal_form",
                "A DIO-sorted word with one y at index j, width at most one, and the stated boundary condition has a unique family and pair of multiplicities whose encoding is that word.", DescribeRole.Theorem),
            Node("sec-grammar-words-invariants", "Support word invariants", "word_invariants",
                "Every word in the support after n derivative steps is DIO-sorted, contains exactly one y, has index width at most one, and after a positive number of steps a y at index zero is accompanied by an x at index one.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
