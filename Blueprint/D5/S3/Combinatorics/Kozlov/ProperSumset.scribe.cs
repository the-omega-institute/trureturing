using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class ProperSumsetDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/ProperSumset.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every repeated sum of actual proper f-vectors has a chained representative with the same number of summands and with exactly the same vector sum.",
        H("Chained representatives of the literal proper sumset"),
        Blocks(
            Node("proper-sumset-surjon", "proper_sumset_surjOn", "Unconditional surjectivity onto the proper sumset", DescribeRole.Theorem,
                "The surjectivity is the equal-shift case of the proper lex representative argument in Part II, Lemma 40 and the proof of Theorem 41. Choose actual downsets for the input tuple. At each degree take a position-first lex segment with the same total number of missing faces. The module shadow bound and nesting show that the shadow of the chosen missing layer fits into the next chosen layer. Complementing these families yields proper downsets because the missing totals at zero and one vanish. A nonempty missing layer in a later position forces a full earlier missing layer, which gives the strict chaining inequality. Each degree's total is preserved by the layer partition identity."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-proper-sumset-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
