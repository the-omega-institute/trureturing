using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Span;

internal sealed class PositivePairsSpanFullFamilyBracketSpanDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyBracketSpan";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual full-family differences span every rational Lyndon standard bracket.",
        H("FullFamilyBracketSpan"),
        Blocks(
            Paragraph(Text(
                "The classical Lyndon bracket basis motivates the target directions. The new "
                + "content here is realizability by the complete family of actual recursively "
                + "generated positive-word pairs, without quotienting duplicate indices.")),
            D("every-standard-bracket-mem", "every_standardBracket_mem", "Every standard bracket is realized in the span",
                "For finite linearly ordered A and every word w, the rational coefficient extension of standardBracket w belongs to fullFamilySpan A w.length. The induction uses the actual successor commutator and does not assume an abstract free parameter family."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
