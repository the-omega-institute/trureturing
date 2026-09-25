using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Span;

internal sealed class PositivePairsSpanLiteralPowerSubstitutionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal power substitution realizes actual positive pairs at controlled degree.",
        H("LiteralPowerSubstitution"),
        Blocks(
            Paragraph(Text(
                "The classical Lyndon bracket basis motivates the target directions. The new "
                + "content here is realizability by the complete family of actual recursively "
                + "generated positive-word pairs, without quotienting duplicate indices.")),
            D("literal-power-word", "literalPowerWord", "Literal letter-power substitution",
                "literalPowerWord m source replaces every letter of source by m consecutive copies of that same letter.", DescribeRole.Definition),
            D("literal-power-positive-pair", "literalPowerSubstitution_actual_positivePair", "Power substitution preserves lower data and scales the lead",
                "For finite A with decidable equality, m,r, and every actual pair index, powering both pair words multiplies each length by m, preserves equal positive lengths at levels r>=2 when m>0, preserves all scattered counts below r, and scales every degree-r count difference by m^r, including degenerate levels."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
