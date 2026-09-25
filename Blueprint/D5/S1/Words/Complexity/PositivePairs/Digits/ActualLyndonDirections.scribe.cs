using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Digits;

internal sealed class PositivePairsDigitsActualLyndonDirectionsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Lyndon words index independent directions in the full positive-pair family.",
        H("ActualLyndonDirections"),
        Blocks(
            Paragraph(Text(
                "For each length r, ActualLyndonWord is the subtype of actual words of length r "
                + "that satisfy IsLyndon. The module publicly installs a lifted linear order on "
                + "this subtype and, for finite A, a Fintype instance obtained by injection into "
                + "length-r vectors. These two anonymous public instances support the cardinality "
                + "and deterministic selection below; the digit construction itself is a "
                + "repository result, not a claim attributed to the cited paper.")),
            D("actual-lyndon-word", "ActualLyndonWord", "Actual Lyndon words of a fixed length",
                "For linearly ordered A and r:N, ActualLyndonWord A r is the subtype of lists w with w.length=r and IsLyndon w.", DescribeRole.Definition),
            D("actual-lyndon-count", "actualLyndonCount", "The actual Lyndon-word count",
                "For finite linearly ordered A, actualLyndonCount A r is Fintype.card (ActualLyndonWord A r), not an independent proxy parameter.", DescribeRole.Definition),
            D("selected-direction", "selectedDirection", "Selected independent actual directions",
                "For each r, selectedDirection chooses one PositivePairIndex A r for every element of Fin(actualLyndonCount A r), with the resulting actualLeadingDifference family linearly independent over Q.", DescribeRole.Definition))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
