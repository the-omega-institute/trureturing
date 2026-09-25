using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.UpperBound;

internal sealed class ExactDecksUpperBoundFullLyndonRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ExactDecks/UpperBound/FullLyndonRecovery";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All bounded scattered counts are recovered unconditionally from Lyndon coordinates.",
        H("FullLyndonRecovery"),
        Blocks(
            Paragraph(Text(
                "This module recovers every bounded scattered count from actual Lyndon "
                + "coordinates. Its minimal-counterexample argument factors the least bad word, "
                + "uses the infiltration identity to cancel shorter overlaps, and uses indexed "
                + "shuffle order to isolate its positive top-degree multiplicity. The result "
                + "supplies the recovery step in the exact-deck upper bound.")),
            D("lyndon-coordinate-recovery", "scatteredCount_eq_of_lyndon_coordinates", "Actual Lyndon coordinates recover every bounded count",
                "For finite linearly ordered A and arbitrary k,left,right, if every actual Lyndon word of length at most k has equal scattered count in left and right, then every word of length at most k has equal scattered count. No common-length premise, exact-deck premise, or guarded recovery hypothesis is required."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
