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
                "The infiltration product and its top-degree shuffle stratum are classical and "
                + "are also used in the cited source. The list-valued definitions retain one "
                + "entry per alignment, so coincident output words remain repeated. The final "
                + "unconditional recovery theorem is the repository bridge used by the exact "
                + "asymptotic upper injection.")),
            D("lyndon-coordinate-recovery", "scatteredCount_eq_of_lyndon_coordinates", "Actual Lyndon coordinates recover every bounded count",
                "For finite linearly ordered A and arbitrary k,left,right, if every actual Lyndon word of length at most k has equal scattered count in left and right, then every word of length at most k has equal scattered count. No common-length premise, exact-deck premise, or guarded recovery hypothesis is required."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
