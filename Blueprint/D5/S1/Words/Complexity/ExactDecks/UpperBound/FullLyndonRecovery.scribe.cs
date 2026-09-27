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
            H(title), StatementSource.FromAuthor(Disp(Seq(Forall, Sp,
                F.Id("A"), Comma, F.Id("k"), Comma, F.Id("left"), Comma,
                F.Id("right"), Comma, Sp,
                Open, Forall, Sp, F.Id("v"), InMacro,
                Call("ActualLyndonWordsThrough", F.Id("A"), F.Id("k")), Comma,
                Equal(Call("scatteredCount", F.Id("v"), F.Id("left")),
                    Call("scatteredCount", F.Id("v"), F.Id("right"))), Close,
                Rightarrow, Forall, Sp, F.Id("w"), Comma,
                Call("length", F.Id("w")), Leq, Sp, F.Id("k"), Rightarrow,
                Equal(Call("scatteredCount", F.Id("w"), F.Id("left")),
                    Call("scatteredCount", F.Id("w"), F.Id("right")))))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
