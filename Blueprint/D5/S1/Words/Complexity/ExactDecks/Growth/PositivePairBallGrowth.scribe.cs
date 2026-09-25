using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.Growth;

internal sealed class ExactDecksGrowthPositivePairBallGrowthDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ExactDecks/Growth/PositivePairBallGrowth";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual positive-word cutoff balls have weighted Lyndon polynomial growth.",
        H("PositivePairBallGrowth"),
        Blocks(
            Paragraph(Text(
                "The exponent uses the cardinalities of actual Lyndon-word subtypes at every "
                + "degree. The proof combines a complete degree-one letter box with the "
                + "multi-scale central digits at higher degrees, always using images of actual "
                + "positive words rather than an abstract free-coordinate family.")),
            D("actual-positive-word-ball-lower-bound", "actual_positiveWordBall_weightedLyndon_lower_bound", "All-radius weighted-Lyndon lower growth",
                "For every finite linearly ordered A with 2<=Fintype.card A and every r with 1<=r, there are naturals C,N with 0<C such that for every n>=N, n^(weightedLyndonExponent A r) <= C*(positiveWordBall A r n).card."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
