using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class PositivePairBallGrowthDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairBallGrowth";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual positive words realize the full weighted-Lyndon polynomial lower growth of every positive cutoff-Magnus ball.",
        H("Growth of Actual Positive-Word Balls"),
        Blocks(
            Paragraph(Text(
                "The exponent uses the cardinalities of actual Lyndon-word subtypes at every "
                + "degree. The proof combines a complete degree-one letter box with the "
                + "multi-scale central digits at higher degrees, always using images of actual "
                + "positive words rather than an abstract free-coordinate family.")),
            D("positive-word-ball", "positiveWordBall", "The actual cutoff-Magnus ball",
                "For finite A, positiveWordBall A r n is the finite image of cutoffMagnus r on all actual lists over A whose length is at most n.", DescribeRole.Definition),
            D("weighted-lyndon-exponent", "weightedLyndonExponent", "Weighted actual Lyndon exponent",
                "For finite linearly ordered A, weightedLyndonExponent A r is sum over i in range(r+1) of i*actualLyndonCount A i; the degree-zero term is present syntactically and vanishes.", DescribeRole.Definition),
            D("actual-positive-word-ball-lower-bound", "actual_positiveWordBall_weightedLyndon_lower_bound", "All-radius weighted-Lyndon lower growth",
                "For every finite linearly ordered A with 2<=Fintype.card A and every r with 1<=r, there are naturals C,N with 0<C such that for every n>=N, n^(weightedLyndonExponent A r) <= C*(positiveWordBall A r n).card.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Words/Complexity/PositivePairCentralDigits"))]));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
