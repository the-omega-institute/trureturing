using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.Growth;

internal sealed class ExactDecksGrowthPositiveWordBallDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual central digits inject the preceding cutoff ball into the next degree.",
        H("PositiveWordBall"),
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
            D("positive-word-ball-card-step", "positiveWordBall_card_step", "One central-digit growth step",
                "For degree r>=2, if a radius n accommodates a radius-m representative from degree r-1 followed by the complete degree-r, t-scale central digit word, then the degree-r positive-word ball has at least the product of the preceding ball cardinality and (2^r)^(t*actualLyndonCount A r)."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration) => declaration switch
    {
        "positiveWordBall" => Seq(Forall, Sp, F.Id("A"), Comma, F.Id("r"), Comma,
            F.Id("n"), Comma, Sp, Equal(Call("positiveWordBall", F.Id("A"),
                F.Id("r"), F.Id("n")), Call("image", Call("cutoffMagnus", F.Id("r")),
                Call("wordsWithLengthAtMost", F.Id("A"), F.Id("n"))))),
        "weightedLyndonExponent" => Seq(Forall, Sp, F.Id("A"), Comma,
            F.Id("r"), Comma, Sp, Equal(Call("weightedLyndonExponent", F.Id("A"),
                F.Id("r")), Call("sum", Call("range", Add(F.Id("r"), Num(1))),
                Call("lambda", F.Id("i"), Multiply(F.Id("i"),
                    Call("actualLyndonCount", F.Id("A"), F.Id("i"))))))),
        "positiveWordBall_card_step" => Seq(Forall, Sp, F.Id("A"), Comma,
            F.Id("r"), Comma, F.Id("m"), Comma, F.Id("t"), Comma, F.Id("n"),
            Comma, Sp, F.Id("r"), Geq, F.D(2), Land, Sp,
            Add(F.Id("m"), Multiply(Call("baseLength", F.Id("A"), F.Id("r")),
                Subtract(Call("pow", Num(2), F.Id("t")), Num(1)))),
            Leq, Sp, F.Id("n"),
            Rightarrow, Call("card", Call("positiveWordBall", F.Id("A"),
                F.Id("r"), F.Id("n"))), Geq,
            Multiply(Call("card", Call("positiveWordBall", F.Id("A"),
                Subtract(F.Id("r"), Num(1)), F.Id("m"))),
                Call("pow", Call("digitBase", F.Id("r")),
                    Multiply(F.Id("t"), Call("actualLyndonCount", F.Id("A"),
                        F.Id("r")))))),
        _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
    };
}
