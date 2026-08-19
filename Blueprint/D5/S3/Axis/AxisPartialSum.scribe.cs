using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class AxisPartialSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The legal-word partial sum satisfies the two-step trace recurrence.",
        H("Axis Partial Sum"),
        Blocks(
            Paragraph(Text(
                "Legal words of digit depth at most K are exactly the naturals below the "
                    + "Fibonacci number at K plus one, so the partial sum over words is a sum "
                    + "over an initial segment and needs no separate word type. That is what "
                    + "makes the recurrence a splitting of a range rather than a combinatorial "
                    + "argument about strings.")),
            Paragraph(Text(
                "Splitting the range at the next Fibonacci number sorts words by their highest "
                    + "occupied digit. A word that uses digit K plus two starts there, and the "
                    + "greedy decomposition leaves a remainder below the Fibonacci number two "
                    + "steps down: using a digit forces its predecessor to stay empty. The "
                    + "weight of the head factors out, which is the recurrence.")),
            Describe.Lean(
                DescribeId.Create("legal-word-partial-sum-satisfies-the-trace-recurrence"),
                DeclarationHandle.Create(
                    "D5/S3/Axis/AxisPartialSum.axisPartialSum_succ_succ"),
                H("The partial sum satisfies the trace recurrence"),
                StatementSource.FromAuthor(SumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The head weight is the axis weight at the highest digit, whose own "
                        + "multiplicative recurrence is proved separately."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Axis/AxisTraceRecurrence")),
        ]));

    private static Formula W(Formula index) => Seq(F.Id("W"), Underscore, Grp(index));

    private static Formula T(Formula index) => Seq(F.Id("t"), Underscore, Grp(index));

    private static Formula SumFormula()
    {
        Formula k = F.Id("K");

        return Disp(Seq(
            Forall, Sp, k, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            W(Seq(k, Plus, D(2))), Sp, Eq, Sp, W(Seq(k, Plus, D(1))), Sp, Plus, Sp,
            T(Seq(k, Plus, D(2))), Sp, Cdot, Sp, W(k), Dot));
    }
}
