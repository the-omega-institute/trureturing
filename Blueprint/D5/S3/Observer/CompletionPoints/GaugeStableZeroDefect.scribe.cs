using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CompletionPoints;

internal sealed class GaugeStableZeroDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/CompletionPoints/GaugeStableZeroDefect.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gauge-invariant normalization and defect data preserve completion status.",
        H("Gauge Stable Zero Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gauge-transport-preserves-completion"),
                DeclarationHandle.Create(Prefix + "gauge_preserves_completion"),
                H("Gauge transport preserves completion"),
                StatementSource.FromAuthor(CompletionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume a gauge transformation preserves both normalization and defect "
                            + "values at every state.")),
                    Paragraph(Text(
                        "For a fixed normalization target, defect zero, and state, the two "
                            + "invariances transport both conjuncts of completion in either "
                            + "direction.")),
                    Paragraph(Text(
                        "The equivalence is pointwise; invertibility of the gauge map is not "
                            + "assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("defect-invariance-preserves-zero-defect"),
                DeclarationHandle.Create(Prefix + "gauge_preserves_zero_defect"),
                H("Defect invariance preserves zero defect"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume only that the defect value is invariant under the gauge map at "
                            + "every state.")),
                    Paragraph(Text(
                        "At a fixed state, equality to the designated zero is then equivalent "
                            + "before and after gauge transport."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Invariance(string readout)
    {
        Formula state = F.Id("x");
        return Seq(
            Forall, Sp, state, Colon, Sp, F.Id("X"), Comma, Sp,
            Call(readout, Call("gauge", state)), Sp, Eq, Sp, Call(readout, state));
    }

    private static Formula CompletionStatement()
    {
        Formula left = Call("CompletedAt", F.Id("normalize"), F.Id("target"),
            F.Id("defect"), F.Id("zero"), F.Id("x"));
        Formula right = Call("CompletedAt", F.Id("normalize"), F.Id("target"),
            F.Id("defect"), F.Id("zero"), Call("gauge", F.Id("x")));
        Formula antecedent = Seq(
            Open, Invariance("normalize"), Close, Sp, Land, Sp,
            Open, Invariance("defect"), Close);
        return Disp(Seq(
            Forall, Sp, F.Id("normalize"), Colon, Sp,
            Arrow(F.Id("X"), F.Id("N")), Comma, Sp,
            F.Id("target"), Colon, Sp, F.Id("N"), Comma, Sp,
            F.Id("defect"), Colon, Sp, Arrow(F.Id("X"), F.Id("D")), Comma,
            RowBreak, Grp(),
            F.Id("zero"), Colon, Sp, F.Id("D"), Comma, Sp,
            F.Id("gauge"), Colon, Sp, Arrow(F.Id("X"), F.Id("X")), Comma, Sp,
            F.Id("x"), Colon, Sp, F.Id("X"), Comma, RowBreak, Grp(),
            Open, antecedent, Close, Sp, Rightarrow, Sp,
            Open, left, Sp, Iff, Sp, right, Close, Dot));
    }

}
