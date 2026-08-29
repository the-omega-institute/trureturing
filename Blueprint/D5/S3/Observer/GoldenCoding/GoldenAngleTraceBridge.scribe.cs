using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenAngleTraceBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real trace of a thirty-six-degree rotation is the golden ratio and forgets chirality.",
        H("Golden Angle Trace Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("thirty-six-degree-trace-is-golden"),
                DeclarationHandle.Create(Prefix + "thirty_six_degree_trace_eq_golden_ratio"),
                H("Thirty-six degrees has golden rotation trace"),
                StatementSource.FromAuthor(TraceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Degrees are first converted to radians. The thirty-six-degree angle is "
                            + "pi over five, whose doubled cosine is the golden ratio.")),
                    Paragraph(Text(
                        "The trace is an observer from rotation phase to a real invariant. It is "
                            + "even, so opposite rotation directions have the same observation.")),
                    Paragraph(Text(
                        "This proves a typed bridge between angle and ratio. It does not identify "
                            + "the angle carrier with the real number carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rotation-trace-forgets-orientation"),
                DeclarationHandle.Create(Prefix + "rotation_trace_not_injective"),
                H("The trace observer is not injective"),
                StatementSource.FromAuthor(NoninjectiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The golden angle and its negative are distinct, while cosine gives them "
                        + "the same trace. This is the explicit chirality-loss witness."))),
                DescribeRole.Theorem))));

    private static Formula TraceFormula() => Disp(Seq(
        D(2), Sp, Call("cos", Seq(Pi, Slash, D(5))), Sp, Eq, Sp,
        F.Id("varphi")));

    private static Formula NoninjectiveFormula() => Disp(Seq(
        Neg, Sp, Call("Injective", F.Id("rotationTrace"))));
}
