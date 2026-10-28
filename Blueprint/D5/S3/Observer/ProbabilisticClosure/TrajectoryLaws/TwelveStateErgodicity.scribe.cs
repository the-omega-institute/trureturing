using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class TwelveStateErgodicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ergodicity of the actual stationary output law", H("Ergodicity of the actual stationary output law"),
        Blocks(
            Paragraph(Text("The shift is the original integer emitted-bit shift, under the same actual joint law and its complete visible marginal.")),
            Describe.Lean(DescribeId.Create("actual-output-ergodic"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateErgodicity.actual_output_ergodic"),
                H("Ergodicity of the actual visible law"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual P is ergodic under z(t) mapped to z(1+t). A measurable invariant event admits almost-sure versions from each retained half-line by measurable-cylinder approximation, stationarity and summable approximation errors. The actual whole-past/future factorization at H0 forces that event to be a Boolean function of H0. Invariance makes this function equal along every positive marked edge, and irreducibility of the original hidden chain makes it constant. This argument uses the actual J throughout and does not infer a pathwise filtration identification from separate-radius stationarity."))), DescribeRole.Theorem))));
}
