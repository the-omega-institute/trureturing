using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HigherHolonomy;

internal sealed class MatrixGaugeCovarianceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/HigherHolonomy/MatrixGaugeCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace and determinant of finite matrix loop holonomy are invariant under vertex gauge transport.",
        H("Gauge-Invariant Finite Loop Observables"),
        Blocks(
            Def("trace", "transportTrace", "Transport trace",
                "A finite path is observed through the trace of its matrix transport."),
            Def("determinant", "transportDeterminant", "Transport determinant",
                "A finite path is observed through the determinant of its matrix transport."),
            Thm("trace-conjugate", "trace_unit_conjugate", "Trace is conjugacy invariant",
                "Conjugating a matrix unit by another unit preserves its trace."),
            Thm("det-conjugate", "determinant_unit_conjugate", "Determinant is conjugacy invariant",
                "Conjugating a matrix unit by another unit preserves its determinant."),
            Thm("trace-loop", "loop_transport_trace_gauge_invariant", "Loop trace is gauge invariant",
                "Endpoint gauge covariance becomes trace invariance on every closed path."),
            Thm("det-loop", "loop_transport_determinant_gauge_invariant", "Loop determinant is gauge invariant",
                "Endpoint gauge covariance becomes determinant invariance on every closed path."),
            Thm("empty", "transportDeterminant_empty", "Empty-loop determinant",
                "The determinant observable of the identity path equals one.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
