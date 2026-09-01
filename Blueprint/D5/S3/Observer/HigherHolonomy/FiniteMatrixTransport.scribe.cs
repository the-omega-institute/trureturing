using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HigherHolonomy;

internal sealed class FiniteMatrixTransportDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/HigherHolonomy/FiniteMatrixTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite matrix transport composes along vertex paths and gauge factors telescope to the endpoints.",
        H("Finite Matrix Path Transport"),
        Blocks(
            Def("end", "pathEnd", "Path endpoint",
                "A start vertex and list of successive vertices determine the terminal vertex."),
            Def("transport", "pathTransport", "Finite path transport",
                "Invertible edge matrices are multiplied in reverse order so the first edge acts first on a column state."),
            Def("gauge", "gaugeEdgeTransport", "Gauge-transformed edge transport",
                "Each edge matrix is conjugated by the gauges at its target and source."),
            Thm("append", "pathTransport_append", "Path append composition",
                "The transport of appended path segments is the later transport multiplied by the earlier transport."),
            Thm("telescope", "pathTransport_gauge", "Gauge factors telescope",
                "All interior vertex gauges cancel and only endpoint factors remain."),
            Thm("loop", "loopTransport_gauge_conjugate", "Loop holonomy is gauge conjugate",
                "A closed path transforms by conjugation at its base vertex."),
            Thm("one-edge", "one_edge_path_transport", "One-edge transport",
                "A path containing one target vertex evaluates to its single edge matrix.")),
        []));

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
