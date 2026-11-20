using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9FivefoldCoverDynamicsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FivefoldCoverDynamics.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five parallel covers flip a corner condition",
        H("Five parallel covers flip a corner condition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-fivefold-cover-endpoint-switch"),
                DeclarationHandle.Create(Prefix + "fivefold_cover_endpoint_switch"),
                H("Five parallel covers flip a corner condition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose a cube edge outside two separated Huang-balanced cubic "
                        + "supports has three parallel covers from one support and two from the "
                        + "other.")),
                    Paragraph(Text("At each endpoint the smaller side uses the same pair of directions. "
                        + "Its two-direction corner belongs to the smaller support at exactly "
                        + "one endpoint.")),
                    Paragraph(Text("If both corners belonged, the four translated vertices would form a "
                        + "selected square. If both were absent, cubicity would force a shared "
                        + "fourth direction at the two ends of a selected edge, again making a "
                        + "square."))),
                DescribeRole.Theorem)),
        []));
}
