using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class WeavingReferenceDegreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform forward degree bound.",H("A uniform forward degree bound"),Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Topology/WeavingReferenceDegree.orderedGraph_forward_degree"),
                H("A uniform forward degree bound"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every interval-circle vertex meets only four possible crossing labels. Distinct incident edges yield distinct neighbors, so its full degree is at most four, including connectors to outer hubs. Hubs are independent. Order all interval vertices before the hubs, using the explicit finite equivalence supplied by the uniform-circle classification. An interval vertex then has at most four later neighbors, while a hub has no later neighbors. This proves a bound on forward degree; no bound on the full degree of a hub is asserted."))),DescribeRole.Theorem))));
}
