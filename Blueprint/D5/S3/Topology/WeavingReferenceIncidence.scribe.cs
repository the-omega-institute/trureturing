using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class WeavingReferenceIncidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crossing labels and graph edges.",H("Crossing labels and graph edges"),Blocks(
            Describe.Lean(DescribeId.Create("main-result"),
                DeclarationHandle.Create("D5/S3/Topology/WeavingReferenceIncidence.crossingEdgeEquiv"),
                H("Crossing labels and graph edges"),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let n be at least two, m at least three and p either parity. Uniform-circle codes distinguish all interval columns and both outer hubs. A cup-cap crossing joins consecutive cyclic times in a single column. A vertical crossing joins two distinct column codes, with the boundary hub time fixed to zero. The unordered endpoint pair determines the crossing: reversing a row edge would force two to vanish modulo m, which is impossible for m at least three. Vertical edge times are recovered from an interval endpoint. Consequently the crossing labels biject with the simple reference graph edges, with exactly nm edges."))),DescribeRole.Definition))));
}
