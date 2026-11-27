using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisFourLeafSignsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The shared faces produce a coherent four-term fragment. Degree eight is tight and every remaining occupied direction contributes the negative of the axis-zero term.",
        H("Four leaves determine all compensator signs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coherent-exterior-four-leaves"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisFourLeafSigns.coherent_exterior_four_leaves"),
                H("Four leaves determine all compensator signs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shared faces produce a coherent four-term fragment. Degree eight is tight and every remaining occupied direction contributes the negative of the axis-zero term."))),
                DescribeRole.Theorem)),
        []));
}
