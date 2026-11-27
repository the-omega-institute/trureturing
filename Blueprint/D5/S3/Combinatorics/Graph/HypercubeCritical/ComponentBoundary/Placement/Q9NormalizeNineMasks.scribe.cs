using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9NormalizeNineMasksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixing a low-high contact sends the absent mask to the same two coordinates in every actual five-axis family.",
        H("The five-axis contact frame"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-normalized-nine-mask-contact"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9NormalizeNineMasks.exists_normalized_nine_mask_contact"),
                H("The five-axis contact frame"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fixing a low-high contact sends the absent mask to the same two coordinates in every actual five-axis family."))),
                DescribeRole.Theorem)),
        []));
}
