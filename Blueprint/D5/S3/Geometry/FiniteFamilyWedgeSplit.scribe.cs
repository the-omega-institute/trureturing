using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteFamilyWedgeSplitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A distinguished factor separates from the family wedge with its original inclusions.",
        H("Splitting a family wedge at one factor"),
        Blocks(Describe.Lean(
            DescribeId.Create("split"),
            DeclarationHandle.Create("D5/S3/Geometry/FiniteFamilyWedgeSplit.split"),
            H("The based homeomorphism with a binary wedge"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Choose an index in a family of pointed spaces. The family wedge is homeomorphic " +
                "to the binary wedge of that space and the wedge of the remaining family. Both " +
                "directions descend continuous maps from the disjoint sums. The homeomorphism " +
                "takes the shared basepoint to the binary wedge point and preserves the original " +
                "inclusion of each factor on its designated side. The remaining family may be empty."))),
            DescribeRole.Definition))));
}
