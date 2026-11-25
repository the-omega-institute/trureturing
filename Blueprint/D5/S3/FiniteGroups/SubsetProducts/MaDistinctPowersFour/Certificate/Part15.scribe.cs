using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate;

internal sealed class MaPart15Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-four certificate decisions for chunks 270 through 290.",
        H("Order-four certificate decisions for chunks 270 through 290"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-part15-boundary15"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part15.boundary15"),
                H("boundary15"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordered List Partition contains state271, state286, state287, state288, state290. "
                    + "Each state has type Partition (Vector Nat 16) and records a symbol for each cell. "
                    + "Known asserts closure for these states so later certificates can reuse them."))),
                DescribeRole.Theorem))));
}
