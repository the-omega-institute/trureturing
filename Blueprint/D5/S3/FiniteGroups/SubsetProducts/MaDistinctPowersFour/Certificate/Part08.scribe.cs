using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate;

internal sealed class MaPart08Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-four certificate decisions for chunks 139 through 156.",
        H("Order-four certificate decisions for chunks 139 through 156"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-part08-boundary08"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part08.boundary08"),
                H("boundary08"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordered List Partition contains state146, state147, state149, state155, state156. "
                    + "Each state has type Partition (Vector Nat 16) and records a symbol for each cell. "
                    + "Known asserts closure for these states so later certificates can reuse them."))),
                DescribeRole.Theorem))));
}
