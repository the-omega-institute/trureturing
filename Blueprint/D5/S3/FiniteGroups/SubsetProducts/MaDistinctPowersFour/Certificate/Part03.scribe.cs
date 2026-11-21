using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate;

internal sealed class MaPart03Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-four certificate decisions for chunks 42 through 63.",
        H("Order-four certificate decisions for chunks 42 through 63"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-part03-boundary03"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part03.boundary03"),
                H("boundary03"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordered List Partition contains state55, state56, state57, state58, state59, state60, state61, state62, state63. "
                    + "Each state has type Partition (Vector Nat 16) and records a symbol for each cell. "
                    + "Known asserts closure for these states so later certificates can reuse them."))),
                DescribeRole.Theorem))));
}
