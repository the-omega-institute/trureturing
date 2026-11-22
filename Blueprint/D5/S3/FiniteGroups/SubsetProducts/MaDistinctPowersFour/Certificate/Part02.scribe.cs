using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate;

internal sealed class MaPart02Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-four certificate decisions for chunks 21 through 41.",
        H("Order-four certificate decisions for chunks 21 through 41"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-part02-boundary02"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part02.boundary02"),
                H("boundary02"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordered List Partition contains state21, state24, state38, state39, state40, state41. "
                    + "Each state has type Partition (Vector Nat 16) and records a symbol for each cell. "
                    + "Known asserts closure for these states so later certificates can reuse them."))),
                DescribeRole.Theorem))));
}
