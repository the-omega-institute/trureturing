using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate;

internal sealed class MaPart06Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-four certificate decisions for chunks 100 through 117.",
        H("Order-four certificate decisions for chunks 100 through 117"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-part06-boundary06"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part06.boundary06"),
                H("boundary06"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordered List Partition contains state103, state104, state105, state106, state111, state112, state113, state117. "
                    + "Each state has type Partition (Vector Nat 16) and records a symbol for each cell. "
                    + "Known asserts closure for these states so later certificates can reuse them."))),
                DescribeRole.Theorem))));
}
