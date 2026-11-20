using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour;

internal sealed class MaModularBlockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive exponents for four generators over a composite modulus.",
        H("Consecutive exponents for four generators over a composite modulus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-modularblock-fourblock-of-orderfour"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/ModularBlock.fourBlock_of_orderFour"),
                H("fourBlock_of_orderFour"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The products are formed modulo the full common order, with the four generator units distinct there. Commutativity excludes the motif. Equal column sets would force a multiplicative coset in a prime reduction, contradicted by the first and second coefficient power sums."))),
                DescribeRole.Theorem))));
}
