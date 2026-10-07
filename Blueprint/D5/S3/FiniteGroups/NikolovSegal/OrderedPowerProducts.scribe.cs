using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class OrderedPowerProductsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Products use the original ordered list, with exactly m factors and without a commutativity assumption.",
        H("Exact ordered power products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-orderedpowerproducts-ordered-power-products"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.orderedPowerProducts"),
                H("The exact power-product set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any group G and natural q and m, orderedPowerProducts(G,q,m) is the range of powerProduct q m on functions from Fin m to G. The latter multiplies the qth powers in the order of List.finRange m. Identity factors and repetitions are allowed; m equal to zero gives only the identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-orderedpowerproducts-one-mem-orderedpowerproducts"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.one_mem_orderedPowerProducts"),
                H("Identity padding"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every group G and every natural q and m, the identity belongs to orderedPowerProducts(G,q,m). Choose the identity in every coordinate, including the empty list."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-orderedpowerproducts-lift-orderedpowerproducts"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/OrderedPowerProducts.lift_orderedPowerProducts"),
                H("Lift each factor through a surjection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any surjective group homomorphism f from G to Q and natural q and m, each x in orderedPowerProducts(Q,q,m) has a preimage y in orderedPowerProducts(G,q,m). Choose a lift of each of the exact m factors and apply map_powerProduct. Multiplication order and length are preserved."))),
                DescribeRole.Lemma))));
}
