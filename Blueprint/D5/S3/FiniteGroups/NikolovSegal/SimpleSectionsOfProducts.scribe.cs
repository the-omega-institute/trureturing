using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class SimpleSectionsOfProductsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A simple section of a finite product occurs in one factor even when its section subgroup is arbitrary.",
        H("Simple sections of finite products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-simplesectionsofproducts-simple-involves-pi-factor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SimpleSectionsOfProducts.simple_involves_pi_factor"),
                H("A simple section occurs in a factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary simple group A, a finite index type and an arbitrary family of groups, if A is a section of their product, then A is a section of one factor. A section is a surjective image of an arbitrary subgroup; that subgroup need not itself be a product. Induction by adjoining one index uses the simple-section image-or-kernel alternative, and embeds the projection kernel into the new factor. Individual factors need not be finite."))),
                DescribeRole.Theorem))));
}
