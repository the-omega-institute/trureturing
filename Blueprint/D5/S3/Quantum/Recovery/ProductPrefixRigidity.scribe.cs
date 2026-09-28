using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class ProductPrefixRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For locally informationally complete normalized common-label source families, assuming label-independent norm products at every prefix, actual local compositions with isometric roots, one actor at each step, and inactive identity up to coordinate equivalence force positive prefixes to factor into scaled local isometries. A first zero factor annihilates the product map and all later products, without requiring other zero-tail factors to have scalar Grams.",
        H("ProductPrefixRigidity"),
        Blocks(Describe.Lean(
            DescribeId.Create("prefix-rigidity"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/ProductPrefixRigidity.prefix_rigidity"),
            H("prefix rigidity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For locally informationally complete normalized common-label source families, label-independent norm products along actual local compositions force positive prefixes to factor into scaled local isometries. A first zero factor annihilates the product map and all later products, without requiring other zero-tail factors to have scalar Grams."))),
            DescribeRole.Theorem))));
}
