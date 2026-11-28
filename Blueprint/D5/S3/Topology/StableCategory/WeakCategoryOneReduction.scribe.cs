using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class WeakCategoryOneReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduction of the stable category bound to contractible order complexes",
        H("Reduction of the stable category bound to contractible order complexes"),
        Blocks(Describe.Lean(
            DescribeId.Create("stable-category-product-bound-contractible-order-complex"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/WeakCategoryOneReduction.stable_product_bound_iff_contractible"),
            H("The bound on spaces of weak category one is equivalent to the universal product bound"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Fix a natural number b. A stable categorical lower cover by b sets for every finite poset with contractible order complex is equivalent to a stable lower cover by a times b sets from every categorical open cover of size a. Subdivision first makes the open cover subordinate to subcomplexes. Exact factorizations of the inclusions give contractible order complexes. The finite family of lower covers persists to one common depth, where the product cover is assembled. Conversely, the entire contractible realization is one categorical open."))),
            DescribeRole.Theorem))));
}
