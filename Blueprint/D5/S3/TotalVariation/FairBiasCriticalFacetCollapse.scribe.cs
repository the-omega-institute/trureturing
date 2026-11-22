using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FairBiasCriticalFacetCollapseDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/TotalVariation/FairBiasCriticalFacetCollapse";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed complex with its full-restriction facets removed collapses onto its first simplex.",
        H("Collapse after omitting full-restriction facets"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-collapse-to-first-facet"),
            DeclarationHandle.Create(Module + ".exists_collapse_to_first_facet"),
            H("The retained subcomplex collapses to its first simplex"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Start with a signed fair-bias complex having at least one nonempty facet, and order " +
                "the facets lexicographically by the chosen order on the signed labels. Remove exactly " +
                "the facets that equal their restriction faces, keeping all proper subfaces. There is " +
                "a sequence of elementary collapses from the resulting subcomplex to the simplex " +
                "on the first facet. When a full-restriction facet is removed, its preceding and " +
                "following retained prefixes agree. At every other step after the first, the elementary " +
                "pairs from the restriction interval remain present and free in the retained prefix."))),
            DescribeRole.Theorem))));
}
