using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FairBiasShellingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/TotalVariation/FairBiasShelling";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed fair-bias facets have uniform size and satisfy the lexicographic shelling criterion.",
        H("Purity and shelling of the fair-bias link"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("facet-card-eq-nullity"),
                DeclarationHandle.Create(Module + ".facet_card_eq_nullity"),
                H("Each facet has size equal to the column nullity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a finite labelled family of columns in a finite vector space over the binary field. " +
                    "Each maximal nonempty face of the signed complement-spanning complex has one vertex " +
                    "per label outside a column basis. Its cardinality equals the number of labels minus " +
                    "the rank of the full family. The signed complex is the nonempty part of the independence " +
                    "complex of the dual column matroid pulled back along the sign-forgetting map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lexicographic-facet-shelling"),
                DeclarationHandle.Create(Module + ".lexicographic_facet_shelling"),
                H("Lexicographic precedence satisfies the shelling criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix the same finite binary column family and any linear order on its signed labels. " +
                    "Order facets by the first differing label. For an earlier facet S and a later facet T, " +
                    "there is a facet U earlier than T that contains the intersection of S and T and omits " +
                    "exactly one vertex of T. Extend the common vertices and an earlier differing vertex to " +
                    "a basis inside T together with that vertex."))),
                DescribeRole.Theorem))));
}
