using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FairBiasFacetQuotientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/TotalVariation/FairBiasFacetQuotient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each omitted simplex attaches to the retained realization along its full boundary.",
        H("The quotient by the retained fair-bias realization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("disk-in-core-iff-boundary"),
                DeclarationHandle.Create(Module + ".diskIn_mem_core_iff_boundary"),
                H("The attaching locus of an omitted simplex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A point of a full-restriction facet simplex belongs to the retained realization " +
                    "exactly when a coordinate indexed by a vertex of that facet is zero. This gives " +
                    "the entire boundary, which is empty for a singleton facet."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("core-attachment-homeomorphism"),
                DeclarationHandle.Create(Module + ".exists_core_attachment_homeomorph"),
                H("The canonical attachment quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose the signed complex has a nonempty facet. Take the disjoint sum of one " +
                    "point and the coordinate simplices of the full-restriction facets. Identify every " +
                    "attaching boundary point with the added point. The resulting space is homeomorphic " +
                    "to the original realization with its retained subcomplex collapsed. The " +
                    "homeomorphism agrees with coordinate inclusion followed by the quotient map on " +
                    "each simplex and sends the added point to the retained class."))),
                DescribeRole.Theorem))));
}
