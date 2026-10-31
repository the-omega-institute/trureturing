using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;

internal sealed class PolygonEarSlideDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Polygons/PolygonEarSlide.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The adjacent-label ear slide on complete diagonal-set fibres",
        H("Condition-preserving ear slide"),
        Blocks(
            Describe.Lean(DescribeId.Create("polygon-ear-slide-datum"),
                DeclarationHandle.Create(Prefix + "SlideDatum"), H("Local four-coordinate involution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A SlideDatum records the adjacent-label involution on the complete diagonal carrier. It exchanges the observed ears s and t and exchanges the block-start coordinate e0 with the unobserved target coordinate u. The involution is retained as an explicit equality, so each retained diagonal is transformed individually."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-map"),
                DeclarationHandle.Create(Prefix + "slide"), H("Erase and insert map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The forward map erases t, applies the involution to every retained diagonal, and inserts s. It therefore acts on the full diagonal set, including every diagonal outside the observed ear coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-inverse"),
                DeclarationHandle.Create(Prefix + "unslide"), H("Inverse erase and insert map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse erases s, applies the same involution, and inserts t. The compiled inverse identities show equality of complete diagonal Finsets under the source conditions t in T and s absent from T, and under the target conditions s in U and t absent from U."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polygon-ear-slide-image-fibre"),
                DeclarationHandle.Create(Prefix + "image_condition_fibre_equiv"), H("Complete condition-fibre equivalence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("sourceFibre keeps the forced ear t, forbids s, retains a forced set P, a forbidden set Q, and fixes the exact trace R union {t} on J. imageFibre is the image of this complete source fibre under the diagonal-set map. image_condition_fibre_equiv is the resulting equivalence, so empty fibres and every individual completion are preserved. Identifying imageFibre with the polygon target trace on J with t and u removed requires the actual polygon triangulation deletion carrier."))),
                DescribeRole.Theorem)), []));
}
