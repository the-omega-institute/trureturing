using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteAttachmentQuotientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Geometry/FiniteAttachmentQuotient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Collapsing a closed core in a finite cover identifies exactly the attachment points over it.",
        H("Quotients of finite attachment families"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-homeomorph"),
            DeclarationHandle.Create(Module + ".exists_homeomorph"),
            H("The canonical quotient of the attachment family"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A compact Hausdorff space is covered by a closed core and the images of finitely many " +
                "compact spaces under continuous injections. Fix a point of the core and suppose " +
                "intersections of distinct attachment images lie in the core. In the disjoint sum of " +
                "the attachment spaces and an added point, identify with that point each attachment point " +
                "mapping into the core. The resulting quotient is homeomorphic to the ambient space " +
                "with the core collapsed. On each attachment the map is the given injection followed by " +
                "the ambient collapse. It maps the added point to the core class. The construction permits an " +
                "empty index and attachments disjoint from the core."))),
            DescribeRole.Theorem))));
}
