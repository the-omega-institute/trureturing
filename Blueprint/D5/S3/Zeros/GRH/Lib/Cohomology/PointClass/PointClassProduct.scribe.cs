using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.PointClass;

internal sealed class PointClassProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Point Class Product", H("Point Class Product"),
        Blocks(
            Paragraph(Text("Hodge class of a point of a product is the product of point classes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/PointClass/PointClassProduct.cup_pointClass"),
                H("cup_pointClass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The product of point classes is a point class: over a field k of characteristic 0, if X and Y have atlases of dimensions d and 1, then cl(z) × cl(w) = cl(z, w) in Hdg^{d+1}(X × Y) for k-points z, w.")))))));
}
