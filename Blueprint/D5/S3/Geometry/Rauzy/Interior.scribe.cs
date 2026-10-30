using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Rauzy;

internal sealed class SeparatedCylinderInteriorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Separated shrinking upper cylinder covers turn positive planar area into interior.",
            H("Interior from separated cylinder geometry"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("separated-planar-cylinder-system"),
                    DeclarationHandle.Create(
                        "D5/S3/Geometry/Rauzy/Interior.SeparatedCylinderSystem"),
                    H("Actual cylinder data"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The data records a compact carrier of positive area, its disk "
                        + "bound, contraction, scale separation and actual upper covers. "
                        + "It contains neither a finite translate disk cover nor interior."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("interior-from-separated-planar-cylinders"),
                    DeclarationHandle.Create(
                        "D5/S3/Geometry/Rauzy/Interior.interior_nonempty_of_separated_cylinders"),
                    H("A synchronized finite family covers a disk"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "K is a compact subset of the complex plane with positive area, "
                            + "bounded by a closed disk of radius R. At every natural scale n, "
                            + "the actual affine cylinders p + z^n K cover K from above. "
                            + "Their centers are separated by at least c times norm(z)^n, "
                            + "where c is positive and 0 < norm(z) < 1. No reverse cylinder "
                            + "inclusion or open-set condition is assumed.")),
                        Paragraph(Text(
                            "Choose one density point. The relevant normalized centers lie "
                            + "in a fixed compact disk and are c-separated. A finite c/3-net "
                            + "represents every center, with at most one center per slot; unused slots "
                            + "contain zero. Compactness of the finite product gives one "
                            + "subsequence on which all slots converge simultaneously.")),
                        Paragraph(Text(
                            "The limiting translates cover the open unit disk. A missing "
                            + "point would have a whole ball missing from the closed finite "
                            + "union. Uniform convergence of all slots preserves a smaller "
                            + "hole in every sufficiently late cluster. The upper cylinder "
                            + "cover then produces an actual K-free ball whose relative "
                            + "area is fixed and positive, contradicting density one. "
                            + "A finite union of closed nowhere-dense translates cannot "
                            + "cover an open disk, so K has nonempty interior.")),
                        Paragraph(Text(
                            "The argument is an unbounded analytic existence construction. "
                            + "It asserts no numerical inner disk, tiling, connectedness, "
                            + "or original-research novelty."))),
                    DescribeRole.Theorem)),
            []));
    }
}
