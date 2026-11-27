using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSpatialTaylorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Taylor coefficients on a common polydisk",
        H("Ordered coefficients and normal summation"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-fourm-spatial-coefficient"),
                DeclarationHandle.Create(Prefix + "spatialCoefficient"),
                H("Ordered spatial coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take a coordinate list and a nonnegative degree for every coordinate. "
                    + "At each step, replace the selected coordinate by t, take its ordinary Taylor "
                    + "coefficient at t = 0 and leave the other coordinates as parameters. "
                    + "The empty list gives evaluation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-spatial-coefficient-has-sum"),
                DeclarationHandle.Create(Prefix + "spatialCoefficient_hasSum"),
                H("Taylor extraction commutes with normal summation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume the summands are analytic on one open polydisk about zero "
                    + "and their norms there are bounded by a summable family independent of the point. "
                    + "The sum of their ordered spatial coefficients at zero is the corresponding "
                    + "coefficient of the series. Each coordinate step uses local uniform convergence "
                    + "of complex derivatives and a Cauchy bound on the circle of half the radius. "
                    + "For degree n the new majorant is the old one divided by that radius to power n."))),
                DescribeRole.Theorem))));
}
