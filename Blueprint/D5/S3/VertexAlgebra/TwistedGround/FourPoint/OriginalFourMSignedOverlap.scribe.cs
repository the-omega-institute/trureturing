using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSignedOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native signed sources on the four-point charts",
        H("The A and B germs and both D lips"),
        Blocks(
            Paragraph(Text("For 0 < z < 1, the chart parameters are rA = 1−1/z, rB = z and rD = 1/z. "
                + "The choice upperA = true selects the lower D lip Im r < 0. "
                + "The choice upperA = false selects the upper D lip Im r > 0.")),
            Describe.Lean(DescribeId.Create("original-fourm-signed-chosen-chart-source"),
                DeclarationHandle.Create(Prefix + "chosenChartSource"),
                H("Source with the chosen period root"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write r for the chart parameter, b = b(u) and h = h(e,u,r). "
                    + "The outgoing source is (h/b)^(−1/2)/b. The inward source is "
                    + "(h/[b(1−r)])^(−1/2)/(b periodRoot(c,z)). "
                    + "The chosen D root is the lower radial lip at rD."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-signed-parameter-complement"),
                DeclarationHandle.Create(Prefix + "chart_parameter_ne_one"),
                H("Nonzero complementary parameter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each chart and real 0 < z < 1, the complementary argument "
                    + "1−parameter(c,z) is nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-source-at-zero"),
                DeclarationHandle.Create(Prefix + "chosen_chart_source_at_zero"),
                H("Analyticity and period-root normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 0 < z < 1 and any chart and flag, the chosen source is "
                    + "analytic at u = 0. Its value there is 1 for the outgoing flag and the reciprocal "
                    + "of the chosen period root for the inward flag."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-source-square"),
                DeclarationHandle.Create(Prefix + "chosen_chart_source_square"),
                H("Square of the chosen source"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 0 < z < 1 and any chart and flag, wherever the native "
                    + "factors b(u) and h(e,u,parameter(c,z)) are nonzero, the square of the chosen "
                    + "source is the reciprocal of their product."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-chart-source-eq-native"),
                DeclarationHandle.Create(Prefix + "chosen_chart_source_eq_native"),
                H("Native source germ in A and B"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For c equal to A or B, require |parameter(c,z)| < 1. "
                    + "For either sign e, the chosen source agrees with sourceMode(e,·,parameter(c,z)) "
                    + "on a neighborhood of the spatial origin."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-signed-chart-d-lip-mean"),
                DeclarationHandle.Create(Prefix + "dLipMean_eq_chosen_chart_source"),
                H("Source normalization on both D lips"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At rD = 1/z with 0 < z < 1, the actual dLipMean equals the chosen D "
                    + "source on the lower radial lip for both signs and on the upper radial lip for the "
                    + "outgoing sign. The upper radial lip reverses the inward source. The identity is "
                    + "pointwise in the spatial coordinate."))),
                DescribeRole.Theorem))));
}
