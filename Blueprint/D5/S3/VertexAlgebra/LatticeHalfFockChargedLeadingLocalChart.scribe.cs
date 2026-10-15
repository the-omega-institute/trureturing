using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockChargedLeadingLocalChartDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native Cleared Charged Product Chart",
        H("Native Cleared Charged Product Chart"),
        Blocks(
            Paragraph(Text("The construction keeps the actual IsUnit determinant ground representation, charge cocycle action, charge scalars and arbitrary oscillator tensor state.")),
            Describe.Lean(
                DescribeId.Create("native-cleared-product-term-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedLeadingLocalChart.cleared_product_term_expansion"),
                H("Each finite clearing term consumes the native ordered-product kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The explicit signed binomial term is identified with the native tensor common-kernel contraction expansion at the shifted pair of exponents. No replacement field, cutoff, positivity assumption or chosen fusion constant is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-square-root-chart-binomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedLeadingLocalChart.chartCoefficientValue"),
                H("The chart coefficient uses the generalized binomial series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The local cover x=y(1+t)^(1/2) is represented by the exact PowerSeries.binomialSeries coefficient. The finite diagonal-support proof and the first nonzero N+g coefficient remain separate open obligations."))),
                DescribeRole.Definition),
            Paragraph(Text("This increment does not claim the full signed iterate, local vanishing/leading theorem, literal ordinary e_a[-g-1]e_b recovery, twisted Jacobi, string completion or AdS/CFT bridge.")))));
}
