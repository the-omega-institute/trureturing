using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReflectingHeatCanonicalProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical heat multiplier is the product over the positive equal-mass right endpoints.",
        H("Canonical quantile product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-product-entire"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_entire"),
                H("Entire canonical multiplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A bound on the density forces the positive endpoints to grow at least linearly in their index. Their inverse squares are summable. This gives locally uniform convergence of the paired-zero factors, so the limit is entire."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-product-real"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_real_bound"),
                H("Real-axis estimate with logarithmic clipping"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The clipped logarithm decreases to its minimum and then increases to zero. Its signed quadrature error costs at most log(1+|x|/δ). The integral of the clipping correction with density bounded by D costs at most 2Dδ. Choosing δ=1/D yields the factor exp(2)(1+D|x|). The finite-product comparison includes zeros of the product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-product-imaginary"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_imaginary_bounds"),
                H("Signed imaginary-axis estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At either imaginary argument the factors are positive. The decreasing kernel log(1+y²/t²) identifies the signed logarithmic discrepancy, with a cost of at most log(1+y²/β²) in the lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-product-half-width"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatCanonicalProduct.canonicalProduct_half_width"),
                H("Radial half-width bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each factor on a circle is bounded in modulus by its value on the imaginary axis. The signed imaginary-axis upper estimate transfers a bound of Ly/2 for the potential to a radial exponential bound of half-width L/2."))),
                DescribeRole.Theorem))));
}
