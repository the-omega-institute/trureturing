using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class AffineProductCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact clamped product certificates for full-box hard-core affine messages.",
        H("Affine product certificates"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-clipped-product-bound"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.clipped_product_bound"),
                H("A global product bound from a clamped witness"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Divide the affine residual by the positive level and the three coordinates by their reference values. The clamping inequalities make the sum of these four nonnegative factors at most four. Mathlib's AM-GM theorem bounds their product by one. The negative-residual case is handled separately. A local numerical optimum is never assumed global."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-clip-witness"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.ClipWitness"),
                H("Rational proposal data"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A witness stores a rational level and three rational reference coordinates. Validity is a separate proposition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-checked-affine-row"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.CheckedRow"),
                H("Exact finite certificate obligations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A present witness must satisfy positivity, interval bounds, exact balance, the three clamping alternatives and the rational margin. The absent-witness case proves that the residual has the favorable sign throughout the box."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-checked-affine-row-sound"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AffineProductCertificate.checked_row_sound"),
                H("Every real point and every smaller activity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The checked rational data imply the polynomial margin on the entire real box and throughout the nonnegative activity interval. This theorem supplies the continuous semantic bridge consumed by the concrete adaptive-grid certificate."))), DescribeRole.Theorem),
            Paragraph(Text("The general AM-GM principle is prior art and reused from Mathlib. These proof scripts have not been elaborated in the authoring runtime.")))));
}
