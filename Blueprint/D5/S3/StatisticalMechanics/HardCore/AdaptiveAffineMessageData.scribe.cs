using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class AdaptiveAffineMessageDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational affine coefficients and certificate patterns for actual geometric states.",
        H("Adaptive affine message data"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-affine-coefficients"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessageData.affineCoefficients"),
                H("Actual state coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each of the 881 increasing geometric masks has a slope and intercept with denominator one million. Repeated pairs share storage. No state quotient, transition equivalence or numerical solver verdict is assumed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-affine-pattern"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessageData.affinePattern"),
                H("Clamping pattern"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Three base-three digits select lower endpoint, upper endpoint or interior coordinates. Pattern 27 selects the everywhere favorable residual case. The consumer recomputes the level and checks the full rational certificate against actual geometric successors."))), DescribeRole.Definition))));
}
