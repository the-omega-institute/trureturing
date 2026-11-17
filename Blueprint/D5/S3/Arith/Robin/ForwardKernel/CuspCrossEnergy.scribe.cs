using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class CuspCrossEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/CuspCrossEnergy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inner and outer cusp averages have a quadratic logarithmic cross-energy main term.",
        H("Cusp cross energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cusp-average-outer-integral"),
                DeclarationHandle.Create(Prefix + "cuspAverage_outer_integral"),
                H("The exact weighted outer integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive h<k, write L=log(k/h). The integral of B_k(y)/y from h to k equals L^2/2-L+2-(L+2)h/k. An elementary logarithmic primitive proves the identity, used to identify the leading cross energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cusp-cross-energy-estimate"),
                DeclarationHandle.Create(Prefix + "cuspCrossEnergy_estimate"),
                H("The cusp cross energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is an absolute positive constant C such that, for h>0 and k>=2h, the absolute difference between the cross energy and h*log(k/h)^2/4 is at most C*h*log(k/h). The proof uses C=10. The intervals below h, between h and k-h, and above k-h are estimated separately. CuspMovingLengths and CommonBandSharpnessTransport consume the uniform bound."))),
                DescribeRole.Theorem))));
}
