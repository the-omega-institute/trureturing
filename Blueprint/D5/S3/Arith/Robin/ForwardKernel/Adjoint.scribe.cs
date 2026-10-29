using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class AdjointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/Adjoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Mellin adjoint retains the complete signed arithmetic response of the original forward kernel.",
        H("The compact adjoint of the forward price kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adjoint-kernel-compact"),
                DeclarationHandle.Create(Prefix + "adjointKernel_eq_compact"),
                H("Compact support at every evaluation point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Mellin adjoint q_s(t) is the integral over x>=x0 of "
                    + "x^(-s-1)*k(x,t). For each t it equals the compact integral "
                    + "over x in [x0,max(x0,t)]. Centers x>=t have zero kernel value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjoint-kernel-integrable"),
                DeclarationHandle.Create(Prefix + "adjointKernel_center_integrable"),
                H("Absolute integrability in the center variable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For x0>=4, every complex s and real t give an absolutely integrable "
                    + "center integrand x^(-s-1)*k(x,t) on [x0,infinity). Its support "
                    + "is compact and its Mellin weight is continuous there."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-response-prefix-kernel"),
                DeclarationHandle.Create(Prefix + "forwardResponse_eq_prefix_kernel"),
                H("The complete signed response of the price kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For x>1, T(x) equals the sum of Lambda(n)*k(x,n) for "
                    + "1<=n<=floor(B(x)), minus the integral of k(x,t) over [x,B(x)]. "
                    + "The normalization sqrt(x)/(w(x)*H(x)^2) is exactly "
                    + "1/(w(x)*x^(11/10)); the initial atom is excluded and the "
                    + "terminal atom has zero price weight."))),
                DescribeRole.Theorem))));
}
