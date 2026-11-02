using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;
internal sealed class ActualKernelMomentCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete actual-K moment certificate.",
        H("Original full-kernel certificate source"), Blocks(
            Describe.Lean(DescribeId.Create("actual-kernel-explicit-leading-one"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate.actual_kernel_explicit_leading_one"),
                H("actual kernel explicit leading one"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the original full actual-K source endpoint: arbitrary finite universe-polymorphic I, D>0, nodes in [0,D], arbitrary complex coefficients and atomic moments of EVERY degree 0,...,N(D), inclusive, imply E<=Re Q_ActualKernelLocalPositivity.K. Here B=C(1+10!(2/alpha)^10), d0=gamma-1+log(2pi), beta_D=exp(D/2)(1+C(exp(-alpha(D/4)^(1/10))+exp(-D/4)))+D+B, C_D=((9+4C+2B)exp(D/2)+D+3)/4, and N(D)=ceil(max(1,D sqrt(C_D)/2,(5D/4)exp(beta_D+d0+2))). Global C,alpha are selected from actual unconditional MediumPNT before every family. The complete mixture, actual weighted prime inequality and concrete H/V corrections are all consumed. Nonnegative d0 W is dropped only after proving d0>=0. The unchanged ceiling gives q/D>=8, delta_q C_D<=1/8 and log(q/D)>=beta_D+d0+2+1/5, leaving the original endpoint slack. There is no energy division or nonempty, distinctness or real-coefficient restriction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-signed-expression-compensation"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate.actual_signed_expression_compensation"),
                H("actual signed expression compensation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same original endpoint implies (log(2pi)-1-gamma)(E-W)-Re Q_P+E<=signedJExpression. This theorem concerns only the explicitly defined finite expression -2gamma(E-W)-primeQuadratic+continuum+V. An independently defined ORIGINAL signed-J integral has not been identified with that expression. No arbitrary J bridge is assumed and no signed-J integral completion is claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-order-leading-one-asymptotic"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate.original_order_leading_one_asymptotic"),
                H("original order leading one asymptotic"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For exactly the same ceiling/max N(D), log(N(D)/D)/exp(D/2) tends to 1. The actual MediumPNT-rate errors tend to zero and (D+B)exp(-D/2) tends to zero, so beta_D/exp(D/2) tends to 1. For D>=1 the third maximum term dominates the other two; ceiling bounds place log(N(D)/D) between beta_D+d0+2+log(5/4) and beta_D+d0+2+log(5/2). Dividing these bounds by exp(D/2) proves the limit. No sufficient order is enlarged."))),
                DescribeRole.Theorem))));
}
