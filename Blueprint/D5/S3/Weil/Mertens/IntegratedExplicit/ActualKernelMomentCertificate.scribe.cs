using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;
internal sealed class ActualKernelMomentCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete actual-K moment certificate.",
        H("Original full-kernel certificate source"), Blocks(
            Describe.Lean(DescribeId.Create("q-scalar-bounds"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate.q_scalar_bounds"),
                H("Original moment order scalar bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the original ceiling N(C, alpha, D), with C at least one and D positive, the order is at least one and N/D is at least eight. The exact curvature payment is at most one eighth, and the logarithmic ceiling pays beta plus the Euler and endpoint constants with the retained one fifth margin. The definition keeps the original max, ceiling, inclusive moment degree, and all degenerate finite families."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-kernel-explicit-leading-one"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate.actual_kernel_explicit_leading_one"),
                H("actual kernel explicit leading one"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the original full actual-K source endpoint: arbitrary finite universe-polymorphic I, D>0, nodes in [0,D], arbitrary complex coefficients and atomic moments of EVERY degree 0,...,N(D), inclusive, imply E<=Re Q_ActualKernelLocalPositivity.K. Here B=C(1+10!(2/alpha)^10), d0=gamma-1+log(2pi), beta_D=exp(D/2)(1+C(exp(-alpha(D/4)^(1/10))+exp(-D/4)))+D+B, C_D=((9+4C+2B)exp(D/2)+D+3)/4, and N(D)=ceil(max(1,D sqrt(C_D)/2,(5D/4)exp(beta_D+d0+2))). Global C,alpha are selected from actual unconditional MediumPNT before every family. The complete mixture, actual weighted prime inequality and concrete H/V corrections are all consumed. Nonnegative d0 W is dropped only after proving d0>=0. The unchanged ceiling gives q/D>=8, delta_q C_D<=1/8 and log(q/D)>=beta_D+d0+2+1/5, leaving the original endpoint slack. There is no energy division or nonempty, distinctness or real-coefficient restriction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-kernel-q6-small-window"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate.actual_kernel_q6_small_window"),
                H("q6 complete-K small-window endpoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite complex atomic family, including empty, repeated, cancelling and zero-energy families, with nodes in the inclusive window [0,D], 0<=D<=log 3, and all moments through q vanishing, q>=6 implies (36/575) E <= Re Q_K. The literal K is the complete original kernel K=P+fullR with every inclusive prime power and boundary term. The proof consumes the finite positive first-20 mixture head, the division-free Gamma coercivity, the exact small-window prime translation and V cutoff bounds, and keeps the D=0 branch explicit; it assumes no nonemptiness, distinctness, realness or exponential-null condition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-kernel-q22-small-window"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate.actual_kernel_q22_small_window"),
                H("q22 complete-K small-window endpoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same arbitrary finite complex inclusive-window hypotheses, q>=22 gives (2017/2000) E <= Re Q_K, and therefore E <= Re Q_K. The endpoint retains the literal complete K, inclusive prime powers and boundary term, consumes the original P/fullR decomposition and the finite positive mixture head at the exact 1600 gap, and handles empty, repeated, cancelling, E=0 and D=0 cases without normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-signed-expression-compensation"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate.actual_signed_expression_compensation"),
                H("actual signed expression compensation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same original endpoint implies (log(2pi)-1-gamma)(E-W)-Re Q_P+E<=signedJExpression. This theorem concerns only the explicitly defined finite expression -2gamma(E-W)-primeQuadratic+continuum+V. An independently defined ORIGINAL signed-J integral has not been identified with that expression. No arbitrary J bridge is assumed and no signed-J integral completion is claimed."))),
                DescribeRole.Theorem),
            Paragraph(Text("Exact original order limit as an application.")),
            Paragraph(Text("Fix any PNTConstants p, with C=p.C>=1 and alpha=p.alpha>0; in particular take the same unconditional pnt as in the certificate. Keep M(D)=exp(D/2), B=C(1+10!(2/alpha)^10), d0=gamma-1+log(2pi), beta(D)=M(D)(1+C(exp(-alpha(D/4)^(1/10))+exp(-D/4)))+D+B and C_D=((9+4C+2B)M(D)+D+3)/4. The unchanged order is N(D)=ceil(max(1,max(D sqrt(C_D)/2,(5D/4)exp(beta(D)+d0+2)))). The application of standard power/exponential limits and ceiling inequalities gives exactly log(N(D)/D)/exp(D/2) tending to 1 as D tends to positive infinity.")),
            Paragraph(Text("For D>=1, the retained scalar inequalities give beta(D)>=2, C_D<2 beta(D)^2 and 8 beta(D)<=exp(beta(D)+d0+2). Hence sqrt(C_D)<2 beta(D), and the third term of the displayed maximum dominates both 1 and D sqrt(C_D)/2. The ceiling bound t<=ceil(t)<t+1, together with D>=1 and exp(beta(D)+d0+2)>=1, therefore gives (5/4)exp(beta(D)+d0+2)<=N(D)/D<=(9/4)exp(beta(D)+d0+2). Monotonicity of log places log(N(D)/D) between beta(D)+d0+2+log(5/4) and beta(D)+d0+2+log(9/4).")),
            Paragraph(Text("Since alpha>0, exp(-alpha(D/4)^(1/10)) and exp(-D/4) tend to zero. The standard exponential decay limits also give D/M(D) tending to zero and 1/M(D) tending to zero. Thus, for every fixed real k, (beta(D)+k)/M(D)=1+C(exp(-alpha(D/4)^(1/10))+exp(-D/4))+D/M(D)+(B+k)/M(D) tends to 1. Apply this identity with k=d0+2+log(5/4) and k=d0+2+log(9/4), divide the logarithmic bounds by positive M(D), and use squeeze. This exact application preserves N and every constant; it is exposition of reused scalar and standard limit facts. It implies neither RH nor a sublinear moment count. The separate identification of signedJExpression with the independent original signed-J integral remains open.")))));
}
