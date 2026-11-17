using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MellinPolynomialGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MellinPolynomialGrowth.";
    private const string ResiduePrefix = "D5/S3/Arith/Robin/ForwardKernel/MellinResidue.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial growth of the Mellin remainder.",
        H("Polynomial growth of the Mellin remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adjoint-kernel-fixed-compact-interval"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.adjointKernel_eq_fixed"),
                H("A fixed compact interval for the adjoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If both the starting center x0 and evaluation point t are at most b, the Mellin adjoint equals its center integral on [x0,b]. The kernel vanishes for larger centers. This representation bounds the initial corrections uniformly throughout a vertical strip."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-response-compact-integrable"),
                DeclarationHandle.Create(ResiduePrefix + "forwardResponse_compact_integrable"),
                H("Integrability on bounded intervals of centers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the complete Chebyshev error is eventually bounded by a nonnegative real power, the complete forward response is integrable on every compact interval whose lower endpoint is at least three. The global power estimate for the response supplies an integrable continuous majorant on that interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-kernel-mellin-explicit-remainder"),
                DeclarationHandle.Create(ResiduePrefix + "forward_kernel_mellin_explicit_remainder"),
                H("The explicit common remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For x0 at least three, put y=max(4,x0) and a=max(9,endpoint(y)). The remainder is the Mellin integral of the response on [x0,y], plus the finite signed correction at a, minus E(a)r_s(a), minus the integral of E(t)r_s'(t) on (a,infinity). Under an eventual power bound with exponent alpha, this same function is holomorphic on Re(s)>alpha-7/10 and gives the Mellin identity on Re(s)>max(1/2,alpha-3/10). Its formula does not depend on alpha."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-kernel-mellin-polynomial-remainder"),
                DeclarationHandle.Create(Prefix + "forward_kernel_mellin_polynomial_remainder"),
                H("Quadratic growth in closed vertical strips"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume |psi(t)-t| is eventually bounded by C sqrt(t) log(t)^2. For every x0 at least three, one common explicit remainder R is holomorphic on Re(s)>-1/5 and satisfies F(s)=-zeta'(s+1/2)/(2 zeta(s+1/2))-1/(2(s-1/2))+R(s) for Re(s)>1/2. For each margin delta strictly between zero and one fifth, R(s) is bounded by C_delta(1+|Im(s)|)^2 whenever -1/5+delta<=Re(s)<=1. Relative powers and their time derivatives have strip bounds independent of the imaginary part except for the indicated polynomial factors. Compact contributions are uniformly bounded using the real part of each Mellin exponent. A small positive power absorbs the logarithmic factors in the Chebyshev error and gives an integrable majorant for the tail. All half-plane and strip estimates concern the same explicit R."))),
                DescribeRole.Theorem))));
}
