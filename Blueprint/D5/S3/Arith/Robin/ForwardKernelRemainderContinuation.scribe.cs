using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ForwardKernelRemainderContinuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernelRemainderContinuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The forward-kernel remainder estimates imply convergence and holomorphy of the Chebyshev partial-summation tail.",
        H("The remainder tail at the infinite endpoint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("remainder-tail-converges"),
                DeclarationHandle.Create(Prefix + "remainder_tail_converges"),
                H("An integrable differentiated tail and a vanishing boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Put E(t)=psi(t)-t and assume that there is a real C satisfying "
                        + "|E(t)|<=C*sqrt(t)*log(t)^2 for every t>=2. Let x0>=3, "
                        + "sigma>-1/5 and A>=0. Suppose complex-valued functions r and dr satisfy "
                        + "|r(t)|<=A*t^(-sigma-7/10) and "
                        + "|dr(t)|<=A*t^(-sigma-17/10) for t>=x0, "
                        + "with dr almost everywhere strongly measurable on (x0,infinity). "
                        + "Then E(t)*dr(t) is absolutely integrable there, and E(t)*r(t) tends "
                        + "to zero as t tends to infinity.")),
                    Paragraph(Text(
                        "Choose eta=(sigma+1/5)/4. The elementary logarithmic estimate gives "
                        + "|E(t)|<=(C/eta^2)*t^(1/2+2*eta). Multiplication by the two "
                        + "assumed kernel bounds gives a boundary majorant proportional to t^p "
                        + "and an integral majorant proportional to t^(p-1), "
                        + "where p=-sigma-1/5+2*eta=-(sigma+1/5)/2<0. "
                        + "These two real-power estimates prove the conclusions. "
                        + "For partial summation, dr may be the derivative of r. The theorem "
                        + "only uses the displayed estimates and measurability; it does not "
                        + "assert that the actual adjoint kernel satisfies them or that its "
                        + "integral is holomorphic."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("remainder-integral-holomorphic"),
                DeclarationHandle.Create(Prefix + "remainder_integral_holomorphic"),
                H("A holomorphic integral under compact parameter bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the same von Koch bound and x0>=3. Let d(s,t) be "
                        + "holomorphic in s on Re(s)>-1/5 for each t>x0, and assume "
                        + "that d(s,t) and its complex parameter derivative are almost "
                        + "everywhere strongly measurable in t for each such s. "
                        + "Suppose every compact set K in this half-plane has a constant A>=0 "
                        + "such that |d(s,t)|<=A*t^(-Re(s)-17/10) for all s in K and t>=x0. "
                        + "Then integral_(x0,infinity) E(t)*d(s,t) dt is holomorphic on "
                        + "Re(s)>-1/5.")),
                    Paragraph(Text(
                        "At a fixed parameter s choose r=(Re(s)+1/5)/4. The closed ball "
                        + "of radius 2*r about s lies in the half-plane. Throughout this ball "
                        + "Re(z)>=sigma=Re(s)-2*r>-1/5. For y within radius r of s, "
                        + "Cauchy's estimate on the circle of radius r about y bounds "
                        + "the parameter derivative of d(y,t) by "
                        + "(A/r)*t^(-sigma-17/10). The preceding convergence theorem makes "
                        + "this bound integrable after multiplication by |E(t)|. "
                        + "Differentiation under the Lebesgue integral proves the conclusion. "
                        + "This theorem applies to a family once its stated kernel estimates "
                        + "and regularity are supplied; it does not supply those estimates "
                        + "for the actual adjoint kernel."))),
                DescribeRole.Theorem))));
}
