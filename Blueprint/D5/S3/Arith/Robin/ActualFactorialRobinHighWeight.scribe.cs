using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualFactorialRobinHighWeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual complete factorial high dyadic weight is positive, strictly decreasing and vanishing; it pays convergence of the ordinary odd Mobius natural prefixes.",
        H("Actual High Dyadic Weight and Ordinary Odd Mobius Convergence"),
        Blocks(
            Paragraph(Text(
                "Set h(r)=ActualFactorialRobinHighDerivative.highRemainder(r), c=log(2), "
                + "and q(r)=h(r)-h(r+c)/2. The derivative is the literal signed difference "
                + "highRemainderDerivative(r)-highRemainderDerivative(r+c)/2. "
                + "Neither the floor factorial nor a replacement envelope is differentiated.")),
            Describe.Lean(
                DescribeId.Create("actual-factorial-robin-high-weight"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualFactorialRobinHighWeight.result"),
                H("Signed derivative and its anchored natural-prefix consumer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every r>0, q(r)>0, q has the actual signed derivative, and that "
                        + "derivative is strictly negative. Consequently q is strictly antitone "
                        + "on the whole positive half-line and tends to zero at infinity.")),
                    Paragraph(Text(
                        "Use the original positive cumulative mass C(Y)=integral from 1 to Y "
                        + "of eta(y)/y^2. With K2(t)=t^(-2)+2*t^(-3) and "
                        + "K3(t)=2*t^(-3)+6*t^(-4), set Qj(t)=Kj(t)-Kj(t+c)/2. "
                        + "Both Q2 and Q3 are positive for t>0. The full y representation "
                        + "is q(r)=integral over y>1 of C(y)*Q2(r+log(y))/y. "
                        + "Its derivative is minus the integral of C(y)*Q3(r+log(y))/y.")),
                    Paragraph(Text(
                        "Local differentiation is dominated on r/2<s<3*r/2 by "
                        + "(2*(r/2)^(-1)+6*(r/2)^(-2))*C(y)*J(r/2,y), where "
                        + "J(a,y)=K2(a+log(y))/y and the original supplier already proves "
                        + "this complete baseline integrable. Derivative measurability follows "
                        + "by multiplying the integrable baseline by the measurable kernel ratio. "
                        + "Strict signs use positive-measure support on (1,2). The derivative "
                        + "identity is matched to the original signed HasDerivAt by uniqueness. "
                        + "The original upper budget gives 0<q(r)<=2*(r^(-1)+r^(-2)), "
                        + "which pays decay.")),
                    Paragraph(Text(
                        "For every natural D>=2 and M>D, including M in the sum, "
                        + "the actual odd tail has absolute value at most 4*q(log(D+1)). "
                        + "C's anchored finite Abel estimate is applied only after proving "
                        + "nonnegativity and antitonicity of m↦q(log(m)) on every member "
                        + "of the entire interval [D+1,M]. The prefix is the sum over "
                        + "odd 3<=m<N of mu(m)*q(log(m))/m. Its difference between "
                        + "prefix(M+1) and prefix(D+1) equals the complete tail (D,M]. "
                        + "The bound tending to zero makes these natural prefixes Cauchy; "
                        + "completeness of the reals gives their ordinary sequential limit.")),
                    Paragraph(Text(
                        "The live consumers are the negative-derivative proof, strict "
                        + "antitonicity, the complete finite tail bound and the Cauchy proof. "
                        + "ActualFactorialCumulativePositivity owns all original cumulative "
                        + "positivity, integrability and high-representation suppliers; "
                        + "ActualOddHarmonicMobiusTail owns the harmonic arithmetic and "
                        + "inclusive anchored Abel budget. Mathlib supplies dominated "
                        + "differentiation, derivative uniqueness, mean value monotonicity "
                        + "and completeness. The estimates are repository-derived; no "
                        + "literature priority is asserted.")),
                    Paragraph(Text(
                        "This is ordinary convergence of natural prefixes. No real Summable, "
                        + "unconditional summability or absolute interchange of the signed "
                        + "family is asserted. The strict negative infinite high pairing is "
                        + "unproved. LowPrimitive, both x-versus-m and N+1-versus-2m "
                        + "clipping boundaries, the original unit, finite terminal term "
                        + "and actual positive integer pressure remain unpaid. The full "
                        + "obligation Ipsi(log(n))+R(log(n))+d_n>0 for all n>5040 remains "
                        + "open; removing d_n is false at 5041. RH, FIB/3D and PR14823 "
                        + "are the same continuing program."))),
                DescribeRole.Theorem))));
}
