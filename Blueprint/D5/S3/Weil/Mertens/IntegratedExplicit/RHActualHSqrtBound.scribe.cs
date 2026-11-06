using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RHActualHSqrtBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RH supplies a square-root envelope for the complete actual zero series, whose nonconstancy is unconditional.",
        H("A conditional square-root bound for the actual zero kernel"),
        Blocks(
            Paragraph(Text(
                "The existing actualH is the series over every actual nontrivial zeta-zero occurrence, "
                + "including analytic multiplicity and both imaginary signs. With rho(k)=actualZero(k), "
                + "its coefficient is actualCoeff(k)=1/(rho(k)*(1-rho(k))) and its value at real y is "
                + "the sum of actualCoeff(k)*exp(y*rho(k)). The ActualZeroLaplace package supplies "
                + "absolute convergence and a zero imaginary part, so this complex-valued definition "
                + "represents a real-valued kernel. Its value at zero is firstLiMass, which is strictly "
                + "positive. These are the actual analytic zeros, with no additional zero family chosen.")),
            Describe.Lean(
                DescribeId.Create("actual-h-sqrt-bound-of-rh-registered"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/RHActualHSqrtBound.actualH_sqrt_bound_of_rh_registered"),
                H("The full real-axis square-root envelope under RH"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public theorem states the conjunction actualH(0)=actualH(0) and, for "
                        + "every hRH:RiemannHypothesis and every real y, the inequality "
                        + "norm(actualH(y))<=(101/100)*firstLiMass*exp(y/2). The reflexive equality "
                        + "is part of the source statement used by the registration. The bound "
                        + "ranges over all real y, including negative y. On writing x=exp(y)>0, "
                        + "the exponential factor exp(y/2) is the square root of x.")),
                    Paragraph(Text(
                        "RH enters through zeroData_zero_on_critical_line_of_rh, which gives "
                        + "Re(rho(k))=1/2 for each actual occurrence. Thus the norm of each "
                        + "exponential factor is exp(y/2). The coefficient estimate "
                        + "norm(actualCoeff(k))<=Im(rho(k))^(-2), the summability of this "
                        + "inverse-square majorant and the existing height-refined mass bound "
                        + "give the displayed constant 101/100. This theorem consumes RH as "
                        + "an explicit hypothesis; it does not establish RH."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-h-nonconstant"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Mertens/IntegratedExplicit/RHActualHSqrtBound.actualH_nonconstant"),
                H("Unconditional nonconstancy of the actual zero kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exists a real y such that actualH(y) differs from actualH(0). "
                        + "This conclusion has no RH hypothesis. Every actual nontrivial zero "
                        + "has positive real part, so each summand tends to zero as y tends "
                        + "to negative infinity. On the negative half-axis its norm is bounded "
                        + "by norm(actualCoeff(k)); these coefficient norms form a summable "
                        + "majorant. Dominated convergence therefore makes actualH tend to zero "
                        + "at negative infinity. A constant actualH would have value zero, "
                        + "contradicting actualH(0)=firstLiMass>0. The statement is existential "
                        + "and specifies no numerical location for the differing value."))),
                DescribeRole.Theorem))));
}
