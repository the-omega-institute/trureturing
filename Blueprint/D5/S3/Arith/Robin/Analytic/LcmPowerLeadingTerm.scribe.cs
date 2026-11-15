using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LcmPowerLeadingTermDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The leading asymptotic coefficient of the LCM power threshold at a fixed real parameter.",
        H("The scaled threshold limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-threshold"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.normalizedF"),
                H("The inverse-power coordinate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With N(t)=(x-t)^kappa-(1-t)^kappa, the normalized expression is "
                    + "log(N(t)/N(x*t))/(kappa*log(x)). For kappa>1 and x>1, at t=0 its value is zero, "
                    + "and its derivative is c(kappa,x)."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("threshold-normalization"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.lcmPowerF_normalized"),
                H("Exact normalization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For x>1 and a positive natural n, the original lcmPowerF from Definition 4.2 "
                    + "equals the normalized expression at t=1/x^n. Factoring x^n from "
                    + "each power base and cancelling its nonzero kappa power proves the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scaled-threshold-limit"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.lcmPowerF_scaled_limit"),
                H("Fixed-parameter leading term"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each real kappa>1 and x>1, F(kappa,x,n)*x^n tends to "
                        + "c(kappa,x)=(x-1)*(x^(kappa-1)-1)/((x^kappa-1)*log(x)) as "
                        + "the natural n tends to infinity.")),
                    Paragraph(Text(
                        "The normalized function is differentiable at zero with this derivative. "
                        + "Its difference quotient converges along the positive sequence 1/x^n. "
                        + "This proves the fixed-parameter limit. It does not assert a uniform "
                        + "second-order error estimate or limits of parameter derivatives.")),
                    Paragraph(Text(
                        "The collision argument applies the intermediate value theorem using "
                        + "the leading limits at two fixed parameter endpoints. It therefore "
                        + "does not require the uniform remainder estimate of Lemma 3.1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("threshold-parameter-continuity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.continuousOn_lcmPowerF"),
                H("Continuity in the parameter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At x>1 and a positive natural exponent, the numerator and denominator "
                    + "power differences are positive for kappa>1. Their quotient, logarithm, "
                    + "and division by kappa*log(x) are continuous throughout that interval."))),
                DescribeRole.Theorem))));
}
