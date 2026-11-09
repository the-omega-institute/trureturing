using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class DyadicMacroMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive powers of a common logarithmically sampled dyadic scale have strictly positive covariance.",
        H("Macroscopic dyadic moments"),
        Blocks(
            Paragraph(Text(
                "Let U have density 1/(u log 2) on [1,2], and define "
                + "M(gamma) as the integral of u^gamma against this probability measure. "
                + "This integral definition also includes gamma=0, where M(0)=1.")),
            Describe.Lean(
                DescribeId.Create("dyadic-macro-moment"),
                DeclarationHandle.Create(Prefix + "dyadicMacroMoment"),
                H("Moment of the logarithmic dyadic scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real exponent gamma, dyadicMacroMoment(gamma) is the "
                    + "integral of u^gamma against du/(u*log(2)) on [1,2]. "
                    + "In particular, its value at gamma=0 is one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dyadic-macro-moment-eq"),
                DeclarationHandle.Create(Prefix + "dyadic_macro_moment_eq"),
                H("Evaluation of positive power moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For gamma>0, M(gamma)=(2^gamma-1)/(gamma log 2). "
                    + "Normalize the logarithmic integral and integrate u^(gamma-1) "
                    + "between 1 and 2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-macro-moment-pos"),
                DeclarationHandle.Create(Prefix + "dyadic_macro_moment_pos"),
                H("Positivity of power moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For gamma>0, M(gamma)>0: the numerator 2^gamma-1 "
                    + "and the denominator gamma log 2 are both strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-macro-moment-strict-mul"),
                DeclarationHandle.Create(Prefix + "dyadic_macro_moment_strict_mul"),
                H("Strict covariance of two powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a>0 and b>0, M(a)M(b)<M(a+b). "
                        + "Thus two positive powers of the same scale have "
                        + "strictly positive covariance.")),
                    Paragraph(Text(
                        "Write I(t) for the integral of u^t/u over [1,2] and "
                        + "J(u) for the integral of (u^a-v^a)(u^b-v^b)/v over [1,2]. "
                        + "Both powers are strictly increasing, so the inner integrand "
                        + "is nonnegative. At u=2 and v=1 it is strictly positive. "
                        + "Continuity gives J(2)>0, then strict positivity of the "
                        + "integral of J(u)/u. Expansion evaluates this last integral "
                        + "as 2(log 2 I(a+b)-I(a)I(b)). Dividing by (log 2)^2 "
                        + "proves the strict moment inequality. The common scale, "
                        + "rather than any additional coupling assumption, supplies "
                        + "this positive covariance."))),
                DescribeRole.Theorem))));
}
