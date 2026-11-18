using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LcmPowerLocalFactorBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized prime-power local factor is bounded below by the Euler factor and a uniform Bernoulli correction.",
        H("Bernoulli lower bound for the LCM local factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-local-factor"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.normalizedLocalFactor"),
                H("Normalized local factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real kappa, r, and a this is the normalized local difference "
                    + "(1-r)^(-kappa) ((1-r^(a+1))^kappa-r^kappa(1-r^a)^kappa)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-factor-constant"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.localFactorConstant"),
                H("Uniform correction coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient is c_kappa=kappa/(1-(1/2)^kappa), the uniform replacement "
                    + "for kappa/(1-r^kappa) when 0<=r<=1/2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-factor-lower-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLocalFactorBound.local_factor_lower_bound"),
                H("Local factor lower bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For 1<=kappa, 0<=r<=1/2, and 1<=a, the normalized local factor is at least "
                        + "(1-r)^(-kappa)(1-r^kappa)(1-c_kappa*r^(a+1)).")),
                    Paragraph(Text(
                        "The proof uses the tangent-line Bernoulli inequality for the convex map "
                        + "u ↦ u^kappa, the bound (1-r^a)^kappa<=1, and monotonicity of real powers "
                        + "to obtain the uniform coefficient. It isolates the local algebraic core "
                        + "and makes no claim about later Euler products or RH.")),
                    Paragraph(Text(
                        "The Reg source-bound escape audit remains unresolved with "
                        + "unclassified_form:source.observation_data because the source conclusion "
                        + "contains the real variable a in multiple coupled operands. The unresolved "
                        + "registration is tracked at https://github.com/the-omega-institute/trureturing/issues/30238; "
                        + "no declared_validated certificate is claimed."))),
                DescribeRole.Theorem))));
}
