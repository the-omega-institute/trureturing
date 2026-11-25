using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class PathRodriguesMangoldtBridgeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The path Rodrigues coefficient LCM and the Mangoldt remainder",
        H("The path Rodrigues coefficient LCM and the Mangoldt remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factorial-complement"),
                DeclarationHandle.Create(Owner + ".contentLCM_eq_factorial_div_tail"),
                H("The exact factorial complement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For natural r ≥ 2 and s ≥ 0, put x = s + 1. Let L(r,x) be the LCM "
                        + "of the coefficient contents C(r − 1,s,k) for integers 0 ≤ k ≤ s. "
                        + "In the natural numbers, L(r,x) is (s!)^r divided by tailLCM(rx − 1,r − 1). "
                        + "The tail is the product over r ≤ k ≤ rx − 1 of the prefix LCMs "
                        + "at the integer quotients floor((rx − 1)/k).")),
                    Paragraph(Text(
                        "Each coefficient content and its complementary path moment multiply "
                        + "to (s!)^r. The gcd of those moments is the tail product. The tail "
                        + "times each content divides (s!)^r, giving one divisibility. "
                        + "In the other direction, (s!)^r divides each moment times the LCM "
                        + "and therefore divides their gcd, which is the tail times the LCM."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-ceiling-correction"),
                DeclarationHandle.Create(Owner + ".T_eq_U_add_ceilingError"),
                H("The signed ceiling correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For r ≥ 2 and integer x > 0, the logarithm of the tail is the sum "
                        + "over 1 ≤ q ≤ x of Λ(q) times (ceil(rx/q) − r). The count comes from "
                        + "the integers k ≥ r with qk ≤ rx − 1. Dividing by r gives "
                        + "x times the sum of Λ(q)/q, minus ψ(x), plus E(r,x)/r. "
                        + "Here E(r,x) is the sum of Λ(q) times (ceil(rx/q) − rx/q) "
                        + "over the same q.")),
                    Paragraph(Text(
                        "Write γ for Euler's constant and T(r,x) for "
                        + "log((x − 1)!) − x log x + (1 + γ)x − log L(r,x)/r. "
                        + "The complete Mangoldt remainder U satisfies T(r,x) = U(x) + E(r,x)/r. "
                        + "The ceiling error lies between 0 and ψ(x). At r = x ≥ 2 the "
                        + "difference T(x,x) − U(x) therefore lies between 0 and log 4 + 4."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-gamma-threshold"),
                DeclarationHandle.Create(Owner + ".diagonal_gamma_threshold"),
                H("The two-sided diagonal inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every integer x ≥ 2, put G(x) = γx − log L(x,x)/x. "
                        + "Then G(x) + 1 − log x − (log 4 + 4) ≤ U(x) ≤ G(x) + 1. "
                        + "Left and right unit-cell sums for log bound the factorial term "
                        + "between γx + 1 − log x and γx + 1. Combining these bounds "
                        + "with the signed ceiling correction gives the two inequalities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pointwise-window-transfer"),
                DeclarationHandle.Create(Owner + ".contentLCM_gamma_blocks_of_pointwise_windows"),
                H("Transfer from real windows to all integers in a block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose that for every real δ > 0 and every real R there is "
                        + "a Y ≥ max(R,1) with U(t) ≤ t^(1/2+δ) for every real "
                        + "t in [Y,Y^(3/2)]. Then for every real ε > 0 and natural A "
                        + "there is a natural k ≥ max(A,2) such that "
                        + "γx² − x^(3/2+ε) ≤ log L(x,x) for every integer "
                        + "x in [k^12,k^16].")),
                    Paragraph(Text(
                        "Choose δ = ε/2 and a sufficiently late real window to absorb "
                        + "the additive logarithm and constant in the lower bound for U. "
                        + "The quartic block placement fits the entire interval "
                        + "[k^12,k^16] in that window."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cofinal-gamma-blocks"),
                DeclarationHandle.Create(Owner + ".rh_iff_cofinal_contentLCM_gamma_blocks"),
                H("The cofinal gamma-block criterion for RH"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Riemann hypothesis holds exactly when for every ε > 0 and natural A "
                        + "there is a natural k ≥ max(A,2) with "
                        + "γx² − x^(3/2+ε) ≤ log L(x,x) at every integer "
                        + "x in [k^12,k^16]. Under RH the pointwise Mangoldt window "
                        + "criterion supplies the real windows for the transfer.")),
                    Paragraph(Text(
                        "Conversely, sample at x = n^4 for each k³ ≤ n ≤ k⁴. "
                        + "The upper inequality for U converts the gamma bound "
                        + "with ε = κ/2 into U(n^4) ≤ (n^4)^(1/2+κ) "
                        + "on sufficiently late blocks for every κ > 0. "
                        + "The quartic integer criterion then gives RH."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Arith/FactorialRatio/PathRodriguesGcd")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtPointwiseWindows")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling"))
        ]));
}
