using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class SmoothedChebyshevTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact smoothing transfer for Chebyshev error",
        H("An exact smoothing transfer for Chebyshev error"), Blocks(
            Describe.Lean(DescribeId.Create("smoothed-chebyshev-integrated-u"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SmoothedChebyshevTransfer.psi1_div_sub_half_eq_integrated_U"),
                H("The finite-interval transfer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "For every real x at least one, psi1(x)/x - x/2 equals " +
                        "U(x) - (2/x) integral from 1 to x of U(t) dt " +
                        "- (3/2 + gamma)/x. Here gamma is the Euler-Mascheroni constant, " +
                        "psi1(x) is the integral of Chebyshev psi from 1 to x, and " +
                        "U(x) = x times the sum of Lambda(n)/n for 1 <= n <= x, " +
                        "minus psi(x), minus x log(x), plus (1 + gamma)x.")),
                    Paragraph(Text(
                        "Each Mangoldt ramp Lambda(n) max(t/n - 1, 0) has integral " +
                        "Lambda(n)(x-n)^2/(2n) when 1 <= n <= x. A single finite " +
                        "support works throughout the integration interval. The ramp " +
                        "vanishes at its entry point, so integer and prime-power endpoints " +
                        "require no correction. Integrating t log(t) gives the lower-endpoint " +
                        "term (3/2 + gamma)/x. At x = 1 both sides equal -1/2.")),
                    Paragraph(Text(
                        "This identity transfers integrated estimates for U to the " +
                        "smoothed Chebyshev error without a new contour integral. " +
                        "It is unconditional. Bounds for the transformed zero series and " +
                        "for nonprincipal character sums are separate estimates."))),
                DescribeRole.Theorem))));
}
