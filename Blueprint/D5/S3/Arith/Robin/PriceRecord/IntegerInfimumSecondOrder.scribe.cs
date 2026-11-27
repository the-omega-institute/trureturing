using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class IntegerInfimumSecondOrderDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/IntegerInfimumSecondOrder";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second-order limit of the complete integer Robin infimum on prime prefixes.",
        H("Second-order prime-prefix integer infimum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-integer-infimum-second-order"),
                DeclarationHandle.Create(Gid + ".actual_integer_infimum_second_order"),
                H("The correction tends to −√2(2 + log 2)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each natural cutoff P, let S be the primes at most P, "
                        + "H the sum of their logarithms, ell = log H, and D = √H·ell. "
                        + "Then ell·(D·integerInfimum(S) − 2√2) tends to −√2(2 + log 2) "
                        + "as P tends to infinity. The theorem is unconditional. The integer "
                        + "infimum is over the full image of the baseline-subtracted objective "
                        + "for all natural exponent vectors with exponents at least one on S.")),
                    Paragraph(Text(
                        "At the price 1/(H·ell), the first activation sum splits exactly into "
                        + "the Chebyshev head divided by H·ell and the finite prime-square tail "
                        + "over t < p ≤ P. The real cutoff t solves t² log t = H·ell. "
                        + "The head includes equality. With B = t/√H, the cutoff equation "
                        + "becomes B²(1/2 + log B/ell) = 1. It gives B → √2 and "
                        + "ell·(B − √2) → −√2 log(√2).")),
                    Paragraph(Text(
                        "The quantitative Chebyshev estimate controls the head. The finite "
                        + "prime-square refinement uses F(t) − F(P), where "
                        + "F(x) = 1/(x log x) − 1/(x(log x)²). The upper endpoint "
                        + "and the tail remainder vanish at the scale √H·ell². The head "
                        + "and leading lower endpoint each contribute B at scale D, and "
                        + "the second lower endpoint contributes −B³/ell. The cutoff shift "
                        + "and this second term give the two contributions −√2 log 2 "
                        + "and −2√2.")),
                    Paragraph(Text(
                        "The finite integer activation envelope uses radius 1/√H and trial "
                        + "cutoff H to the power 1/4. The activation sum is eventually below "
                        + "the radius, and the second activation sum and both envelope errors "
                        + "vanish after multiplication by √H·ell². The resulting two-sided "
                        + "estimate transfers the correction to the full infimum."))),
                DescribeRole.Theorem))));
}
