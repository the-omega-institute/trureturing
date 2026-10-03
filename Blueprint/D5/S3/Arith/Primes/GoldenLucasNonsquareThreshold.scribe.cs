using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenLucasNonsquareThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd-index Lucas growth crosses an explicit square-obstruction threshold.",
        H("An Explicit Lucas Growth Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-lucas-nonsquare-threshold"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenLucasNonsquareThreshold.golden_lucas_nonsquare_threshold"),
                H("Growth beyond the square-obstruction bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every r at least 119 and every index n at least 2r+1, "
                    + "the square of the Lucas number L_n exceeds 128 times 6^r plus four. "
                    + "The odd-index subsequence grows by a factor of at least five halves "
                    + "at each step. An exact integer comparison at r=119 then places "
                    + "its square above the stated exponential bound, and Lucas "
                    + "monotonicity extends the result to later indices."))),
                DescribeRole.Theorem))));
}
