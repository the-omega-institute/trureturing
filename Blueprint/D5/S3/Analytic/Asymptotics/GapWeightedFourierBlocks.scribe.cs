using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class GapWeightedFourierBlocksDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Analytic/Asymptotics/GapWeightedFourierBlocks";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Gid, "Long late mesh blocks recover Fourier coefficients uniformly.",
            "evidence-not-specified-by-formal-manifest"),
        H("Fourier recovery on long mesh blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("block-average"),
                DeclarationHandle.Create(Gid + ".blockAverage"),
                H("Gap-weighted block average"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real mesh y, complex samples f and natural indices a and b, "
                    + "sum (y(k+1)−y(k))f(k) over a≤k<b and divide by y(b)−y(a). The quotient is zero when the span is zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("eventually-block-average-modulated-series"),
                DeclarationHandle.Create(Gid + ".eventually_blockAverage_modulated_series"),
                H("Uniform recovery at a chosen frequency"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let y be a strictly increasing real mesh with gaps tending to zero. "
                        + "Let c(i) be absolutely summable complex coefficients on an arbitrary "
                        + "index type with real frequencies f(i). Suppose the samples s(k) differ "
                        + "from the sum of c(i) exp(i f(i)y(k)) by an error tending to zero. "
                        + "For each real ν and each ε>0 there exist an index A and a span H>0. "
                        + "For every A≤a<b with y(b)−y(a)≥H, the gap-weighted block average of "
                        + "s(k) exp(−iνy(k)) differs from the sum of c(i) over f(i)=ν by at most ε.")),
                    Paragraph(Text(
                        "At a nonzero shifted frequency μ, comparison with the phase primitive "
                        + "bounds the normalized contribution by 2/(|μ|(y(b)−y(a))) plus "
                        + "|μ| times the largest gap in the block. The boundary term comes from "
                        + "telescoping the primitive. Use this estimate for a finite set of "
                        + "frequencies and bound the rest by their absolute coefficient mass. "
                        + "The total gap weight is the block span, so a uniform bound on the "
                        + "late sample errors also bounds their normalized contribution."))),
                DescribeRole.Theorem))));
}
