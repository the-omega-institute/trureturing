using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class MobiusLogFourthDocument : IScribeDocumentDefinition
{
    private const string Path = "D5/S3/Weil/Analytic/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An unconditional fourth-logarithmic bound for the Mertens function",
        H("A Mertens bound from the centered Mangoldt recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mobius-centered-recurrence"),
                DeclarationHandle.Create(Path + "MobiusCenteredHyperbola.sum_log_weighted_moebius"),
                H("The centered finite recurrence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtracting the constant counting weight from von Mangoldt gives a logarithmic "
                    + "Möbius convolution with one boundary unit. A finite Dirichlet hyperbola "
                    + "split writes this convolution as a short sum of Möbius prefixes and a tail "
                    + "involving only differences of the centered Mangoldt prefix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mobius-prefix-fourth-log-bound"),
                DeclarationHandle.Create(Path + "MobiusLogFourth.mobiusPrefix_fourth_log_bound"),
                H("Fourth-logarithmic decay for ordinary Möbius prefixes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real x greater than one, the absolute Möbius prefix is bounded "
                    + "by a constant times x divided by the fourth power of log x. The medium "
                    + "prime number theorem controls the tail at the eighth-root cutoff. "
                    + "Discrete Abel summation and the short head give a contraction of the "
                    + "running normalized envelope."))),
                DescribeRole.Theorem))));
}
