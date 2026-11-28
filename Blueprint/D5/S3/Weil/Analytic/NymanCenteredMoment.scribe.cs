using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanCenteredMomentDocument : IScribeDocumentDefinition
{
    private const string Path = "D5/S3/Weil/Analytic/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero Mellin moment for centered prime dilations",
        H("The centered prime Mellin moment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nyman-centered-prime-cubic-log-bound"),
                DeclarationHandle.Create(Path + "NymanCenteredMomentTail.centeredPrime_log_cube_bound"),
                H("Unconditional decay of the centered prime sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Partial summation transfers fourth-logarithmic Möbius decay to the compact "
                    + "dilation kernel. The centered logarithmic identity then bounds the prime "
                    + "sum by a constant times x divided by the third power of log x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nyman-centered-prime-zero-mellin-moment"),
                DeclarationHandle.Create(Path + "NymanCenteredMoment.integral_centeredPrime_weighted_eq_zero"),
                H("The absolutely convergent zero moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Weighting the centered prime sum by the inverse square of x gives an "
                    + "absolutely convergent integral on the interval from one to infinity. "
                    + "The prime number theorem gives zero normalized residue for the centered "
                    + "Dirichlet series. Mellin factorization and dominated convergence give "
                    + "the value zero for the ordinary integral."))),
                DescribeRole.Theorem))));
}
