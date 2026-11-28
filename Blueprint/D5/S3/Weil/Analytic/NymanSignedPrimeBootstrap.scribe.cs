using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Analytic;

internal sealed class NymanSignedPrimeBootstrapDocument : IScribeDocumentDefinition
{
    private const string Path = "D5/S3/Weil/Analytic/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A centered prime-dilation criterion for the Riemann hypothesis",
        H("A centered prime-dilation criterion for the Riemann hypothesis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-dilation-centering"),
                DeclarationHandle.Create(Path + "NymanPrimeDilations.primeDilations_add_shell_eq_centered"),
                H("Centering by the integer counting weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Möbius inversion evaluates the sum of all integer dilations of the shell. "
                    + "At scales at least one, subtracting the integer counting weight from the "
                    + "prime logarithm weight changes the prime sum by exactly one copy of the shell."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-correction-envelope"),
                DeclarationHandle.Create(Path + "NymanLogCorrectionEnvelope.abs_logCorrection_le_envelope"),
                H("The logarithmic correction on earlier scales"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The logarithmic moment of the four-box kernel is a sum of exponentially "
                    + "weighted dilations and integrals. For a power envelope with exponent "
                    + "at least one half, these operations cost at most four times log(7/6) plus sixteen."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-centered-signed-prime-growth"),
                DeclarationHandle.Create(Path + "NymanSignedPrimeBootstrap.rh_iff_signedPrimeSquareRoot"),
                H("Equivalence with a one-sided prime bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Riemann hypothesis holds exactly when the adverse part of the centered "
                    + "prime-dilation sum is eventually bounded by a constant times x to the power "
                    + "one half plus epsilon, times log x, for every positive epsilon. "
                    + "At each scale the sign comes from the Möbius shell at that scale. "
                    + "The prime-power and kernel corrections are absorbed by the running power envelope."))),
                DescribeRole.Theorem))));
}
