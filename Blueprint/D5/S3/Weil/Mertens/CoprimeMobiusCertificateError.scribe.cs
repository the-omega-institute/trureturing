using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class CoprimeMobiusCertificateErrorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The error of the coprime Mobius certificate.",
        H("A uniform error for a truncated Mobius sum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coprime-mobius-certificate-error"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/CoprimeMobiusCertificateError.certificate_error"),
                H("The explicit divisor bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a squarefree integer R greater than one, sum the absolute truncated Mobius "
                    + "kernel over every positive integer at most N that is coprime to R. Its difference "
                    + "from c(R) times N has absolute value at most twice the number of divisors of R "
                    + "times the sum of the absolute partial Mobius sums on consecutive divisor intervals. "
                    + "Here c(R) is the coprime density times the sum of those absolute partial sums "
                    + "weighted by the differences of reciprocal endpoints. The bound holds for every "
                    + "natural number N, including zero."))),
                DescribeRole.Theorem))));
}
