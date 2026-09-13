using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class UpperHalfPrimeCertificateExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Upper-half Prime Certificate Extension.",
        H("Upper-half Prime Certificate Extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("upperhalfprimecertificateextension-certificate-extension"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/UpperHalfPrimeCertificateExtension.certificate_extension"),
                H("The exact change of two absolute Mobius certificates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let Q be a positive squarefree integer and N an integer at least two. "
                    + "Choose a finite set T of primes p with N less than twice p, p at most N, "
                    + "and p not dividing Q. Write R for their product, s for their number, "
                    + "and b for the Mobius sum over divisors of Q at most N. The certificate U "
                    + "sums absolute truncated kernels over all positive coprime indices at most N; "
                    + "W further restricts these indices to squarefree integers. Both differences, "
                    + "from support Q to support QR, equal s plus the absolute value of b minus "
                    + "the absolute value of (b minus s). This includes the empty set and Q equal to one. "
                    + "The new divisors in the window and the deleted coprime outer indices are "
                    + "exactly T. Every retained index other than one has the same truncated kernel."))),
                DescribeRole.Theorem))));
}
