using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio.Compression;

internal sealed class OptimalLossDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/Compression/OptimalLoss.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quadratic scale of the original compact compression loss is necessary.",
        H("Optimal order of the compact loss"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("endpoint-excess"),
                DeclarationHandle.Create(Prefix + "endpointExcess"),
                H("The excess at the singleton window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Set r=n+1 and s=n. The only legal integer parameter is b=0, "
                    + "so the compact gcd is (n!)^(n+1). The tail has degree n(n+2) "
                    + "and cutoff n. For n>=1 the tail divides this gcd, and endpointExcess "
                    + "is the resulting positive integer quotient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("endpoint-loss-limit"),
                DeclarationHandle.Create(Prefix + "endpoint_loss_tendsto"),
                H("The exact limiting constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "As n tends to infinity through the natural numbers, "
                        + "log(endpointExcess(n))/(n+1)^2 tends to the Euler-Mascheroni "
                        + "constant gamma. Thus log E=gamma r^2+o(r^2) along s=r-1. "
                        + "Since gamma>1/2, a uniform loss estimate o(r^2) over the "
                        + "original compact windows is impossible.")),
                    Paragraph(Text(
                        "The exact finite tail estimate compares its centered logarithm "
                        + "D(n+2,n) with the complete Mangoldt error U(n+2). Their difference "
                        + "lies between zero and psi(n+2)/n. The bound "
                        + "psi(y)<=(log 4+4)y makes this difference negligible after division "
                        + "by n+1. The weighted Mangoldt limit "
                        + "sum_{m<=y} Lambda(m)/m-log y -> -gamma and the prime number "
                        + "theorem psi(y)/y -> 1 give U(y)/y -> 0.")),
                    Paragraph(Text(
                        "For the numerator, the logarithmic factorial bounds leave an error "
                        + "at most log(n+2)+1 beyond n log n-n. The remaining logarithmic "
                        + "terms are multiples of log(n/(n+2)) and log(n+2)/(n+1), "
                        + "both tending to zero. The constant term left by the tail "
                        + "normalization is gamma."))),
                DescribeRole.Theorem))));
}
