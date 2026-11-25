using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class PrimeContactTransportDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactTransport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime weights and integer transport of a signed contact graph",
        H("Prime weights and integer transport of a signed contact graph"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("contact-rational-normalization"),
                DeclarationHandle.Create(Module + ".normalize_real_kernel"),
                H("A connected real kernel has rational coordinate ratios"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A two-contact row transports one column coefficient to another by "
                    + "a signed ratio of coordinate weights. With rational nonzero weights, "
                    + "a connected real solution divided by its nonzero root value has "
                    + "rational, nowhere-zero coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("contact-prime-potential"),
                DeclarationHandle.Create(Module + ".real_prime_kernel_iff_potential"),
                H("Distinct primes detect the integer exponent potential"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use pairwise distinct primes as coordinate weights. Valuation at "
                        + "each of these primes sends multiplication of nonzero rational "
                        + "numbers to addition of integers and sends the corresponding "
                        + "prime to its coordinate basis vector. Along a two-contact row "
                        + "the potential gains the source axis and loses the target axis. "
                        + "The sign of the rational coordinate gives the simultaneous "
                        + "transport of the two-element multiplicative sign group.")),
                    Paragraph(Text(
                        "Conversely, the signed integer potential gives a nonzero kernel "
                        + "by evaluating the Laurent monomial attached to each column."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("contact-uniform-laurent-kernel"),
                DeclarationHandle.Create(Module + ".exists_laurent_kernel_of_real_prime_kernel"),
                H("One prime specialization gives the uniform Laurent family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The integer gains and signs obtained at the prime weights "
                        + "are independent of subsequent weight choices. Every vector "
                        + "of nonvanishing real weights therefore admits the same "
                        + "signed Laurent monomial construction.")),
                    Paragraph(Text(
                        "For the paired-column boundary of a balanced cubic nine-cube "
                        + "support, this identifies the connected two-contact branch "
                        + "with integer coordinate transport. It reduces the all-weight "
                        + "kernel condition to a geometric constraint on the contact "
                        + "graph in Hong, Wu and Xia's Problem 2. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
