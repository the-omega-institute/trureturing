using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot.SmallPrimes;

internal sealed class SmallPrimeFiniteRangeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimitiveRoot/SmallPrimes/FiniteRange.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite prime primitive-root range",
        H("The finite prime primitive-root range"), Blocks(
            Describe.Lean(DescribeId.Create("small-prime-primitive-root"),
                DeclarationHandle.Create(Prefix + "small_prime_primitiveRoot"),
                H("A smaller prime primitive root for every small odd prime"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural p, if 3≤p<3483482 and p is prime, there exists " +
                    "a prime q<p with orderOf (q : ZMod p)=p−1. Consecutive odd-slot " +
                    "certificates cover the entire interval. The prime hypothesis " +
                    "excludes every composite-slot witness; the remaining slot supplies " +
                    "the exact order and the smaller prime witness.")),
                Paragraph(Text(
                    "The restriction 3≤p excludes p=2: no prime is strictly below two. " +
                    "The upper endpoint is the exact split used by the analytic " +
                    "large-prime theorem. This finite theorem supplies the small-prime " +
                    "premise of erdos985_of_GRH; it carries no Riemann-hypothesis or " +
                    "Dirichlet L-function assumptions. Every block checks literal input " +
                    "inside the Lean kernel. A list of primes supplied by external " +
                    "software is never used as an unproved coverage assumption."))),
                DescribeRole.Theorem))));
}
