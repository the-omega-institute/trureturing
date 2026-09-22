using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class MixedPrimeHistoryPrimeEndpointBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed Prime Histories Ending at Primes.",
        H("Mixed Prime Histories Ending at Primes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixedprimehistoryprimeendpointbound-prime-endpoint-count-bound"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryPrimeEndpointBound.prime_endpoint_count_bound"),
                H("Counting histories with prime endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let X and k be natural numbers at least two, and let m count the primes at most X. "
                    + "The number of typed additive and multiplicative prime histories of length k "
                    + "ending at these primes is at most m times (2m) to the power k minus one. "
                    + "Every label uses a prime at most X. The final letter must be additive, since "
                    + "a multiplication after a nonempty prefix would produce a composite endpoint. "
                    + "The endpoint and the first k minus one labels therefore determine the final "
                    + "label uniquely. There are m choices for the endpoint and at most 2m choices "
                    + "for each prefix label."))),
                DescribeRole.Theorem))));
}
