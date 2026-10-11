using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class MixedPrimeHistoryAsymptoticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subcritical Control of Mixed Prime Histories.",
        H("Subcritical Control of Mixed Prime Histories"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixedprimehistoryasymptotics-subcritical-bound"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryAsymptotics.subcritical_bound"),
                H("One bound for all endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a positive real length weight t and a real number r strictly between "
                    + "zero and one. Let P(r) be the sum of r to the power q over all primes q. "
                    + "If t P(r) is strictly less than one, there is a positive real B such that "
                    + "the actual sum of t to the history length, over all mixed prime histories "
                    + "ending at n, multiplied by r to the power n, is at most B for every "
                    + "natural n. Endpoint zero has weight zero. The same B controls all endpoints.")),
                    Paragraph(Text(
                    "Grouping the finite history fibre by length transports the last-letter "
                    + "length recurrence to the weighted count. In the normalized recurrence, "
                    + "the additive terms are controlled by P(r). Each multiplicative predecessor "
                    + "is at most half the endpoint, and there are at most n distinct prime "
                    + "divisors. Their total normalized contribution is bounded by n times "
                    + "the nth power of the square root of r. This tends to zero, leaving a "
                    + "strict contraction beyond a fixed threshold. A single finite initial "
                    + "sum supplies B, and strong induction propagates it to every endpoint."))),
                DescribeRole.Theorem))));
}
