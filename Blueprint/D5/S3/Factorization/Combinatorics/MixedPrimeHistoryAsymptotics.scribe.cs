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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixedprimehistoryasymptotics-subcritical-analytic-control"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryAsymptotics.subcritical_analytic_control"),
                H("Analyticity and common control of prime compositions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same positive t, zero less than r less than one, and t P(r) "
                    + "less than one hypotheses, choose B once. It bounds every normalized "
                    + "endpoint weight. The actual generating function F is analytic on the "
                    + "open disk of radius r. For every nonnegative a with a squared less "
                    + "than r, every prime q, and every complex z of modulus at most a, "
                    + "the modulus of F(z to the power q) is at most B times a to the power q "
                    + "divided by r minus a squared. The numerator z plus t times the sum "
                    + "of these prime compositions is analytic on the open disk of radius "
                    + "the square root of r. B is chosen before a, q, and z."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixedprimehistoryasymptotics-functional-equation"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryAsymptotics.subcritical_functional_equation"),
                H("The last-letter functional equation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive t and zero less than r less than one with t P(r) less than "
                    + "one, every complex z of modulus less than r satisfies "
                    + "(1 - t P(z)) F(z) = z + t times the sum of F(z to the power q) over primes q. "
                    + "F is the ordinary generating series of the actual weighted histories. "
                    + "The initial coefficient at endpoint one contributes z; endpoint zero "
                    + "contributes zero. Absolute convergence justifies the Cauchy product "
                    + "for additive letters and the divisor reindexing for multiplicative letters."))),
                DescribeRole.Theorem))));
}
