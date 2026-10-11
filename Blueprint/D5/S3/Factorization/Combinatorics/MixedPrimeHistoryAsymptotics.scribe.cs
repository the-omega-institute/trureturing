using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class MixedPrimeHistoryAsymptoticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed Prime History Asymptotics.",
        H("Mixed Prime History Asymptotics"),
        Blocks(
            Paragraph(Text(
                "For a fixed positive real t, w_t(n) is the frozen weightedCount: the sum "
                + "of t to the history length over all typed mixed prime histories ending "
                + "at n. Endpoint zero has weight zero and endpoint one has weight one. "
                + "P(z) is the prime-supported sum of z to the power q. F_t(z) is the "
                + "ordinary generating series of the actual endpoint weights, and its "
                + "numerator is z plus t times the prime sum of F_t(z to the power q). "
                + "Infinite-series identities are used only on proved convergence disks.")),
            Describe.Lean(
                DescribeId.Create("mixedprimehistoryasymptotics-subcritical-bound"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryAsymptotics.subcritical_bound"),
                H("One bound for all actual endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive real t and every real r with zero less than r less "
                    + "than one and t P(r) less than one, there exists a positive real B "
                    + "such that w_t(n) times r to the power n is at most B for every "
                    + "natural n. B is chosen before n.")),
                    Paragraph(Text(
                    "Grouping each finite history fibre by length transports the frozen "
                    + "last-letter length recurrence to the weighted count. Additive terms "
                    + "are controlled by P(r). Each multiplicative predecessor is at most "
                    + "half the endpoint and there are at most n distinct prime divisors. "
                    + "Their total normalized contribution is bounded by n times the nth "
                    + "power of the square root of r, which tends to zero. A finite initial "
                    + "sum supplies B, and strong induction propagates it to every endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixedprimehistoryasymptotics-result"),
                DeclarationHandle.Create("D5/S3/Factorization/Combinatorics/MixedPrimeHistoryAsymptotics.result"),
                H("A positive single-pole asymptotic and bounds for all positive endpoints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive real t there exist real rho, C, R, K, cLow and cHigh "
                    + "with zero less than rho less than R less than one, C positive, K "
                    + "positive, and zero less than cLow at most cHigh. They satisfy "
                    + "t P(rho) = 1; every sigma strictly between zero and one satisfying "
                    + "t P(sigma) = 1 equals rho. For every natural n, "
                    + "abs(w_t(n) - C/rho^n) is at most K/R^n. For every natural n at least "
                    + "one, cLow/rho^n is at most w_t(n), which is at most cHigh/rho^n. "
                    + "All six constants are chosen before the endpoint quantifier. This "
                    + "includes the critical-root assertion and the exponential error and "
                    + "two-sided clauses of the single-pole asymptotic.")),
                    Paragraph(Text(
                    "The common subcritical bound makes F_t analytic on the critical disk. "
                    + "For a nonnegative a with a squared less than a subcritical r, one "
                    + "and the same B controls every prime q and every point of the closed "
                    + "a disk by abs(F_t(z^q)) at most B a^q/(r-a^2). This summable "
                    + "majorant makes the numerator analytic on the square-root-rho disk. "
                    + "Absolute convergence and the actual weighted recurrence yield "
                    + "(1-t P(z)) F_t(z) equal to that numerator, including the initial "
                    + "coefficients at zero and one.")),
                    Paragraph(Text(
                    "Finite sets of primes and strict increase establish the unique root. "
                    + "The derivative P'(rho) is a positive real number. Nonnegative "
                    + "boundary deficits, especially the prime two and prime three terms, "
                    + "exclude all other denominator zeros on the closed critical disk. "
                    + "A divided difference takes the derivative value at rho, and compactness "
                    + "gives a larger disk where it stays nonzero. The positive numerator "
                    + "value b gives C = b/(t rho P'(rho)). A second divided difference "
                    + "constructs an analytic remainder after subtracting C/(1-z/rho). "
                    + "Mathlib's Cauchy series, coefficient uniqueness and radius bound "
                    + "give the uniform error. Frozen reachability gives positive weights; "
                    + "the convergent normalized sequence and its positive limit form a "
                    + "compact set bounded away from zero, yielding the all-endpoint lower bound.")),
                    Paragraph(Text(
                    "The pole subtraction and Cauchy estimate are classical analytic "
                    + "combinatorics. The repository-specific obligation is the common "
                    + "global control derived for these actual weighted histories; no "
                    + "external open-problem resolution or literature novelty is claimed."))),
                DescribeRole.Theorem))));
}
