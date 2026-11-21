using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class BeriZelinskyQuestion6Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/BeriZelinskyQuestion6.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/berizelinsky2025norton");
    private static readonly LibraryNoteRef GeneralThresholdSource =
        LibraryNoteRef.Create("D5/L/Factorization/zelinsky2023nondeficient");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The difference between Norton and KS strict threshold lengths tends to infinity.",
        H("Norton thresholds and the reciprocal-square perturbation"),
        Blocks(
            Paragraph(Text("Prime enumeration reuses "
                + "D5/S3/Arith/OmegaGreedyPermutation.prime, the zero-based "
                + "Nat.nth Nat.Prime enumeration with prime(0)=2. The source's "
                + "p_n is prime(n-1). Euler factors reuse "
                + "D5/S3/Arith/Robin/GoldenResidualFive.eulerFactor, whose value "
                + "at a natural q is q/(q-1), with real subtraction. Weight "
                + "bounds reuse ZelinskyZhangDoublePrimitive.log_bounds.")),
            Describe.Lean(DescribeId.Create("ks-factor"),
                DeclarationHandle.Create(Prefix + "ksFactor"),
                H("The perturbed Euler factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural q, ksFactor(q) is "
                    + "eulerFactor(q)+1/q^2, with real arithmetic. For a prime q "
                    + "this is the factor in Beri and Zelinsky's definition of KS."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weight"),
                DeclarationHandle.Create(Prefix + "weight"),
                H("The logarithmic Euler weight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural q, weight(q) is "
                    + "log(eulerFactor(q)), using the real logarithm. For prime q, "
                    + "it lies between 1/q and 2/q. Positivity of prime Euler "
                    + "factors makes logarithms preserve their strict crossings."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("perturbation"),
                DeclarationHandle.Create(Prefix + "perturbation"),
                H("The logarithmic perturbation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural q, perturbation(q) is "
                    + "log(1+(q-1)/q^3), with real arithmetic. For prime q, "
                    + "log(ksFactor(q)) equals weight(q)+perturbation(q), and "
                    + "the perturbation lies between 1/(4*q^2) and 1/q^2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("norton-product"),
                DeclarationHandle.Create(Prefix + "nortonProduct"),
                H("Consecutive Norton factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For natural n and k, put s=n-1 using "
                    + "natural subtraction. nortonProduct(n,k) is the product of "
                    + "eulerFactor(prime(i)) over s<=i<s+k. When n>=1 this is "
                    + "the product over the source's primes p_n through p_(n+k-1). "
                    + "The product for k=0 is one. The value at n=0 uses the same "
                    + "starting prime as n=1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ks-product"),
                DeclarationHandle.Create(Prefix + "ksProduct"),
                H("Consecutive perturbed factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For natural n and k, ksProduct(n,k) is "
                    + "the product of ksFactor(prime(i)) over n-1<=i<n-1+k, "
                    + "with natural subtraction in the starting index. It is the "
                    + "source's perturbed product for n>=1, and its empty product "
                    + "is one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a-alpha"),
                DeclarationHandle.Create(Prefix + "aAlpha"),
                H("The strict threshold at alpha"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(GeneralThresholdSource),
                Blocks(Paragraph(Text("For every real alpha and natural n, "
                    + "aAlpha(alpha,n) is the infimum in the natural numbers of "
                    + "the positive lengths k such that nortonProduct(n,k)>alpha. "
                    + "Prime reciprocal divergence makes this set nonempty, so "
                    + "the infimum is its least member. The endpoint estimates "
                    + "and difference conclusions assume alpha>1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a"),
                DeclarationHandle.Create(Prefix + "a"),
                H("Norton's threshold at two"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural n, a(n) is "
                    + "aAlpha(2,n), the least positive number of consecutive prime "
                    + "Euler factors, starting at p_n for n>=1, whose product "
                    + "strictly exceeds two."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ks"),
                DeclarationHandle.Create(Prefix + "KS"),
                H("The KS threshold at two"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural n, KS(n) is the least "
                    + "positive natural k such that ksProduct(n,k)>2. The larger "
                    + "factors guarantee existence and KS(n)<=a(n). The strict "
                    + "inequality defining the crossing is part of the definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("endpoint-bounds"),
                DeclarationHandle.Create(Prefix + "norton_endpoint_bounds"),
                H("The terminal prime has the alpha power scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every real alpha>1 there are positive "
                        + "real constants c and C such that, for all sufficiently "
                        + "large natural n, the final prime Q_n in the product of "
                        + "length aAlpha(alpha,n) satisfies "
                        + "c*p_n^alpha <= Q_n <= C*p_n^alpha. Precisely, "
                        + "p_n=prime(n-1) and "
                        + "Q_n=prime(n-1+aAlpha(alpha,n)-1).")),
                    Paragraph(Text("The Mertens logarithmic Euler-product error "
                        + "is bounded by a constant divided by log(p_n). The "
                        + "first strict crossing exceeds log(alpha) by at most "
                        + "the final logarithmic weight. Subtracting prefix "
                        + "estimates gives log(Q_n)=alpha*log(p_n) plus a bounded "
                        + "error, which yields the two power bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("adjacent-cancellation"),
                DeclarationHandle.Create(Prefix + "norton_adjacent_cancellation"),
                H("Adjacent starting indices force large differences"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every real alpha>1 there is a positive "
                        + "real constant c such that, for all sufficiently large "
                        + "natural n, c*p_n^(alpha-1) is at most "
                        + "aAlpha(alpha,n+1)-aAlpha(alpha,n)+1, where the threshold "
                        + "lengths on the right are cast separately to the reals.")),
                    Paragraph(Text("Subtracting the two crossing sums cancels "
                        + "their common prime interval. The remaining sum is the "
                        + "initial weight w(p_n) plus the difference of the two "
                        + "crossing excesses. Endpoint localization makes the "
                        + "excesses negligible compared with 1/p_n, while each "
                        + "new upper-end weight is at most a constant times "
                        + "p_n^(-alpha). Their number is one plus the difference "
                        + "of the threshold lengths."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Question 6 has an affirmative answer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("As the natural starting index n tends to "
                        + "infinity, the integer a(n)-KS(n) tends to positive "
                        + "infinity. Both natural threshold lengths are cast to "
                        + "the integers before subtraction.")),
                    Paragraph(Text("Write A and B for the terminal primes of "
                        + "the Norton and KS crossings, and P for p_n. Both "
                        + "terminal primes are bounded above and below by positive "
                        + "constant multiples of P^2. The accumulated perturbation "
                        + "through B has a positive lower bound of order "
                        + "1/(P*log(P)), using the finite prime reciprocal-square "
                        + "tail estimate. Subtracting the crossing identities "
                        + "leaves the ordinary weights between B and A, with "
                        + "crossing errors of order P^(-2). Each intervening "
                        + "weight is at most a constant times P^(-2), forcing "
                        + "the number of omitted primes to grow without bound.")),
                    Paragraph(Text("This is the limit in Beri and Zelinsky's "
                        + "Question 6. It does not assert an exact asymptotic "
                        + "equivalence for a(n)-KS(n), or strict a(n)>KS(n) at "
                        + "every positive starting index."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("norton-threshold-differences"),
                    ResolutionKind.Proved)))));
}
