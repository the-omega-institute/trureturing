using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class WeightedTotientEulerDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/WeightedTotientEulerDensity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mccormackzelinsky2023weightedamgm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted totient condition D1 is a strong property among Euler forms.",
        H("McCormack and Zelinsky's Question 45 (#31746)"),
        Blocks(
            Describe.Lean(DescribeId.Create("pseudoperfect"),
                DeclarationHandle.Create(Prefix + "Pseudoperfect"),
                H("Pseudoperfect integers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Pseudoperfect(n) means that a finite subset T of "
                    + "the proper divisors of n has sum n. Positivity is imposed by the "
                    + "counting interval, which excludes zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weight-a"),
                DeclarationHandle.Create(Prefix + "weightA"),
                H("The weighted logarithmic mean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a finite set S and a natural number n, "
                    + "weightA(S,n) is the sum over d in S of (d/(2*n))*log(phi(d)), "
                    + "with the weights, totients and logarithms interpreted in the reals. "
                    + "This is equation (12)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weight-c"),
                DeclarationHandle.Create(Prefix + "weightC"),
                H("The complementary totient sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a finite set S and a natural number n, "
                    + "weightC(S,n) is log of the sum over d in S of phi(n/d)/(2*d). "
                    + "Here n/d inside phi is natural division, and the outer sum and "
                    + "logarithm are real. Divisor membership ensures exact division "
                    + "when this expression is used for D1. This is equation (14)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("d-one"),
                DeclarationHandle.Create(Prefix + "D1"),
                H("The source's D1 property"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("D1(n) requires Pseudoperfect(n) and the existence "
                    + "of a finite subset S of the positive divisors of n with sum 2*n "
                    + "and weightA(S,n) <= weightC(S,n). The independent pseudoperfect "
                    + "conjunct is retained. The set S may contain n and need not contain "
                    + "1 or be closed under complementary divisors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("euler-d-one-count"),
                DeclarationHandle.Create(Prefix + "eulerD1Count"),
                H("Counting D1 Euler forms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("eulerD1Count(X) counts integers n from 1 to X "
                    + "satisfying both EulerForm(n) and D1(n). EulerForm is the existing "
                    + "predicate n=q^s*m^2 with q prime, q and s congruent to one modulo "
                    + "four, m positive, and q coprime to m. It does not impose oddness "
                    + "on m. Integers are counted once regardless of their representations."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("D1 is a strong property"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("As the natural threshold X tends to infinity, "
                        + "eulerD1Count(X)/eulerCount(X) tends to zero. This is precisely "
                        + "the source's definition of a strong property and answers "
                        + "Question 45. Real thresholds reduce to natural-number floors.")),
                    Paragraph(Text("For any prime q and positive r, D1(q*r) implies "
                        + "q <= sigma(r), without a coprimality assumption. If q exceeds "
                        + "sigma(r), the elements of S not divisible by q divide r. "
                        + "Their sum u is less than q, while the total sum 2*q*r and "
                        + "the remaining terms show q divides u. Thus u is zero, and "
                        + "positivity makes that subset empty.")),
                    Paragraph(Text("Consequently S=q*T for a nonempty subset T of the "
                        + "divisors of r. The sum of phi(r/e) over all divisors e of r "
                        + "equals r. It follows that the logarithm argument Z satisfies "
                        + "0 < Z <= r/(2*q) < 1. Hence weightC(S,q*r) is negative. "
                        + "Positive divisors have totient at least one, so weightA is "
                        + "nonnegative, contradicting the D1 inequality.")),
                    Paragraph(Text("For exponent s=1, the prime obstruction bounds q "
                        + "by sigma(m^2). The existing finite images for small and large "
                        + "square factors apply directly. Their cardinalities are at "
                        + "most 3*T^3 and 2*X/(T+1). For every allowed exponent at least "
                        + "five, write s=5+4*j and absorb q^(2*j) into m. The existing "
                        + "high-power image contributes at most sqrt(X). Image cardinalities "
                        + "bound the count without requiring uniqueness of representation.")),
                    Paragraph(Text("With T the integer part of X^(1/6), these bounds "
                        + "give eulerD1Count(X) <= 4*X^(5/6) when X^(1/6) is at "
                        + "least two. For smaller X, the elementary bound eulerD1Count(X) "
                        + "<= X gives the same estimate. Thus it holds for all X at "
                        + "least one. Every "
                        + "prime congruent to one modulo four is an Euler form with "
                        + "s=m=1, giving eulerCount(X) >= exp(-50)*X/log(X) eventually. "
                        + "The ratio is therefore at most 4*exp(50)*log(X)/X^(1/6), "
                        + "which tends to zero. Five also witnesses positivity of the "
                        + "denominator for every X at least five.")),
                    Paragraph(Text("Question 44 concerns complementary-divisor-closed "
                        + "sets. Its density conclusion alone does not imply this one, "
                        + "because D1 imposes no such closure on S."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mccormack-zelinsky-2023-question-45"),
                    ResolutionKind.Proved)))));
}
