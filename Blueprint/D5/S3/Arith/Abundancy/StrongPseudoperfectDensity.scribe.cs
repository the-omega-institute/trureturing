using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class StrongPseudoperfectDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/StrongPseudoperfectDensity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mccormackzelinsky2023weightedamgm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strongly pseudoperfect positive integers have natural density zero.",
        H("McCormack and Zelinsky's Question 43"),
        Blocks(
            Describe.Lean(DescribeId.Create("strongly-pseudoperfect"),
                DeclarationHandle.Create(Prefix + "StronglyPseudoperfect"),
                H("Complementary divisor sums"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A positive integer n is strongly pseudoperfect "
                    + "when a subset S of its positive divisors is closed under "
                    + "d maps to n/d and the sum of its elements is 2n. "
                    + "No condition requires 1 or n to belong to S. Positivity "
                    + "excludes zero, in agreement with Wang and Zelinsky's definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sp-count"),
                DeclarationHandle.Create(Prefix + "spCount"),
                H("Counting positive integers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The count includes exactly the strongly "
                    + "pseudoperfect integers in the closed interval from 1 to X."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Zero natural density"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Question 43 asks: Does SP have positive natural "
                        + "density? The quotient spCount(X)/X tends to zero as the "
                        + "natural number X tends to infinity. Thus the answer is no. "
                        + "Wang and Zelinsky repeat the same question as Question 22.")),
                    Paragraph(Text("Let q be prime with q not dividing m. For a "
                        + "complementary divisor subset S of mq with sum 2mq, put T equal to its "
                        + "intersection with the divisors of m. The disjoint "
                        + "decomposition into T and its complements gives "
                        + "A + qB = 2mq, where A is the sum of d over T and B is "
                        + "the sum of m/d over T. Since A is positive, B is less "
                        + "than 2m and q = A/(2m-B). Consequently at most 2^tau(m) "
                        + "primes q can occur for a fixed m.")),
                    Paragraph(Text("Write Omega for the number of prime factors "
                        + "with multiplicity. The inequalities tau(m) <= 2^Omega(m) "
                        + "and 2^4 < (3/2)^7 give tau(m)^(4/7) <= (3/2)^Omega(m). "
                        + "A finite Euler product and a weak Mertens upper bound "
                        + "give a constant D for which, for X at least three, the sum up to X of "
                        + "(3/2)^Omega(m)/m is at most D*(log X)^(3/2). "
                        + "The factor at the prime two has geometric ratio 3/4.")),
                    Paragraph(Text("For sufficiently large X, put L = log X, a = 15/16, b = 31/32, "
                        + "z = exp(L^b), and Y equal to the integer part of z. "
                        + "The Rankin bound with exponent 1-1/log z counts the "
                        + "integers whose prime factors are at most Y. A finite "
                        + "inverse-square sum bounds integers divisible by q^2 "
                        + "for q greater than Y. Every other integer has a "
                        + "representation mq with q prime, q greater than Y, "
                        + "q not dividing m, and m at most X/(Y+1).")),
                    Paragraph(Text("Cofactors with tau(m) at most L^a contribute "
                        + "at most (X/z)*2^(L^a). The others have reciprocal mass "
                        + "at most L^(-15/28) times the weighted Omega sum. "
                        + "Chebyshev's bound applies at X/m, whose logarithm is "
                        + "at least L^b. After division by X, their contribution "
                        + "is at most a constant times L^(-1/224). The remaining "
                        + "terms are bounded by constants times "
                        + "(1+L^b)*exp(-L^(1/32)), exp(-L^b), and "
                        + "exp((log 2)*L^a-L^b). All four terms tend to zero."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mccormack-zelinsky-2023-question-43"),
                    ResolutionKind.Refuted)))));
}
