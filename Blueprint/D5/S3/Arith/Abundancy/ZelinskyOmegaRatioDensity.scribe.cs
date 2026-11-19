using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyOmegaRatioDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/zelinsky2021totalprimefactors");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every fixed prime-factor inequality has positive lower relative density in Euler forms.",
        H("Zelinsky's Conjecture 1 on prime-factor restrictions"),
        Blocks(
            Describe.Lean(DescribeId.Create("prime-factor-restriction"),
                DeclarationHandle.Create(Prefix + "OR"),
                H("The prime-factor inequality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For real alpha and beta, OR(alpha,beta)(n) means "
                    + "alpha*omega(n)+beta <= Omega(n). Here omega counts distinct prime "
                    + "factors and Omega counts prime factors with multiplicity, using "
                    + "Mathlib's cardDistinctFactors and cardFactors, respectively. "
                    + "This is the inequality defined on printed page 48 of Section 7."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("restricted-count"),
                DeclarationHandle.Create(Prefix + "orCount"),
                H("Counting the restricted Euler forms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("orCount(alpha,beta,X) counts integers from 1 to X "
                    + "satisfying EulerForm and OR(alpha,beta). The reused EulerForm "
                    + "predicate says n=q^a*m^2, with q prime, q and a congruent to one "
                    + "modulo four, m positive, and gcd(q,m)=1. It imposes no separate "
                    + "oddness condition on m. Each integer is counted once, regardless "
                    + "of its representations."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Both clauses of substantially stronger"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 1 quantifies over all real alpha1, "
                    + "alpha2, beta1 and beta2 with alpha1 > alpha2 > 2. It asserts both "
                    + "that every Euler form satisfying OR(alpha1,beta1) satisfies "
                    + "OR(alpha2,beta2), and that "
                    + "orCount(alpha1,beta1,X)/orCount(alpha2,beta2,X) tends to zero "
                    + "as the natural threshold X tends to infinity. These are exactly "
                    + "the two requirements of substantially stronger on page 48. "
                    + "Real thresholds have the same counts as their natural-number floors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("euler-count-upper"),
                DeclarationHandle.Create(Prefix + "euler_count_upper"),
                H("An upper bound of order X/log(X)"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("There is a real constant C > 0 such that, for all "
                        + "sufficiently large natural numbers X, eulerCount(X) <= C*X/log(X). "
                        + "The predicate is the full Euler form printed in Section 7: "
                        + "n=q^a*m^2, q prime, q and a congruent to one modulo four, "
                        + "m positive and coprime to q. No parity condition on m is added.")),
                    Paragraph(Text("Write a=1+2j and s=q^j*m. Then n=q*s^2. "
                        + "Cover these integers by images of primes q <= X/s^2 for "
                        + "1 <= s <= floor(X^(1/4)), together with the larger-square tail. "
                        + "Repeated representations only increase this upper bound; "
                        + "no coprimality condition on q and s is imposed.")),
                    Paragraph(Text("In the first range X/s^2 >= X^(1/2), so a single "
                        + "Chebyshev threshold applies to every summand for sufficiently "
                        + "large X. Moreover log(X/s^2) >= log(X)/2. The sum of 1/s^2 "
                        + "is at most two. The other range is at most 2X/(T+1), where "
                        + "T=floor(X^(1/4)). Since log(X)/X^(1/4) tends to zero, "
                        + "the tail is eventually at most 2X/log(X). "
                        + "Natural division X/s^2 equals floor((X:real)/s^2), which "
                        + "connects the finite prime counts to the real estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-relative-density"),
                DeclarationHandle.Create(Prefix + "relative_density_pos"),
                H("A positive lower bound for every parameter pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every pair of real numbers alpha and beta, "
                        + "there is a real c > 0 such that "
                        + "c*eulerCount(X) <= orCount(alpha,beta,X) for every sufficiently "
                        + "large natural X. No lower bound on alpha is needed.")),
                    Paragraph(Text("Choose an integer h >= 1 with 1+2h >= 2alpha+beta. "
                        + "For every prime q congruent to one modulo four, q differs "
                        + "from 3. Thus 3^(2h)*q has Euler's form with exponent one "
                        + "and square factor 3^h, exactly two distinct prime factors, "
                        + "and 1+2h prime factors with multiplicity. These integers "
                        + "satisfy OR(alpha,beta), and multiplication by 3^(2h) is "
                        + "injective. The modulus-four prime lower bound therefore "
                        + "bounds their count below by a positive multiple of X/log(X).")),
                    Paragraph(Text("The full-set estimate counts every Euler form "
                        + "as q*s^2 by absorbing the even part of its prime exponent "
                        + "into the square factor. For s <= X^(1/4), Chebyshev's "
                        + "prime-counting upper bound and the reciprocal-square sum "
                        + "give O(X/log(X)). For larger s, the reciprocal-square tail "
                        + "gives O(X^(3/4)). Consequently eulerCount(X) is at most "
                        + "a constant times X/log(X), and comparison gives the "
                        + "displayed positive relative lower bound.")),
                    Paragraph(Text("In particular, the strong-property assertion of "
                        + "Theorem 9 on the same page fails for every alpha > 2 and "
                        + "real beta: its required quotient cannot tend to zero. "
                        + "This concerns counting within the entire printed Euler set, "
                        + "and makes no assertion about the existence of odd perfect numbers."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Conjecture 1 is false"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Apply the preceding lower bound to (alpha,beta) "
                    + "equal to (4,0) and (3,0). The latter count is at most the full "
                    + "Euler count and eventually positive. Hence the quotient of "
                    + "the former by the latter is eventually bounded below by a "
                    + "positive constant, contradicting the asserted limit zero. "
                    + "For these parameters the inclusion clause itself holds, since "
                    + "omega(n) is nonnegative; the density clause supplies the "
                    + "contradiction."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zelinsky-2021-conjecture-1-or-density"),
                    ResolutionKind.Refuted)))));
}
