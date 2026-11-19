using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class McCormackZelinskyQuestion34Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/McCormackZelinskyQuestion34.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mccormackzelinsky2023weightedamgm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd pseudoperfect divisor sets containing one satisfy A < C.",
        H("McCormack and Zelinsky's Question 34"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed odd primitive example"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Question 34 asks whether there is a natural number "
                    + "n which is odd and primitive non-deficient, together with a finite "
                    + "subset S of its positive divisors such that 1 belongs to S, the sum "
                    + "of S is 2*n, and weightC(S,n) < weightA(S,n). Primitive "
                    + "non-deficiency means that n is non-deficient and every positive "
                    + "proper divisor of n is deficient. The two weights are exactly "
                    + "equations (12) and (14), using real logarithms and exact natural "
                    + "division inside the complementary totient. The set may include n "
                    + "and is not required to be closed under complementary divisors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("odd-weight-reverse"),
                DeclarationHandle.Create(Prefix + "odd_weight_reverse"),
                H("Strict reverse inequality for every odd divisor set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every odd natural number n and every finite "
                        + "subset S of n.divisors containing 1 and summing to 2*n, "
                        + "weightA(S,n) < weightC(S,n). No primitivity or separate "
                        + "non-deficiency hypothesis is needed.")),
                    Paragraph(Text("Put T={n/d : d in S}. Exact divisor complementation "
                        + "gives sum over e in T of 1/e = 2, and the reciprocal mass "
                        + "on e>1 is at least one. An odd e>1 with phi(e)<8 belongs "
                        + "to {3,5,7,9}. Using log(8) as a baseline on the remaining "
                        + "terms and allowing all four exceptional indices gives")),
                    Paragraph(Text("sum over e in T of log(phi(e))/e >= "
                        + "log(2)/3 + log(4)/5 + (1/7+1/9)*log(6) "
                        + "+ (67/315)*log(8) = (512*log(2)+80*log(3))/315 "
                        + "> 2*log(2). The strict final inequality follows from "
                        + "9>8, hence 2*log(3)>3*log(2).")),
                    Paragraph(Text("Totient supermultiplicativity bounds A above by "
                        + "log(phi(n)) minus half that complementary logarithmic sum. "
                        + "The element 1 contributes phi(n)/2 to the sum defining C, "
                        + "and another positive term is present because the divisor "
                        + "sum is 2*n. Thus C>log(phi(n)/2), while "
                        + "A<log(phi(n)/2). All logarithm arguments used here "
                        + "are strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Question 34 has a negative answer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The existence statement claim is false. "
                    + "Any proposed example satisfies the hypotheses of the strict "
                    + "reverse inequality, contradicting its requirement A>C. "
                    + "The obstruction holds for every odd divisor set of sum 2*n "
                    + "containing 1, including all primitive non-deficient candidates. "
                    + "It does not assert the same inequality after removing oddness "
                    + "or the requirement that 1 belong to the set."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mccormack-zelinsky-2023-question-34"),
                    ResolutionKind.Refuted)))));
}
