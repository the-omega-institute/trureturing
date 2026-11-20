using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class McCormackZelinskyQuestion38Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/McCormackZelinskyQuestion38.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mccormackzelinsky2023weightedamgm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sixty times every nonnegative power of two is strongly pseudoperfect.",
        H("McCormack and Zelinsky's Question 38"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("An affirmative answer for the entire binary family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every natural number j, including zero, "
                        + "n=60*2^j is strongly pseudoperfect. This uses the positive "
                        + "integer predicate StrongPseudoperfectDensity.StronglyPseudoperfect: "
                        + "there is a finite subset S of n.divisors with sum 2*n, and "
                        + "for every divisor d, d is in S if and only if n/d is in S. "
                        + "This is exactly Question 38 on page 17 of the source.")),
                    Paragraph(Text("Write a=j+2, so n=15*2^a. For a>=5, every "
                        + "chosen divisor has the form 2^i*d with d dividing 15. "
                        + "At levels 0 and a take d in {1,15}; at levels 1 and a-1 "
                        + "take d in {1,3,5,15}; at levels 2 and a-2 take nothing; "
                        + "at levels 3 through a-3 take d in {3,5}. The last "
                        + "range is empty when a=5. Coprimality of 15 and 2^a "
                        + "makes the products distinct.")),
                    Paragraph(Text("Complementation sends (i,d) to (a-i,15/d). "
                        + "Each of the three odd-part sets is closed under d -> 15/d, "
                        + "and its level set is closed under i -> a-i. Thus the "
                        + "chosen divisor set is closed under exact complementation.")),
                    Paragraph(Text("The geometric sum over 3<=i<=a-3 equals "
                        + "2^(a-2)-8. Consequently the chosen divisor sum is "
                        + "16*(1+2^a)+24*(2+2^(a-1))+8*(2^(a-2)-8) "
                        + "=30*2^a=2*n. The three smaller cases n=60,120,240 "
                        + "use all divisors except, respectively, {2,30,6,10}, "
                        + "{3,40,5,24,6,20,10,12}, and "
                        + "{2,120,4,60,6,40,12,20}; every omitted set is a union "
                        + "of complementary pairs, and the remaining sums are "
                        + "120,240,480."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mccormack-zelinsky-2023-question-38"),
                    ResolutionKind.Proved)))));
}
