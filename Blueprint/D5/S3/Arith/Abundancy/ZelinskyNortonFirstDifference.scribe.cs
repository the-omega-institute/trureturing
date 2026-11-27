using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyNortonFirstDifferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyNortonFirstDifference.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/zelinsky2021totalprimefactors");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Norton threshold first differences omit a positive integer.",
        H("Zelinsky's question on the values of the first difference"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Every positive integer is proposed as a difference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural m>0, claim asks for a "
                    + "natural starting index n>=1 such that a(n+1)-a(n)=m. "
                    + "Here a is the least positive length of consecutive prime "
                    + "Euler factors whose product strictly exceeds two. The "
                    + "difference in claim uses natural subtraction. This is "
                    + "Question 5 in Section 5 of Zelinsky's Integers 21 article A76."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Some positive integer is omitted"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The proposition claim is false: there is a "
                        + "positive natural integer m that equals no "
                        + "a(n+1)-a(n) with n>=1.")),
                    Paragraph(Text("The adjacent-cancellation estimate at alpha=2 "
                        + "bounds one plus the real first difference below by a "
                        + "positive constant times p_n. Chebyshev's prime-counting "
                        + "upper bound then gives a(n+1)-a(n)>=2*n for every "
                        + "sufficiently large natural n.")),
                    Paragraph(Text("Choose a natural N beyond that threshold. "
                        + "If every positive value occurred, each of the values "
                        + "1 through 2*N+1 would have a preimage among the indices "
                        + "1 through N: any later index has difference at least "
                        + "2*(N+1). The image of N indices cannot contain 2*N+1 "
                        + "distinct values. This contradiction gives the omitted "
                        + "positive integer without specifying a particular one.")),
                    Paragraph(Text("The conclusion is the negation of the "
                        + "universal value assertion. It neither identifies all "
                        + "omitted values nor states an exact asymptotic for the "
                        + "first differences."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zelinsky-norton-first-difference"),
                    ResolutionKind.Refuted)))));
}
