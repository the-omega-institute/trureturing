using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Abundancy;

internal sealed class ZelinskyNortonConjecture27Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Abundancy/ZelinskyNortonConjecture27.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/zelinsky2023nondeficient");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every Norton threshold at alpha greater than one has unbounded first differences.",
        H("Zelinsky's Conjecture 27"),
        Blocks(
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Every fixed positive increment is eventually exceeded"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every real alpha>1 and every real C>0, "
                        + "all sufficiently large natural n satisfy "
                        + "aAlpha(alpha,n)+C<aAlpha(alpha,n+1), with each natural "
                        + "threshold length cast to the real numbers. Both "
                        + "parameters are fixed before the eventual index is "
                        + "chosen. This is Conjecture 27 on page 13 of "
                        + "Zelinsky's Integers 23 article A13.")),
                    Paragraph(Text("Adjacent cancellation gives a positive "
                        + "constant c, depending on alpha, such that "
                        + "c*p_n^(alpha-1) is at most one plus the real first "
                        + "difference for every sufficiently large n. The primes "
                        + "p_n tend to infinity, and alpha-1 is positive. Hence "
                        + "this lower bound tends to infinity and eventually "
                        + "exceeds C+1, giving the required strict inequality.")),
                    Paragraph(Text("The assertion concerns eventual growth "
                        + "for each fixed alpha and C. It does not supply a "
                        + "uniform starting index over all alpha>1, and it "
                        + "does not claim an exact asymptotic equivalence for "
                        + "the first difference."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zelinsky-norton-conjecture-27"),
                    ResolutionKind.Proved)))));
}
