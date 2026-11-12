using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Polynomials;

internal sealed class KimStolarskyEventualPrefixRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/kimstolarsky2026nicomachus");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd-root continued-fraction conjecture fails on an unbounded arithmetic progression of indices.",
        H("The eventual three-prefix conjecture is false"),
        Blocks(
            Paragraph(Text(
                "Kim and Stolarsky, A Balanced Three-term Generalization of Nicomachus' Identity, "
                + "arXiv:2511.15133v1, Theorem 1 and Remark 4, conjecture three simultaneous "
                + "ordinary continued-fraction prefixes for the negatives of real roots tending to minus four. "
                + "The journal version, A Balanced Three or More-term Generalization of "
                + "Nicomachus' Identity, Integers 26, A98, retains these formulas in Remark 3. "
                + "The claim here includes all three original polynomial sums, the shift "
                + "from m to m+1 for L and R, all three root limits, and one eventual threshold.")),
            Describe.Lean(
                DescribeId.Create("eventual-three-prefix-assertion-refuted"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/KimStolarskyEventualPrefixRefutation.result"),
                H("No common eventual threshold exists"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Put m=10^(4n+2). The shifted R polynomial is the square of "
                        + "T_(2m+1)+(1+T_m)x. Its unique distinct real root is "
                        + "r=-2(2m+1)(m+1)/(m^2+m+2). For m greater than ten, "
                        + "the number y=-r satisfies y-4=(2m-6)/(m^2+m+2), "
                        + "which lies strictly between zero and 2/m. Thus the actual "
                        + "root branch tends to minus four.")),
                    Paragraph(Text(
                        "The reciprocal of y-4 is exactly m/2+2+7/(m-3). "
                        + "Since m is even and 0<7/(m-3)<1, the coefficient after "
                        + "four is m/2+2=50*10^(4n)+2. The next complete quotient "
                        + "is (m-3)/7. If n=3k+2, then m is congruent to four "
                        + "modulo seven. Writing m=7q+4, this complete quotient "
                        + "is q+1/7, so its floor is q. The printed formula is "
                        + "floor(m/7)-1=q-1. The subsequent coefficient is seven, "
                        + "so the rational continued fraction does not terminate "
                        + "at the disputed position.")),
                    Paragraph(Text(
                        "For every proposed threshold N, the index 3N+2 lies "
                        + "beyond it and violates the R prefix. Hence the complete "
                        + "eventual conjunction is false. No individual conclusion "
                        + "about the L or Q prefixes, or the even case, follows. "
                        + "The formal proof derives the contradiction for every "
                        + "R root; its root-limit hypothesis need not be used."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kim-stolarsky-eventual-three-prefix-conjecture"),
                    ResolutionKind.Refuted))),
        []));
}
