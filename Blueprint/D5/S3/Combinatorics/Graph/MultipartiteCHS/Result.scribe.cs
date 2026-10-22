using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MultipartiteCHS;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete multipartite branch of the cited article's CHS norm problem.",
        H("Complete multipartite CHS norm extrema"), Blocks(
            Describe.Lean(DescribeId.Create("multipartite-result-chs"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.chs"),
                H("Complete homogeneous spectral value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a complete multipartite adjacency matrix, chs is the complete homogeneous symmetric polynomial evaluated at its real eigenvalues. This is the spectral quantity in the cited article's norm definition in Section 1.1 and Theorem 1.4."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multipartite-result-chsnorm"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.chsNorm"),
                H("Complete homogeneous spectral norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("chsNorm is the real power of chs with exponent the reciprocal of the natural degree. For an even degree 2m this is the CHS norm used in the cited article's Section 1.1 definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multipartite-result-claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.claim"),
                H("Fixed-part-count multipartite extremum claim"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For r at least two, n at least r, and m at least one, positive part sizes summing to n have their CHS 2m-norm minimized by the concentrated part multiset and maximized by the balanced part multiset. Equality at either endpoint forces equality of part multisets up to permutation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multipartite-result-theorem"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Result.result"),
                H("Complete multipartite branch of Problem 3"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every r at least two, n at least r, and m at least one, and every positive part-size vector of total n, the CHS 2m-norm is at least the value at the part sizes n minus r plus one followed by r minus one singletons. Equality forces the same part multiset. The norm is at most the value at the balanced part sizes, and equality likewise forces the balanced multiset.")),
                    Paragraph(Text("The proof uses the spectral identity chs a d = recH a d, the reciprocal recurrence, and strict coefficient comparison under two-part transfers. Positivity of the even coefficients permits the real-power inequalities and their equality converses."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chavez-2023-multipartite-chs-norm-extrema"),
                    ResolutionKind.Proved)))));
}
