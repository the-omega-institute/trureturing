using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.RegularCHS;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extrema of complete homogeneous symmetric norms over connected regular graphs.",
        H("Regular graph CHS extrema"), Blocks(
            Describe.Lean(DescribeId.Create("regular-chs-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RegularCHS/Result.result"),
                H("The cycle minimizes and the complete graph maximizes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms")),
                Blocks(
                    Paragraph(Text("For every natural n at least three and m at least one, the cycle and the complete graph on Fin n are connected and regular. Every connected regular simple graph G on these vertices has its degree 2m CHS norm at least that of the cycle and at most that of the complete graph. Thus both bounds are attained. The norm is the real power of the complete homogeneous symmetric polynomial in the real adjacency eigenvalues, with exponent one divided by 2m.")),
                    Paragraph(Text("The coefficient lower bound holds more generally for every r-regular graph of order n at least three with r at least two, without connectedness. At regular degree two, cycle-component factorization gives the comparison. At regular degree three, closed-walk domination and the positive Newton recurrence give it. At regular degree at least four, the even closed-walk lower bound gives bseq n r m, monotonicity in r gives bseq n 4 m, and the spectral bound on the cycle places its coefficient below that sequence. Entrywise adjacency comparison with the complete graph gives the upper bound.")),
                    Paragraph(Text("Connectedness and the degree-sum formula force the regular degree to be at least two when n is at least three. All adjacency CHS coefficients are nonnegative; monotonicity of the real power with nonnegative exponent transfers the coefficient inequalities to the stated norms. This conclusion concerns the regular family; it makes no assertion about the unicyclic family or uniqueness within a fixed degree class."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chavez-2023-regular-chs-norm-extrema"), ResolutionKind.Proved)))));
}
