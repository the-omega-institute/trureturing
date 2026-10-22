using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ExpRatioCM;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/weiguo2014completemonotonicity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact complete monotonicity classification of consecutive signed derivative ratios.",
        H("Failure above index two and refutation"), Blocks(
            Describe.Lean(DescribeId.Create("exp-ratio-cm-failure-on-every-tail"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Result.failure_on_every_tail"),
                H("Failure on every right half-line"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every i at least three and every real T, there is t greater than both T and zero and an order k for which both signed ratio derivatives are negative. The second coefficient 2 times 3^i minus 4^i is negative. Its extracted limit is therefore eventually negative, while the sampling points tend to infinity. The two ratio families agree on a neighborhood of each positive sampling point."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-failure-family"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Result.not_cm_of_three_le"),
                H("Indices at least three"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Both ratio families fail complete monotonicity whenever the index is at least three."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exp-ratio-cm-result"),
                DeclarationHandle.Create("D5/S3/Analytic/ExpRatioCM/Result.result"),
                H("Refutation of the universal assertion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The universal assertion about both ratio families is false. Its specialization to index three contradicts Result.not_cm_of_three_le, while the low-index positive cases are supplied by Positive.cm_of_le_two."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wei-guo-2014-exponential-derivative-ratio-complete-monotonicity"),
                    ResolutionKind.Refuted)))));
}
