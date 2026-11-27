using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FourBraidKhovanovCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/FourBraidKhovanovCounterexample.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/przytyckisilvero2024khovanov");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual extreme Khovanov row of an eleven-crossing four-braid",
        H("The actual extreme Khovanov row of an eleven-crossing four-braid"),
        Blocks(
            Paragraph(Text(
                "Przytycki and Silvero formulate the link-level graded constraint in Section 9.1 "
                + "of arXiv:2305.18648v1. The diagram is the closure of the braid with signed "
                + "generator indices (1, 2, 1, 1, -3, 2, 2, -3, 2, 1, 2).")),
            Describe.Lean(
                DescribeId.Create("four-braid-extreme-counterexample"),
                DeclarationHandle.Create(Owner + "fourBraid_integral_extreme_counterexample"),
                H("A four-strand presentation with the forbidden graded row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The signed cube has empty bases in all higher rows other than quantum "
                    + "degrees 21 and 19, which are acyclic. The nonzero row at degree 17 "
                    + "corresponds to framed quantum degree -13. Its rank-two group lies "
                    + "in framed degree -3 above the singleton in degree -5. This order "
                    + "violates the graded alternatives in Corollary 1.6 and supplies a "
                    + "counterexample to the link-level conjecture of Section 9.1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-braid-graded-extreme-claim-refuted"),
                DeclarationHandle.Create(Owner + "gradedExtremeClaim_refuted"),
                H("Refutation of the Section 9.1 graded constraint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Every link presented as a four-strand braid has braid index at most four. "
                    + "The proposed list must therefore contain the actual extreme row of "
                    + "this closure if the conjecture holds. The computed row violates that "
                    + "necessary consequence."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("przytycki-silvero-2024-four-braid-extreme-khovanov"),
                    ResolutionKind.Refuted)))));
}
