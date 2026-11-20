using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.CoveringDimension;

internal sealed class FiniteFrontierDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/CoveringDimension/FiniteFrontier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite frontiers and covering dimension", H("Finite frontiers and covering dimension"),
        Blocks(
            Paragraph(Text("Covering dimension at most n means that every finite open cover has a finite open refinement of multiplicity at most n + 1.")),
            Describe.Lean(
                DescribeId.Create("finite-frontier-covering-dimension-upper-bound"),
                DeclarationHandle.Create(Owner + "atMost_one_of_finiteFrontier"),
                H("Finite frontiers give refinements of multiplicity two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a compact Hausdorff space have a basis of open neighborhoods with finite frontiers. Choose a finite subcover from these neighborhoods. Off the union of the frontiers, the membership patterns in the chosen neighborhoods give disjoint open cells. Pairwise disjoint neighborhoods of the frontier points complete the refinement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("preconnected-space-covering-dimension-lower-bound"),
                DeclarationHandle.Create(Owner + "not_atMost_zero"),
                H("A nontrivial preconnected space with closed points has positive covering dimension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complements of two distinct points form an open cover. A multiplicity-one refinement would contain a nonempty proper clopen member."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-fibers-covering-dimension-upper-bound"),
                DeclarationHandle.Create(Owner + "atMost_of_closedMap_finiteFibers"),
                H("Closed finite-to-one maps pull covering-dimension bounds back"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a continuous closed map from a Hausdorff space to a compact space have finite fibers. Separate each fiber by disjoint open sets subordinate to the original cover. Closedness gives a base neighborhood whose entire preimage lies in those sets. Refine in the base, then split each pullback into the corresponding disjoint pieces."))),
                DescribeRole.Theorem))));
}
