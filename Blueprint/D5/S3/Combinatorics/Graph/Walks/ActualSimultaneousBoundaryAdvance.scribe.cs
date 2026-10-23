using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualSimultaneousBoundaryAdvanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualSimultaneousBoundaryAdvance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual joint update constructs both restored boundary orders on the same supplied cycle.",
        H("Two Actual Boundary Orders of the Same Cycle"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-simultaneous-boundary-advance"),
                DeclarationHandle.Create(Prefix + "actual_simultaneous_boundary_advance"),
                H("Advance Both Actual Boundary Orders"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The supplied prior cycle has actual joint, primary and opposite partitions with disjoint cut groups. The current supplied Hamilton cycle has the earned three-path joint replacement. After the cut groups exchange and their new zero cuts are erased, explicit restoration constructs both actual next boundaries at once. Every output path is simple; all three partitions refer to the same current cycle. The complete endpoint sets and the literal distinguished and crossing prefixes needed by the next step are conclusions."))), DescribeRole.Theorem))));
}
