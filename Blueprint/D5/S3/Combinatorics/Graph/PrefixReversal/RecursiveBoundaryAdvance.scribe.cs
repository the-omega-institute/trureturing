using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class RecursiveBoundaryAdvanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/RecursiveBoundaryAdvance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Even and Odd Boundary Propagation.",
        H("Exact Even and Odd Boundary Propagation"),
        Blocks(
            Describe.Lean(DescribeId.Create("advance-even-boundary"), DeclarationHandle.Create(Prefix + "advance_even_boundary"),
                H("Earn the Next Even Endpoint Relation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k at least three, shifting both indices of every unaffected even boundary pair and replacing the affected whole path by the two new boundary pairs is exactly the even boundary relation at k+1. This is an equivalence of endpoint relations, not existence of walks."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("advance-odd-boundary"), DeclarationHandle.Create(Prefix + "advance_odd_boundary"),
                H("Earn the Next Odd Endpoint Relation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k at least three, the same explicit affected-path replacement and positive-index shift takes the odd boundary relation exactly to the odd boundary relation at k+1. The index zero cases are proved as part of the equivalence."))), DescribeRole.Theorem))));
}
