using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFGlobalAllocationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual deletion and global balance",
        H("Actual deletion and global balance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/DUFGlobalAllocation.result"),
                H("Actual deletion and global balance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Incoming rows at a member e are exactly the valid rows with a sole mark whose recipient is e. Each has its assigned vertex in the actual local graph of e, and different incoming rows have different assigned vertices. Select precisely those incoming rows with positive deletion debt, and let W(e) be their image in the vertex set. The expense of e is the sum of all incoming row deficits.")),
                    Paragraph(Text("The residual graph is the induced graph on the complement of W(e), with the inherited coloring. When W(e) is nonempty, every residual mixed vertex has degree two, and no residual vertex with a singleton color class has degree one. The statement allows the residual vertex type to be empty. It imposes no nonempty ambient-type assumption.")),
                    Paragraph(Text("The privacy argument determines the two neighbor sets of the assigned recipient vertex from the actual mark equalities. Those neighbors are ordinary, and any mixed vertex adjacent to either is the assigned vertex itself. Applying positive private deletion gives the residual assertions. The deletion estimate pays the sum of positive selected debts from the decrease in potential; the row payment inequality bounds the incoming expense by that sum.")),
                    Paragraph(Text("Let U be the union of the internal groups over all actual valid rows. Then U is a subset of H. For an actual member e, define its remaining score as w(e) if W(e) is empty, and as the potential of its actual residual graph otherwise. The score is defined to be zero outside H. Empty selection has zero expense, so in either branch the remaining score is at most w(e) minus the expense.")),
                    Paragraph(Text("The global inequality is 2|U| plus the sum of the remaining scores over H minus U, at most the sum of w(e) over H. The internal groups are pairwise disjoint. Only sole-mark rows have nonzero deficit, and grouping those rows by their actual recipient identifies total deficit with total expense. A sole-mark recipient belongs to no internal group, so every internal member has zero expense. Partitioning H into U and its complement and combining these exact finite sums proves the inequality. The hypotheses are only that every member of H is a triple and H is DUF."))),
                DescribeRole.Theorem))));
}
