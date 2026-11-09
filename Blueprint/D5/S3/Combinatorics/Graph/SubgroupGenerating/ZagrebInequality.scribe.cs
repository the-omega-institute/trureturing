using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubgroupGenerating;

internal sealed class ZagrebInequalityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/SubgroupGenerating/ZagrebInequality.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Zagreb inequality for the complete subgroup-generating graph.", H("ZagrebInequality"), Blocks(
            Describe.Lean(DescribeId.Create("zagreb-first"),
                DeclarationHandle.Create(Owner + "firstZagreb"), H("First Zagreb index"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite simple graph, the first Zagreb index is the real sum of squared degrees over every vertex. Isolated vertices stay in the carrier and contribute zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zagreb-endpoint-product"),
                DeclarationHandle.Create(Owner + "endpointProduct"), H("Unordered endpoint product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication of endpoint degrees is symmetric, so it defines a real function on unordered vertex pairs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zagreb-second"),
                DeclarationHandle.Create(Owner + "secondZagreb"), H("Second Zagreb index"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The second Zagreb index sums the endpoint product over the actual unordered edge finset. Each edge occurs once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zagreb-hansen-vukicevic"),
                DeclarationHandle.Create(Owner + "hansen_vukicevic"), H("All finite groups"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite group, the second Zagreb index divided by the edge count is at least the first Zagreb index divided by the vertex count. The graph has disjoint vertex parts consisting of all ordered pairs and all subgroups, with a pair adjacent precisely to the subgroup it generates. Repetitions and zero fibers are retained. There is no nonabelian, nontrivial or two-generator assumption.")),
                    Paragraph(Text("Write m for the square of the group order, k for the number of all subgroups, and r(H) for the number of ordered pairs generating H. The existing pair partition gives the sum of r(H) as m. The original degree identities give degree one at every pair vertex and degree r(H) at H. An injective map sends each ordered pair to its one unordered graph edge and its image is exactly the edge finset. Consequently the first index is m plus the sum of r(H) squared, and the second index is the sum of r(H) squared. The vertex count is m plus k and the edge count is m; both are positive, including for the trivial group.")),
                    Paragraph(Text("Mathlib's square-sum inequality states that m squared is at most k times the sum of r(H) squared. Clearing the two positive denominators yields the stated comparison. This is a direct application of that standard inequality to the literal graph, and answers the existential question in Das, Erfanian and Nath, arXiv:2501.06124v1, Problem 3.10, in the negative. It makes no claim about arbitrary forests."))), DescribeRole.Theorem))));
}
