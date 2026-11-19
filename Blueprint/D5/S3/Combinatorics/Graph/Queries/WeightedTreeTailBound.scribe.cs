using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class WeightedTreeTailBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The endpoint of a shortest forest suffix fixes its crossing index.",
        H("Summing the weighted crossing events over the leaves"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("total-leaf-weight"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/WeightedTreeTailBound.totalLeafWeight"),
                H("The bound determined by target depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a target of depth d the total leaf weight is three halves minus "
                    + "one half to the power d plus one, represented as an extended "
                    + "nonnegative real."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mass-of-weighted-tail"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/WeightedTreeTailBound.mass_of_weighted_tail"),
                H("Charge each arrival leaf at one crossing index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a target vertex in the complete binary tree and a total path "
                        + "length r. For each index j and arrival leaf y, give crossing and "
                        + "tail events in one probability space. Every outcome of the "
                        + "collision event belongs to both at a witness with j plus one plus "
                        + "the tree distance from y to the target equal to r.")),
                    Paragraph(Text(
                        "Suppose the mass of each crossing event is bounded by a common "
                        + "budget. Suppose the joint mass of crossing and tail is bounded "
                        + "by the crossing mass times one half raised to the tree distance. "
                        + "Then the collision mass is at most the common budget times the "
                        + "total leaf weight for the target.")),
                    Paragraph(Text(
                        "For each arrival leaf, the distance equation determines j. The "
                        + "collision event is contained in a union indexed by the leaves. "
                        + "Subadditivity and the joint mass bounds give the weighted sum. "
                        + "The exact binary tree distance sum evaluates it."))),
                DescribeRole.Theorem))));
}
