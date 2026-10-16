using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ComponentPacking;

internal sealed class PositiveTwoCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive edge lengths allow entire components to be assigned to two groups of controlled total vertex size.",
        H("Two capacities for whole positive-length components"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-two-capacity"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/ComponentPacking/PositiveTwoCapacity.positive_two_capacity"),
            H("Existence of a whole-component split"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every natural C and every function ell from Fin C to the natural numbers, "
                + "assume ell(i) is at least one for every i. Write d for the sum of all ell(i). "
                + "There exists a finite subset A of Fin C such that the sum of ell(i)+1 over A "
                + "is at most d, and the sum of ell(i)+1 over its complement is at most d+1. "
                + "No upper bound or equality condition is imposed on the lengths. Either group "
                + "is allowed to be empty. When C is zero use two empty groups; when C is one use an "
                + "empty first group. For C at least two, the total size is d+C. Among subsets "
                + "whose size sum is at least C-1, choose one with the fewest members. Removing "
                + "any member leaves sum below C-1. Each member has size at most d-C+2, since "
                + "the other C-1 components each have at least one edge. Therefore the chosen "
                + "sum is at most d. Subtracting that sum from d+C bounds the complement by d+1. "
                + "Each component stays whole; this statement concerns the component sizes."))),
            DescribeRole.Theorem)),
        []));
}
