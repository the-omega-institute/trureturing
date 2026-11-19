using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class UndirectedCycleCompletionLawDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef OrientationMultiplicity =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/greenhilljansonkimwormald2002pseudographs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform transport from actual oriented lifts to completed undirected cycle graphs.",
        H("The uniform undirected completion law"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-undirected-completion"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/LinearForests/UndirectedCycleCompletionLaw.uniform_undirected_completion"),
            H("Uniformity on labelled undirected cycle completions"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(OrientationMultiplicity),
            Blocks(
                Paragraph(Text(
                    "Let F be a simple graph on a finite labelled vertex type with at least "
                    + "three vertices. Assume that at least one connected two-regular simple "
                    + "graph on the same type contains F. An actual lift consists of a "
                    + "full-cycle successor permutation and a direction for each edge of F "
                    + "consistent with that permutation. The shadow sends each lift to the "
                    + "graph consisting of the underlying undirected cycle edges.")),
                Paragraph(Text(
                    "There is a uniform probability mass on the lifts and a uniform "
                    + "probability mass on the completed graphs. Pushing the former along "
                    + "the shadow gives the latter. Each mass assigns the reciprocal of its "
                    + "own finite carrier cardinality to each point.")),
                Paragraph(Text(
                    "A connected degree-two graph admits a cyclic labelling. Starting with "
                    + "a chosen outgoing direction, agreement of successor permutations "
                    + "propagates along the cycle. The possible permutations over the graph "
                    + "are the forward cycle and its inverse. Each forces the direction of "
                    + "every prescribed edge. Thus every graph has exactly two lifts, and "
                    + "summing the uniform point mass over a fiber gives uniform transport."))),
            DescribeRole.Theorem))));
}
