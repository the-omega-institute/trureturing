using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DeletionResilientCliques;

internal sealed class ColorableInducedSubgraphDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DeletionResilientCliques/ColorableInducedSubgraph.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal degrees bound the size of a colorable induced subgraph.",
        H("A large colorable induced subgraph"),
        Blocks(
            Describe.Lean(DescribeId.Create("colorable-induced-subgraph"),
                DeclarationHandle.Create(Prefix + "exists_colorable_induce_of_minDegree"),
                H("A large colorable induced subgraph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc")),
                Blocks(Paragraph(Text("Let s be positive, and let G be a finite graph with minimum degree at least s − 1. Some vertex set X induces an s-colorable graph and has cardinality at least the sum, over all vertices v, of s divided by degree(v) + 1. In each total ordering, keep the vertices with fewer than s earlier neighbors. Greedy coloring works in the inherited order. In the closed neighborhood of v the ranks of v have equal multiplicities, by swapping two vertex positions. Averaging these finite counts gives the stated set."))), DescribeRole.Theorem)),
        []));
}
