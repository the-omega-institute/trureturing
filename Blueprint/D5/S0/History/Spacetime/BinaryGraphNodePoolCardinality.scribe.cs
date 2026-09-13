using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class BinaryGraphNodePoolCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nodes of a finite binary graph.",
        H("Nodes of a finite binary graph"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-graph-node-pool-card"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/BinaryGraphNodePoolCardinality.nodePool_card"),
                H("The exact number of distinct nodes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take an arbitrary binary word in a window of length at least three. "
                    + "Represent indices and bits as finite von Neumann ordinals and graph entries "
                    + "as Kuratowski pairs. The union of the indices, their singletons, their unordered "
                    + "bit pairs, and their graph entries has four times the window length minus four "
                    + "elements, with one additional element exactly when bit zero is one and bit two "
                    + "is zero. Positive-index graph entries are distinct from all earlier families. "
                    + "The zero-index entry either equals the singleton of ordinal one or is the "
                    + "unordered pair of ordinals one and two; the latter coincides with an earlier "
                    + "node exactly when the index-two unordered bit pair contains ordinal one. "
                    + "The count requires neither a terminal one nor a nonadjacency condition."))),
                DescribeRole.Theorem))));
}
