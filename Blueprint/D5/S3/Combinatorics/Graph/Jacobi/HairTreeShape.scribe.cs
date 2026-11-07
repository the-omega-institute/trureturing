using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Jacobi;

internal sealed class HairTreeShapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Jacobi/HairTreeShape.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colored hair-tree shapes", H("Finite colored hair-tree shapes"),
        Blocks(
            Describe.Lean(DescribeId.Create("hair-tree-shape"),
                DeclarationHandle.Create(Prefix + "HairTree"), H("Ordinary colored binary trees"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("HairTree C is a finite full binary tree with a color in C at each leaf. HairContext C is an explicit one-hole context, and fill inserts a tree into that context. The structural decomposition into a leaf or a context containing a pair of sibling leaves is used inside actual flag embeddings; it is an auxiliary shape calculation, not a separate mathematical endpoint."))), DescribeRole.Definition))));
}
