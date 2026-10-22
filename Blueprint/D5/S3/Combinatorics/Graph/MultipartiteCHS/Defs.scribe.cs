using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MultipartiteCHS;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete multipartite adjacency matrices and polynomial norms.",
        H("Complete multipartite graphs"), Blocks(
            Describe.Lean(DescribeId.Create("multipartite-adjacency-hermitian"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Defs.adj_isHermitian"),
                H("Symmetry of adjacency"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Vertices are pairs consisting of a part index and a vertex index within that part. Two vertices are adjacent precisely when their part indices differ. The real adjacency matrix is Hermitian, so its eigenvalues define the complete homogeneous symmetric polynomial and its real power norm."))),
                DescribeRole.Theorem))));
}
