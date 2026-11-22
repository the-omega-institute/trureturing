using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SignedGraphSpectral;

internal sealed class NormalizedCliqueBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized matrix equality and its rooted zero-sum extensions.",
        H("Normalized clique blocks"),
        Blocks(Describe.Lean(
            DescribeId.Create("normalized-decomposition-with-extensions"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/SignedGraphSpectral/NormalizedCliqueBlocks.normalized_decomposition_with_extensions"),
            H("Clique decomposition and extension from each root block"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/QuadraticForms/huliuwang2026squareenergy")),
            Blocks(
                Paragraph(Text(
                    "For a supported doubly nonnegative matrix on a finite connected graph, "
                    + "assume total entry mass and twice the square-root edge mass both equal "
                    + "the graph budget 2m − n + 1. The matrix is the sum of normalized "
                    + "rank-one clique matrices. Every edge belongs to precisely one block.")),
                Paragraph(Text(
                    "Choosing any block as root supplies an extension of each zero-sum "
                    + "root vector to a vector with zero sum on every block. Every vertex "
                    + "maps into the root, and an edge joining distinct fibers lies in the "
                    + "root. If every block is an edge, the original graph is a tree."))),
            DescribeRole.Theorem))));
}
