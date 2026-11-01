using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Apollonian;
internal sealed class CutoffGramLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Apollonian/CutoffGramLimit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/radsararanando2026apollonian");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual fixed-cutoff Gram matrices converge to their diagonal face weights.", H("Fixed-cutoff Gram limit"), Blocks(
            Node("normalizedGram", "The normalized actual Gram matrix",
                "For natural k,t, normalizedGram k t is 2^(-(k+t)) times B B^T on the fixed actual vertex set Vertex k, where B=cutoffBlock k t. Powers here have natural exponents before inversion. The matrix comes from the ordinary zero-one graph adjacency.", DescribeRole.Definition),
            Node("limitingDiagonal", "The limiting face-weight diagonal",
                "For natural k, limitingDiagonal k has diagonal entry faceCount k u divided by 2^k at each actual old vertex u, and zero off the diagonal.", DescribeRole.Definition),
            Node("normalized_gram_tendsto", "Convergence on the fixed old vertex set",
                "For each natural cutoff k, normalizedGram k t tends as t tends to infinity to limitingDiagonal k in the finite matrix topology, hence also for the Euclidean operator norm. The diagonal uses the exact doubling recurrence of incident inner faces and the exact degree increments. Every off-diagonal entry lies between zero and 2t/2^(k+t), which tends to zero. The cutoff is fixed before taking the stage limit. This statement alone does not identify the second ordered eigenvalue of the limiting diagonal.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cutoffgramlimit-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
