using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickCornerWeightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickCornerWeight.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original sum is faithful on the normalized common interior",
        H("The original sum is faithful on the normalized common interior"), Blocks(
            Paragraph(Text("The positive-definite conclusion is about the compressed space, not ambient invertibility. It remains valid on an empty interior. This bridges singular original pairs to the faithful weighted criterion.")),
            Node("InteriorIndex", "InteriorIndex hC is the subtype of eigenvalue indices with 0<lambda_i<1. It is the domain of the actual rectangular eigenvector embedding.", false, false),
            Node("interiorEmbedding", "interiorEmbedding hC consists of the eigenvector-unitary columns indexed by InteriorIndex hC. The weight and diagonal spectral coordinate statements use this physical embedding.", false, false),
            Node("embedding_isometry", "The adjoint of the interior eigenvector embedding times the embedding is the subtype identity. compressed_weight_posDef uses injectivity supplied by this isometry.", true, false),
            Node("embedding_eigenvectors", "C times the interior embedding equals the embedding times the diagonal matrix of its interior eigenvalues. This relation excludes kernel vectors when proving faithful compression.", true, false),
            Node("compressed_weight_posDef", "For PSD S and Hermitian C with spectralSupport(S) C=C, the compression J* S J to the eigenvalues 0<lambda(C)<1 is positive definite. No ambient faithfulness of S is assumed. original_pair_weight_posDef consumes this support argument.", true, false),
            Node("original_pair_weight_posDef", "For every PSD A,B, C=normalize(A+B,A) has interior embedding J with J*(A+B)J positive definite, including the zero pair and empty corner. OriginalPair uses this exact result to discharge the only faithfulness hypothesis in the common-corner criterion.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-corner-weight-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
