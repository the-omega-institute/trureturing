using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class ThreeDistinguishabilitySupportCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal supports in four dimensions force two of three densities to be rank one.",
        H("Rank count for three orthogonal density supports"),
        Blocks(
            Theorem("sum-rank-le", "sum_rank_le_of_orthogonal_supports",
                "Joint support dimension",
                "Hermitian matrices with pairwise zero products have mutually orthogonal nonzero "
                + "eigenspaces. Collect the nonzero eigenvalue indices in a disjoint sum. Their unit "
                + "eigenvectors form one orthonormal family, so the sum of the ranks is at most the "
                + "dimension of the ambient space."),
            Theorem("rank-one-pair", "exists_perm_rank_one_pair",
                "Two rank-one states after permutation",
                "Three trace-one matrices each have positive rank. With total rank at most four, "
                + "at least two ranks equal one. A permutation places these two states first."),
            Theorem("rank-one-density", "exists_rankOneDensity_of_rank_one",
                "A unit representative",
                "For a positive rank-one matrix, just one spectral value is nonzero. Trace one "
                + "forces it to be one, so the matrix is the outer product of its unit eigenvector."))));

    private static DocumentBlock.Describe Theorem(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
