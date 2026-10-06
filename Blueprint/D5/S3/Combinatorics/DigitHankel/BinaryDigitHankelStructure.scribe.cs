using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class BinaryDigitHankelStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelStructure.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse binary kernel vectors force the Hankel determinant at t = -2 to vanish outside the threshold triples.",
        H("Vanishing Outside the Threshold Triples"),
        Blocks(
            Node("binary-digit-hankel-structure-zero-direction", "Vanishing away from the triples", "zero_direction",
                "For every integer n at least two, if there is no nonnegative integer k for which n + 1 = n_k, n = n_k, or n = n_k + 1, then H(n,-2) = 0, where n_k = ceil(2^(k+2)/3). Splitting the binary digit sum into blocks gives sparse nonzero vectors in the kernel of the Hankel matrix at these sizes, forcing its determinant to vanish.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
