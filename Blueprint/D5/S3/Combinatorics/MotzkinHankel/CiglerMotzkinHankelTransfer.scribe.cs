using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinHankelTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelTransfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Motzkin path convolution expresses a shifted Hankel determinant as a path transfer determinant.",
        H("Motzkin Path Transfer Determinants"),
        Blocks(
            Node("cigler-motzkin-hankel-transfer-triangle", "Triangularity of the Motzkin array", "motzkin_triangle",
                "For every nonnegative path length n, M_{n,k}(t,s) vanishes whenever k is greater than n, and M_{n,n}(t,s) = 1. Reaching height n in n steps requires every step to be an up step.", DescribeRole.Theorem),
            Node("cigler-motzkin-hankel-transfer-determinant", "The Hankel transfer identity", "hankelDet_transfer",
                "For all nonnegative integers m and n, d_m(n,t,s) equals the determinant of the n by n matrix with entry M_{m+i,j}(t,s) in row i and column j, with indices starting at zero. Convolution factors the Hankel matrix as this transfer matrix times the transpose of the lower triangular Motzkin array. That triangular array has diagonal entries one and determinant one.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
