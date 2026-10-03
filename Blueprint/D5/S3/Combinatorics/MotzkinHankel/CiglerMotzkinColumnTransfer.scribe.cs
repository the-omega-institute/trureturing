using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinColumnTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnTransfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One orthogonal moment functional recovers every column of the boundary-weighted Motzkin triangle.",
        H("Orthogonal Moments for Motzkin Columns"),
        Blocks(
            Node("cigler-motzkin-column-transfer-moments", "The column moment functional", "column_moments",
                "Over the integer polynomial ring in t and s, let p_0(y) = 1, p_1(y) = y - s and p_{r+2}(y) = (y - t)p_{r+1}(y) - p_r(y). There is a linear functional ell on polynomials in y such that ell(y^n p_k(y)) = M_{n,k}(t,s) for all nonnegative n and k, and ell(p_i p_j) is one when i equals j and zero otherwise. Here M_{n,k}(t,s) counts Motzkin paths with horizontal weight s on the axis and t above it. Moving the three-term recurrence across the pairing yields the column identities, and triangularity of the Motzkin array yields orthogonality.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
