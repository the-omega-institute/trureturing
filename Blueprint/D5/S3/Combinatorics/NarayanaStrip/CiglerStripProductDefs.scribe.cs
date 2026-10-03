using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripProductDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The product formula for bounded Narayana series is expressed as equality of polynomial coefficients at heights 4m and 4m + 1.",
        H("Coefficients of the Narayana Strip Product"),
        Blocks(
            Node("cigler-strip-product-defs-left-coefficient", "The squared-parameter coefficient", "lhsCoeff",
                "For nonnegative integers h and N, the coefficient of z^N in C^{(h)}(t^2, z^2) is zero when N is odd. When N is even, it is the Narayana-weighted sum over Dyck paths of semilength N/2 confined to heights zero through h, with t replaced by t^2. Each up-step has weight one, and each down-step arriving at height k has weight one for even k and t for odd k before this substitution.", DescribeRole.Definition),
            Node("cigler-strip-product-defs-right-coefficient", "The signed convolution coefficient", "rhsCoeff",
                "For nonnegative integers h and N, the coefficient of z^N in c^{(h)}(t, z)c^{(h)}(-t, -z) is the sum over i from zero through N of c_i^{(h)}(t) times (-1)^(N - i) times c_{N-i}^{(h)}(-t). Here c_j^{(h)}(t) is the weighted sum over Dyck paths of semilength j confined to heights zero through h, with up-step weight one and down-step arrival weights repeating 1, t, -1, -t.", DescribeRole.Definition),
            Node("cigler-strip-product-defs-claim", "The two strip product identities", "claim",
                "For every positive integer m and every nonnegative integer N, the coefficient of z^N in C^{(4m)}(t^2, z^2) equals the coefficient of z^N in c^{(4m)}(t, z)c^{(4m)}(-t, -z), and the same coefficient equality holds at height 4m + 1. Both equalities are identities of polynomials in t with integer coefficients. This is the coefficientwise form of Conjecture 2, equation (79), of Cigler's paper.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
