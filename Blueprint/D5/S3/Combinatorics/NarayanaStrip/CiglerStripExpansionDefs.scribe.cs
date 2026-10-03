using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripExpansionDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Narayana weights and their signed counterparts give two polynomial sums over Dyck paths confined to an even strip.",
        H("Weighted Dyck Paths in a Strip"),
        Blocks(
            Node("cigler-strip-expansion-defs-height-after", "Prefix height", "heightAfter",
                "A path is a finite sequence of Boolean steps, with true denoting an up-step and false a down-step. Its height after k steps is the sum of the first k increments, each up-step contributing one and each down-step contributing minus one. If k exceeds the path length, the entire path is used.", DescribeRole.Definition),
            Node("cigler-strip-expansion-defs-is-strip-dyck", "Dyck paths of bounded height", "IsStripDyck",
                "For a natural number h, a path is a Dyck path in the strip of height h when every prefix, including the empty prefix, has height between zero and h, inclusive, and its final height is zero.", DescribeRole.Definition),
            Node("cigler-strip-expansion-defs-weight", "The weight of a path", "weight",
                "Given a sequence tau of integer polynomials, the weight of a path is the product of its step weights. An up-step has weight one. A down-step arriving at height k has weight tau(k), with a negative arrival height replaced by zero. The empty path has weight one.", DescribeRole.Definition),
            Node("cigler-strip-expansion-defs-strip-sum", "The weighted strip sum", "stripSum",
                "For natural numbers h and n and a polynomial weight sequence tau, stripSum is the sum of the weights of all Dyck paths of length 2n in the strip of height h. Each Boolean sequence of length 2n contributes its weight if it satisfies the strip condition and zero otherwise.", DescribeRole.Definition),
            Node("cigler-strip-expansion-defs-strip-count", "The number of strip paths", "stripCount",
                "For natural numbers h and j, stripCount is the number of Dyck paths of length 2j in the strip of height h. Equivalently, it is the cardinality of the Boolean sequences of length 2j whose prefix heights lie between zero and h and whose final height is zero.", DescribeRole.Definition),
            Node("cigler-strip-expansion-defs-tau-plus", "Narayana weights", "tauPlus",
                "The Narayana weight sequence is one at every even arrival height and t at every odd arrival height, where t is the indeterminate of the integer polynomial ring. Thus its successive entries are 1, t, 1, t, and so on.", DescribeRole.Definition),
            Node("cigler-strip-expansion-defs-tau-minus", "Signed Narayana weights", "tauMinus",
                "The signed weight sequence has period four, with entries 1, t, minus one and minus t at arrival heights congruent to zero, one, two and three modulo four, respectively.", DescribeRole.Definition),
            Node("cigler-strip-expansion-defs-claim", "The two even-strip expansions", "claim",
                "For every positive integer m and nonnegative integer n, let A_j be the number of Dyck paths of semilength j in the strip of height m minus one. The Narayana-weighted sum of paths of semilength n plus one in the strip of height 2m equals the sum, over j from zero through floor(n/2), of A_j times binom(n, 2j) times t^j times (1 + t)^(n - 2j). The signed weighted sum equals the sum over the same range of (-1)^j times A_j times binom(floor(n/2), j) times t^j times (1 + t)^(n - 2j). Both equalities are identities of integer polynomials.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
