using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cigler's two expansions express the Narayana-weighted Dyck path sums in an even strip through bounded Dyck skeletons and binomial coefficients.",
        H("Cigler's Even-Strip Expansions"),
        Blocks(
            Node("cigler-strip-expansion-result", "The Narayana and signed expansions", "result", "For every positive integer m and nonnegative integer n, let A_j count Dyck paths of semilength j in the strip of height m minus one. Give each up-step weight one and each down-step arriving at height k the Narayana weight one for even k and t for odd k. The weighted sum for paths of semilength n plus one in the strip of height 2m equals the sum, over j from zero through floor(n/2), of A_j times binom(n, 2j) times t^j times (1 + t)^(n - 2j). With the arrival weights instead repeating 1, t, minus one and minus t, the sum equals the sum over the same range of (-1)^j times A_j times binom(floor(n/2), j) times t^j times (1 + t)^(n - 2j). These polynomial identities are Conjecture 3 of Cigler's paper. Pairing the interior steps gives a Motzkin path in the strip of height m minus one. Removing horizontal steps gives a Dyck skeleton and colored gaps; counting all gap fillings yields the first expansion, while sign-reversing cancellation and counting the fixed gaps yield the second.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
