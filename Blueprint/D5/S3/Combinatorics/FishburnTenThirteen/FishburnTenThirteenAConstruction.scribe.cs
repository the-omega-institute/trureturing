using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnTenThirteenAConstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenAConstruction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximum insertion gives a reversible construction and active-position polynomial recurrences for indecomposable Fishburn permutations avoiding 2413 and 2431.",
        H("Constructing Indecomposable 2413 and 2431 Avoiders"),
        Blocks(
            Node("fishburntenthirteenaconstruction-indecomposable-construction", "A construction with active-position weights", "indecomposable_construction",
                "Let A_n be the Fishburn permutations of length n avoiding 2413 and 2431, let I_n be its sum-indecomposable members, and call a position active when insertion of n + 1 there yields a member of A_(n + 1). Maximum insertion is a bijection from pairs consisting of a member p of A_n and either position zero or an active position strictly before the end of an indecomposable p, onto I_(n + 1). For positive n, if p has a active positions, insertion at zero preserves a, whereas insertion at the interior active position of rank j, numbered from zero among interior active positions, gives a - j active positions. Interior active positions are in bijection with the nonnegative integers strictly less than a - 2; the position of rank j has j + 1 active positions preceding it. Thus I_(n + 1) is in bijection with the disjoint union of A_n and pairs of a member of I_n with one of its a - 2 interior active positions. Its cardinality is the cardinality of A_n plus the number of these pairs. For every nonnegative label r, the number of children with r + 2 active positions is the number of members of A_n with r + 2 active positions plus, when r is positive, the number of members of I_n with at least r + 2 active positions. For any rational-polynomial weight w, the sum of w(a(child) - 2) over I_(n + 1) equals the sum of w(a(p) - 2) over A_n plus the sum over p in I_n and nonnegative j strictly less than a(p) - 2 of w(a(p) - j - 2). If L is the sum of X to the power a(p) - 2 over I_n and Q is the sum over those p and nonnegative exponents strictly less than a(p) - 2 of X to that exponent, then (1 - X)Q is the cardinality of I_n minus L, and the active-position polynomial of I_(n + 1) is that of A_n plus XQ. All subtractions in indices and counts are truncated at zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
