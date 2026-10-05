using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RegularInduced;

internal sealed class DysonMcKayLowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RegularInduced/DysonMcKayLower.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/dyson2026regularinduced");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit unions of nine-cycle products, with one exceptional component when needed, attain the prime bound.",
        H("The extremal lower-bound constructions"),
        Blocks(
            Node("dyson-mckay-attainment", "Constructing a union of the extremal order", "attainment",
                "For every prime p at least thirteen, put S = (p-1)/2 and t = floor(p/12). If p is congruent to one modulo twelve, use 3t copies of C_9[K_S]; if it is congruent to five, use 3t+1 copies. If p is congruent to seven, use one C_5[K_S] and 3t+1 copies of C_9[K_S]. If it is congruent to eleven, use one C_4[K_S] and 3t+2 copies of C_9[K_S]. These unions have orders 9(p-1)^2/8, 9(p-1)^2/8, (p-1)(9p-7)/8 and (p-1)(9p-11)/8, respectively. Their independence numbers are p-1 and their clique sizes are at most p-1. In a hypothetical regular selection on p vertices, write q for one more than its degree. The component spectra exclude q = 1 and q = p. Every selected order in a nine-cycle component is divisible by q. A packet selection in the exceptional component would make q divide the prime p. A full-support selection there forces q = 3 and makes p congruent to the exceptional cycle length modulo three, contrary to the chosen residue. Thus no regular induced subgraph has order p, including disconnected selections.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
