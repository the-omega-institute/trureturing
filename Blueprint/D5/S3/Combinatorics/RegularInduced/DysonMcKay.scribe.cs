using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RegularInduced;

internal sealed class DysonMcKayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RegularInduced/DysonMcKay.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/dyson2026regularinduced");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cycle-clique unions of Dyson and McKay attain the largest possible order without a regular induced subgraph of prime order p for every prime p at least thirteen.",
        H("Dyson and McKay's cycle-clique optimality"),
        Blocks(
            Node("dyson-mckay-result", "The exact optimum for every prime at least thirteen", "result", "For every prime p at least thirteen, every finite disjoint union of lexicographic products C_r[K_s], with cycle lengths r at least three and clique sizes s at least one, that has no regular induced subgraph on exactly p vertices has at most 9(p-1)^2/8 vertices when p is congruent to one or five modulo twelve, at most (p-1)(9p-7)/8 when p is congruent to seven, and at most (p-1)(9p-11)/8 when p is congruent to eleven. For every such prime, the explicit unions of Theorem 4.2 attain this bound. This establishes the optimality assertion following Theorem 4.2 in Section 4 of Dyson and McKay's paper. The exact component spectra describe clique packets and period-three full-support selections at one common degree. The explicit constructions avoid all regular p-selections, and independence budgets, clique bounds and triangle reserves give the matching upper bound. Products C_3[K_s] and disconnected regular selections are included.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
