using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RegularInduced;

internal sealed class DysonMcKayDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RegularInduced/DysonMcKayDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/dyson2026regularinduced");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cycle-clique unions and their prime-order regular induced subgraphs define the extremal problem of Dyson and McKay.",
        H("Cycle-clique unions and the prime optimum"),
        Blocks(
            Node("dyson-mckay-vertices", "Vertices indexed by components and bags", "Vert",
                "For a finite list of pairs (r,s), a vertex consists of a component index, a cycle position from zero through r-1, and a clique position from zero through s-1. Thus the component with parameters (r,s) has rs vertices.", DescribeRole.Definition),
            Node("dyson-mckay-cycle-close", "Equal or adjacent cycle positions", "CycleClose",
                "Two positions a and b are close on the cycle of length r when a = b, when a+1 is congruent to b modulo r, or when b+1 is congruent to a modulo r.", DescribeRole.Definition),
            Node("dyson-mckay-union-graph", "The union of cycle-clique products", "unionGraph",
                "For each component (r,s), replace every vertex of C_r by a clique K_s and join all vertices in consecutive bags. Distinct vertices are adjacent precisely when they belong to the same component and their cycle positions are equal or adjacent. Different components have no edges between them. In particular, C_3[K_s] is K_{3s}.", DescribeRole.Definition),
            Node("dyson-mckay-has-regular-induced", "A regular induced subgraph of prescribed order", "HasRegularInduced",
                "A union has a regular induced subgraph of order p when there is a vertex set of cardinality p and a nonnegative integer d such that every selected vertex has exactly d neighbours among the selected vertices. The selected subgraph may be disconnected, and degree zero is permitted.", DescribeRole.Definition),
            Node("dyson-mckay-admissible", "The component parameter range", "Admissible",
                "Every component has cycle length r at least three and clique size s at least one. A finite list satisfying these inequalities specifies the class of disjoint unions of products C_r[K_s]. The empty list is included.", DescribeRole.Definition),
            Node("dyson-mckay-order", "The total number of vertices", "order",
                "The order of a union is the sum of rs over all component pairs (r,s), counting repeated pairs with their multiplicities.", DescribeRole.Definition),
            Node("dyson-mckay-bound", "The order of the prime constructions", "bound",
                "The extremal order is 9(p-1)^2/8 when p is congruent to one or five modulo twelve, (p-1)(9p-7)/8 when p is congruent to seven modulo twelve, and (p-1)(9p-11)/8 otherwise. Division is integer division. For primes p at least thirteen, the remaining residue is eleven and every displayed quotient is an integer.", DescribeRole.Definition),
            Node("dyson-mckay-claim", "The prime optimality assertion", "claim",
                "For every prime p at least thirteen, every finite union of products C_r[K_s] with r at least three and s at least one that has no regular induced subgraph on exactly p vertices has order at most the stated bound. For each such p, a union in this class has exactly that order and still has no regular induced subgraph on p vertices.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
