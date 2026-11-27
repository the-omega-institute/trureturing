using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CollisionEarliestDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/CollisionEarliest.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/mazhang2026edgecollision");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The earliest full-coverage edge collision is counted by n!: T(n,n+1)=n!.",
        H("The earliest full-coverage edge collision"),
        Blocks(
            Describe.Lean(DescribeId.Create("collision-earliest-count"),
                DeclarationHandle.Create(Prefix + "earliest_count"),
                H("T(n, n+1) = n!"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural n and start v in Fin(n), collisionCount n v (n+1)=n!. "
                    + "A counted walk has n+2 vertices x(0),…,x(n+1) with x(0)=v. Its last edge "
                    + "repeats the edge at some i<n, so x(n)=x(i) and x(n+1)=x(i+1); hence the "
                    + "first n vertices already visit every vertex and form an ordering of Fin(n) "
                    + "starting at v. Conversely an ordering σ with σ(0)=v and any vertex a give "
                    + "the walk σ(0),…,σ(n−1),a,x(n+1), where x(n+1) is the successor of the "
                    + "position of a in σ (or a itself when that position is n−1); its first n "
                    + "edges have distinct tails, its last edge repeats the edge leaving the "
                    + "first visit to a, and it visits every vertex. The two constructions are "
                    + "inverse, and orderings with a fixed first value correspond to "
                    + "permutations of Fin(n−1) through Equiv.Perm.decomposeFin, giving "
                    + "(n−1)!·n=n!."))),
                DescribeRole.Theorem))));
}
