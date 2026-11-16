using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class Verkama62LocalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/Verkama62Local.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/verkama2026connectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Northeast ears and terminal patterns.",
        H("Northeast ears and terminal patterns"),
        Blocks(
            Node("verkama62-local-pattern", "The classical forbidden pattern", "pattern",
                "The permutation of six zero-based values is [2, 4, 0, 5, 1, 3], corresponding to the classical one-based pattern 351624.", DescribeRole.Definition),
            Node("verkama62-local-terminal", "Terminal 3412", "Terminal",
                "For a permutation pi of Fin n and a finite set S of positions, a terminal pattern consists of a < b < c < d in S with pi(c) < pi(d) < pi(a) < pi(b). Every position of S is at most d and every value in S is at most pi(b).", DescribeRole.Definition),
            Node("verkama62-local-fresh", "Fresh terminal patterns", "Fresh",
                "A fresh terminal 3412 has the additional properties that every old position is at most b or equals c or d, and every old value is at most pi(d) or occurs at a or b. Thus b,c,d are the last three positions and pi(d),pi(a),pi(b) are the largest three values.", DescribeRole.Definition),
            Node("verkama62-local-double", "Northeast double ears", "Double",
                "Two new positions u,v and distinct old attachments x,y satisfy u < x < v and pi(v) < pi(y) < pi(u). Every old point except x lies left of u; every old value except pi(y) lies below pi(v). Neither new position belongs to S.", DescribeRole.Definition),
            Node("verkama62-local-double-fresh", "The fresh state after a double ear", "fresh",
                "After a northeast double ear, the points y,u,x,v form a fresh terminal 3412 in S union {u,v}.", DescribeRole.Definition),
            Node("verkama62-local-terminal-forces", "The forbidden six-point configuration", "forces",
                "If a terminal 3412 occurs in S and a northeast double ear can be added, the whole permutation contains 351624. The six selected positions are a,b,c,u,d,v. Their values increase in the order c,d,a,v,b,u. The terminal maximum and rightmost point are exactly the two old attachment points.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
