using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class Verkama62PersistenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/Verkama62Persistence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/verkama2026connectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A singleton between double ears.",
        H("A singleton between double ears"),
        Blocks(
            Node("verkama62-persistence-neighbours", "Old inversion neighbours", "neighbours",
                "For a new position x, the old neighbours are precisely the i in S with i < x and pi(x) < pi(i), or x < i and pi(i) < pi(x).", DescribeRole.Definition),
            Node("verkama62-persistence-fresh-singleton-terminal", "Persistence through one degree-two singleton", "singleton_terminal",
                "For every finite permutation and fresh state S, inserting a position x outside S with exactly two old inversion neighbours leaves a terminal 3412. If x becomes the new maximum, it lies between b and c. If it becomes rightmost, its value lies between pi(d) and pi(a). If it changes neither extremum, the original terminal pattern remains.", DescribeRole.Theorem),
            Node("verkama62-persistence-fresh-no-cheap-double", "Cheap transitions cannot precede a double ear", "no_cheap_double",
                "In a 351624-avoiding permutation, a fresh state admits no northeast double ear. The same holds after inserting exactly one singleton having two old neighbours. No assertion of persistence through arbitrary longer sequences is needed.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
