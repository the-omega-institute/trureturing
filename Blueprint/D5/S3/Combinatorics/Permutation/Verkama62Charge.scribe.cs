using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class Verkama62ChargeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/Verkama62Charge.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/verkama2026connectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integer potential for avoiding ear runs.",
        H("An integer potential for avoiding ear runs"),
        Blocks(
            Node("verkama62-charge-earrun", "Northeast ear runs", "EarRun",
                "A run starts with three decreasing points or four points of relative order 3412. Each step inserts a singleton outside the old set with at least two old neighbours, or a northeast double ear. This definition specifies a class of runs; it does not assert that a graph has such a run.", DescribeRole.Definition),
            Node("verkama62-charge-potential", "Signed potential", "potential",
                "The integer potential is 7 times the cardinality of S minus 4 times its inversion count. A singleton of old degree d changes it by 7 - 4d, and a double ear increases it by two. All subtraction takes place in the integers.", DescribeRole.Definition),
            Node("verkama62-charge-ear-run-bound", "The bound for every avoiding run", "ear_run_bound",
                "For every n, permutation pi of Fin n and finite set S, an ear run ending at S and classical 351624-avoidance imply 7|S| <= 4 inv(S) + 12. The induction maintains three alternatives: potential at most 10; potential at most 11 with a terminal pattern; or potential at most 12 with a fresh pattern. A triangle starts at potential 9, and a square starts fresh at potential 12. Terminal states exclude the next double ear; a degree-two singleton lowers the potential by one and preserves a terminal pattern from a fresh state. A higher-degree singleton lowers it by at least five.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
