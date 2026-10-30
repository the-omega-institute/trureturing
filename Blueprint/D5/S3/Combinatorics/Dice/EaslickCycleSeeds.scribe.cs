using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Dice;

internal sealed class EaslickCycleSeedsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Dice/EaslickCycleSeeds.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/easlick2026minimaldice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit simple cycles provide small seeds for uniform nested padding.",
        H("Finite cycle seeds"),
        Blocks(
            Node("easlick-source-seed", "The six seed lists", "sourceSeed",
                "The function sourceSeed assigns the explicit sorted-die cycles at six, seven, eight, nine, ten and eleven faces; it is empty at all other natural arguments. The corresponding lengths are 6,14,29,10,110,14. The lists omit the repeated closure row. The seven- through ten-face lists are the source lists in Appendices G through J, and the eleven-face list is obtained from the seven-face list by shifting each seed label by two and adding two low and two high faces in alternating nested intervals.", DescribeRole.Definition),
            Node("easlick-finite-cycle-witnesses", "The verified finite cycle lengths", "finite_cycle_witnesses",
                "There is a simple minimum-advantage cycle of length six for six-face dice, length fourteen for seven-face dice, length twenty-nine for eight-face dice, length ten for nine-face dice, length one hundred ten for ten-face dice, and length fourteen for eleven-face dice. Every die is sorted with valid labels, all vertices in each cycle are distinct, and every edge including the closing edge has the true minimum probability above one half. These assertions supply finite seeds and do not assert the unbounded parameter statement or the global upper bound at six.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
