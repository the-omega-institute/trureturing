using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152LeftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Left.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Avoidance of 010, 100, 102 and 210 is characterized by the structure at the first descent.",
        H("Structure of the Left Avoidance Class"),
        Blocks(
            Node("inversionseq-inversionseq152left-low-value-unique", "Uniqueness after a larger entry", "low_value_unique",
                "In a word avoiding 010 and 100, any entry preceded by a strictly larger entry occurs at exactly one position in the entire word.", DescribeRole.Theorem),
            Node("inversionseq-inversionseq152left-descent-global-maximum", "A descent begins at the global maximum", "descent_global_maximum",
                "In a word avoiding 102 and 210, the first entry of every adjacent descent is at least every entry of the word.", DescribeRole.Theorem),
            Node("inversionseq-inversionseq152left-first-descent-structure", "Characterization at the first descent", "first_descent_structure",
                "Suppose a word is weakly increasing through position d and then descends at position d + 1. It avoids 010, 100, 102 and 210 if and only if four conditions hold: the entry M at position d is a global maximum; every later entry less than M differs from every prefix entry; the later entries less than M are strictly increasing in their order of occurrence; and whenever a prefix entry lies strictly between the entry at position d + 1 and M, every later entry is less than that prefix entry. The prefix includes position d and the later positions are those greater than d.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
