using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152CutsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Cuts.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Allowed joins between successive labels give independent binary choices for dividing a word into blocks.",
        H("Independent Choices of Block Boundaries"),
        Blocks(
            Node("inversionseq-inversionseq152cuts-independent-join-bijection", "Enumeration of allowed block divisions", "independent_join_bijection",
                "Fix a word of nonnegative labels and a nonnegative upper bound u. Divisions into nonempty consecutive blocks whose concatenation is the word and whose tail entries are all less than u are in bijection with the integers from zero through 2 to the power k minus one, where k is the number of entries less than u after the first position. The empty word has one division, consisting of no blocks.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
