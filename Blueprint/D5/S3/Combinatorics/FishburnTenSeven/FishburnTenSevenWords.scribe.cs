using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenSeven;

internal sealed class FishburnTenSevenWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two languages over three letters encode block restrictions and are related by reversal and interchange.",
        H("FishburnTenSevenWords"),
        Blocks(
            Node("fishburntensevenwords-letter-definition", "Three allocation letters", "Letter",
                "The alphabet consists of the three letters d, i and j.", DescribeRole.Definition),
            Node("fishburntensevenwords-before-definition", "Order between occurrences of two letters", "Before",
                "For letters earlier and later, the order condition requires that no occurrence of later precede an occurrence of earlier at a strictly larger position in the word.", DescribeRole.Definition),
            Node("fishburntensevenwords-languagea-definition", "The first word language", "languageA",
                "Language A of size consists of words of that length over d, i and j having no adjacent j followed by i and no d before a later j.", DescribeRole.Definition),
            Node("fishburntensevenwords-languagec-definition", "The third word language", "languageC",
                "Language C of size consists of words of that length over d, i and j having no adjacent j followed by i and no i before a later d.", DescribeRole.Definition),
            Node("fishburntensevenwords-swap-definition", "Interchanging two letters", "swap",
                "The interchange fixes d and exchanges i and j.", DescribeRole.Definition),
            Node("fishburntensevenwords-phi-definition", "Reversal and interchange", "phi",
                "The word transformation interchanges i and j at every position, fixes d, and reverses the resulting word.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
