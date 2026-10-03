using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DottedStack;

internal sealed class ShiehYangYuTwelveDotFibreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotFibre.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/yangshiehyu2025dotted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Preimages of peak-run reversal correspond to ordered block decompositions, and record values specify possible cuts.",
        H("Fibres of Peak-Run Reversal"),
        Blocks(
            Node("syy-twelve-dot-fibre-equivalence-definition", "A block description of each fibre", "fibre_equiv",
                "For every output word, fibre_equiv is a bijection between inputs whose s12 "
                + "image is that output and lists of blocks concatenating to the output with "
                + "the following properties. Each reversed block is nonempty, and every entry "
                + "after its leader is at most that leader. For any two reversed blocks in "
                + "their original order, every entry of the earlier block is strictly smaller "
                + "than the leader of the later block. The forward map reverses each peak run "
                + "of the input. The inverse reverses each output block and concatenates them.",
                DescribeRole.Definition),
            Node("syy-twelve-dot-record-cuts-definition", "Record values", "recordCuts",
                "For every word of natural numbers, recordCuts is the finite set of values "
                + "in the word whose first occurrence is strictly larger than every preceding "
                + "entry. The first entry has no preceding entries and is therefore a record. "
                + "The set consists of values, rather than their positions; for permutations "
                + "these values correspond uniquely to the left-to-right maximum positions.",
                DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
