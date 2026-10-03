using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourPrimitiveBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveBlocks.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A later inversion creates a cut, restricting primitive words.",
        H("Ordering after the First Primitive Block"),
        Blocks(
            Node("nonnesting-nonnestingfourprimitiveblocks-later-inversion-cut", "A later inversion forces a cut", "later_inversion_cut",
                "If first occurrences before t are separated from later values but a larger c precedes t, an avoider has a value cut at t minus one.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingfourprimitiveblocks-primitive-later-order", "Order after an initial one or two", "primitive_later_order",
                "A primitive avoider beginning with one or two has increasing first-occurrence order among letters from two through n.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
