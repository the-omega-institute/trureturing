using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152BoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Bounds.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Position bounds on rotated blocks separate into bounds on the sorted word and on each block tail.",
        H("Position Bounds for Rotated Blocks"),
        Blocks(
            Node("inversionseq-inversionseq152bounds-rotated-suffix-bounds-iff", "Bounds before and after rotation", "rotated_suffix_bounds_iff",
                "Let a list of nonempty blocks have strictly increasing concatenation, and let b be nonnegative. Rotate each block by moving its first entry to the end. Every entry of the resulting concatenation is at most b plus its position if and only if every entry of the original concatenation satisfies that bound and every entry at position j in a block tail is at most b plus the total length of preceding blocks plus j. All positions are numbered from zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
