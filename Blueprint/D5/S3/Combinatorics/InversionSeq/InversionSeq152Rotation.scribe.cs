using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152RotationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Rotation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct-entry words avoiding 201 and 210 have a unique decomposition into rotated increasing blocks.",
        H("Rotation Blocks for 201 and 210 Avoidance"),
        Blocks(
            Node("inversionseq-inversionseq152rotation-minimum-rotation-split", "Splitting at the minimum", "minimum_rotation_split",
                "Let a word have pairwise distinct entries and be written as a prefix, its minimum entry, and a suffix. It avoids 201 and 210 if and only if the prefix is strictly increasing, every prefix entry is less than every suffix entry and the suffix avoids 201 and 210.", DescribeRole.Theorem),
            Node("inversionseq-inversionseq152rotation-rotation-blocks-unique", "Unique rotated-block decomposition", "rotation_blocks_unique",
                "A word with pairwise distinct entries avoids 201 and 210 if and only if there is a unique list of nonempty blocks whose concatenation is strictly increasing and such that rotating each block by moving its first entry to the end and concatenating the rotated blocks gives the word. The empty word corresponds to the empty list of blocks.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
