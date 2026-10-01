using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152LabelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Labels.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subtracting positional ranks converts bounded rotated blocks into weakly increasing label blocks.",
        H("A Bijection with Bounded Sorted Labels"),
        Blocks(
            Node("inversionseq-inversionseq152labels-sorted-label-bijection", "Sorted labels for rotated blocks", "sorted_label_bijection",
                "Fix nonnegative integers n, l and u. Lists of nonempty blocks with total length n, strictly increasing concatenation, entries greater than l and rotated-concatenation entries at most u + 1 plus their positions are in bijection with lists of nonempty label blocks of total length n whose concatenation is weakly increasing, whose labels lie between l and u inclusive and whose block-tail labels are strictly less than u. Rotation moves each block's first entry to its end, and positions are numbered from zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
