using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceAscendingOutsideDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingOutside.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nonextreme ascending endpoint case forces separated decreasing blocks around an increasing middle pair.",
        H("RotationAvoidanceAscendingOutside"),
        Blocks(
            Node("rotationavoidanceascendingoutside-ascendingnonextremenormalform", "Ascending nonextreme endpoint normal form", "ascending_nonextreme_normal_form", "Let a permutation begin with first, end with last, and have an interior list. If its first entry is positive, first is less than last, at least one endpoint lies away from the extreme values, and exactly the uncut rotation contains 1234, then first plus two is less than last. The interior is a decreasing block of values below first, followed by a decreasing block of values above last, with the remaining values split into decreasing lists before and after those blocks. Some value in the first remaining list is smaller than some value in the second.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

