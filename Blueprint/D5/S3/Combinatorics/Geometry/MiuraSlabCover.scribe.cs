using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraSlabCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraSlabCover.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every occupied row extends to a maximal occupied interval.", H("Actual slab coverage"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraslabcover-existence"),
                DeclarationHandle.Create(Prefix + "occupied_row_has_slab"), H("An occupied row extends to an actual slab"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every actual integer array and every occupied row, there exists a maximal consecutive occupied interval containing that row. Choose a longest fully occupied interval containing it; an occupied immediately adjacent row would extend that interval and contradict maximality. No unit-edge assumption is needed for this finite interval fact."))), DescribeRole.Theorem))));
}
