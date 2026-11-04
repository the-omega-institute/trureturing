using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class MarkedTilingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/MarkedTiling.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact spaces of marked block tilings.",
        H("Compact spaces of marked block tilings"),
        Blocks(
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "MarkedTiling"),
                H("Construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A marked state records the actual binary block type and its physical offset. Adjacent states either advance inside the same block or cross from its last letter to the start of a new block. The closed space of such integer-indexed states is compact. Reading letters gives the entire compact tiling subshift. If the two block lengths differ, equality of all boundary positions determines the marked tiling."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coordinate-read"), DeclarationHandle.Create(Owner + "readTile_of_coordinates"),
                H("Reading a specified coordinate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When a marked state's type is a and its physical offset is p, reading that state gives the p-th letter of W(a). The same declaration serves the finite-window proofs and the equal-length tiling proofs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("main-result"), DeclarationHandle.Create(Owner + "tiled_eq_of_boundaries"),
                H("Result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A marked state records the actual binary block type and its physical offset. Adjacent states either advance inside the same block or cross from its last letter to the start of a new block. The closed space of such integer-indexed states is compact. Reading letters gives the entire compact tiling subshift. If the two block lengths differ, equality of all boundary positions determines the marked tiling."))), DescribeRole.Theorem))));
}
