using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class EqualLengthTilingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/EqualLengthTiling.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-length marked tiling phases and recognizability.",
        H("Equal-length marked tiling phases and recognizability"),
        Blocks(
            Describe.Lean(DescribeId.Create("phase"), DeclarationHandle.Create(Owner + "tiled_offset_phase"),
                H("Two-sided phase"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two binary words of a common positive length L, the marked offset at every integer i is the nonnegative remainder of i plus the offset at zero modulo L. Comparing the tiling with a periodic tiling of one word propagates offset equality both forwards and backwards. Thus translation by any integer multiple of L preserves the phase, and the boundary set is one residue class."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("recognizability"), DeclarationHandle.Create(Owner + "equal_length_tiling_eq_of_read_boundaries"),
                H("Identification from symbols and boundaries"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose the two words have equal lengths and are distinct as words. Two actual marked tilings with identical visible sequences and identical boundary sets are equal. Boundaries first identify every offset. Starting at the common preceding boundary, forward traversal reads every letter of the corresponding words; equality of those words identifies their types. Distinct word lengths are not required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-column"), DeclarationHandle.Create(Owner + "tiled_common_column_periodic"),
                H("Periodic common columns"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the two words agree at the marked offset of a coordinate, its visible symbol is unchanged by every integer multiple of their common length. This holds for arbitrary origin phase. For a tiling with a boundary at zero, each residue at which the words agree therefore gives a fixed symbol throughout that residue class. The conclusion covers negative coordinates and negative multiples as well."))), DescribeRole.Theorem))));
}
