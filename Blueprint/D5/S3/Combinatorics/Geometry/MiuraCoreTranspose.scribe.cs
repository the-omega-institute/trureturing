using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraCoreTransposeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraCoreTranspose.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact residual transport under axis exchange.", H("Exact residual transport under axis exchange"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuracoretranspose-1"),
                DeclarationHandle.Create(Prefix + "transpose_extremum_cards"), H("Each extremum sign is counted separately"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coordinate swap bijects strict minima with strict minima and strict maxima with strict maxima, using every existing neighbour in both grids."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoretranspose-2"),
                DeclarationHandle.Create(Prefix + "transposeSide"), H("Physical sides follow the axes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Top and bottom exchange with left and right under transposition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuracoretranspose-3"),
                DeclarationHandle.Create(Prefix + "transpose_all_minima_side_iff"), H("The common side is transported exactly"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each specified physical side of the transposed rectangle, all minima lie on that side exactly when all original minima lie on its exchanged side."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuracoretranspose-4"),
                DeclarationHandle.Create(Prefix + "transpose_residual"), H("The original residual predicate is preserved"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transposition preserves the unit-edge law, origin normalization, the exact minimum and maximum counts separately, and failure of containment of all minima in any single physical side."))), DescribeRole.Theorem))));
}
